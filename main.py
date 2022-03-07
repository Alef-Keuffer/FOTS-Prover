from pysmt.shortcuts import Symbol, Not, And, Or, EqualsOrIff, Implies, Portfolio
from pysmt.shortcuts import is_sat, is_unsat, Solver, TRUE
from pysmt.typing import BOOL

def next_var(v):
    """Returns the 'next' of the given variable"""
    return Symbol("next(%s)" % v.symbol_name(), v.symbol_type())

def at_time(v, t):
    """Builds an SMT variable representing v at time t"""
    return Symbol("%s@%d" % (v.symbol_name(), t), v.symbol_type())

class FirstOrderTransitionSystem(object):
    """Trivial representation of a FOTS (First Order Transition System)."""

    def __init__(self, variables, init, trans):
        self.prime_variables = [next(v) for v in self.variables]
        self.variables = variables
        self.init = init
        self.trans = trans

class KInduction_FOTS(object):
    def __init__(self, fots):
        self.fotsystem = fots

    def __init__(self, system):
        self.system = system

    def get_subs(self, i):
        """Builds a map from x to x@i and from x' to x@(i+1), for all x in system."""
        subs_i = {}
        for v in self.system.variables:
            subs_i[v] = at_time(v, i)
            subs_i[next_var(v)] = at_time(v, i+1)
        return subs_i

    def get_unrolling(self, k):
        """Unrolling of the transition relation from 0 to k:

        E.g. T(0,1) & T(1,2) & ... & T(k-1,k)
        """
        res = []
        for i in range(k+1):
            subs_i = self.get_subs(i)
            res.append(self.system.trans.substitute(subs_i))
        return And(res)

    def get_simple_path(self, k):
        """Simple path constraint for k-induction:
        each time encodes a different state
        """
        res = []
        for i in range(k+1):
            subs_i = self.get_subs(i)
            for j in range(i+1, k+1):
                state = []
                subs_j = self.get_subs(j)
                for v in self.system.variables:
                    v_i = v.substitute(subs_i)
                    v_j = v.substitute(subs_j)
                    state.append(Not(EqualsOrIff(v_i, v_j)))
                res.append(Or(state))
        return And(res)

    def get_k_hypothesis(self, prop, k):
        """Hypothesis for k-induction: each state up to k-1 fulfills the property"""
        res = []
        for i in range(k):
            subs_i = self.get_subs(i)
            res.append(prop.substitute(subs_i))
        return And(res)

    def get_bmc(self, prop, k):
        """Returns the BMC encoding at step k"""
        init_0 = self.system.init.substitute(self.get_subs(0))
        prop_k = prop.substitute(self.get_subs(k))
        return And(self.get_unrolling(k), init_0, Not(prop_k))

    def get_k_induction(self, prop, k):
        """Returns the K-Induction encoding at step K"""
        subs_k = self.get_subs(k)
        prop_k = prop.substitute(subs_k)
        return And(self.get_unrolling(k),
                   self.get_k_hypothesis(prop, k),
                   self.get_simple_path(k),
                   Not(prop_k))

    def k_induction_always(self, inv, k, logic, solvers=["z3"]):
        trace = [self.get_subs(i) for i in range(k + 1)]
        with Portfolio(solvers,
                       logic=logic,
                       incremental=False,
                       generate_models=False) as s:
            s.reset_assertions()
            f = self.get_k_induction(inv, k)
            print("   [K-IND]  Checking bound %d..." % (k+1))
            if is_unsat(f, portfolio=s):
                print("--> The system is safe!")
                return
