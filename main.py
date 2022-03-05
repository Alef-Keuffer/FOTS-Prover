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
        self.variables = variables
        self.init = init
        self.trans = trans


class KInduction_FOTS(object):
    def __init__(self, fots):
        self.fotsystem = fots

    def get_subs(self, i):
        """Builds a map from x to x@i and from x' to x@(i+1), for all x in system."""
        subs_i = {}
        for v in self.fotsystem.variables:
            subs_i[v] = at_time(v, i)
            # subs_i[next_var(v)] = at_time(v, i+1)
        return subs_i

    def k_induction_always(self, inv, k, logic, solvers=["z3"]):
        trace = [self.get_subs(i) for i in range(k + 1)]
        with Portfolio(solvers,
                       logic=logic,
                       incremental=False,
                       generate_models=False) as s:
            s.reset_assertions()
            s.add_assertion(self.fotsystem.init(trace[0]))
            for i in range(k - 1):
                s.add_assertion(self.trans(trace[i], trace[i + 1]))

            l = [Not(inv(trace[i])) for i in range(k)]

            s.add_assertion(Or(l))

            r = s.solve()

            if r:
                print('A prova por k-indução falhou no caso base:')
                print('O estado do FOTS que causou a falha:')
                m = s.get_model()
                for i in range(k):
                    print(i)
                    for v in trace[i]:
                        print(v, ' = ', m[trace[i][v]])
                return

            s.reset_assertions()
            for i in range(k):
                s.add_assertion(self.trans(trace[i], trace[i + 1]))
                s.add_assertion(inv(trace[i]))
            s.add_assertion(Not(inv(trace[k])))

            r = s.solve()

            if r:
                print(f'Falhou no passo de {k}-indução!')
                m = s.get_model()
                for i in range(k):
                    print(i)
                    for v in trace[i]:
                        print(v, ' = ', m[trace[i][v]])
                return

            if not r:
                print(f'Verifica-se a propriedade {inv}')
                return
