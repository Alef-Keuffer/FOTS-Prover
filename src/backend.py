from typing import Container, Callable

from pysmt.fnode import FNode
from pysmt.shortcuts import Symbol, Not, And, Or, EqualsOrIff, Implies, Portfolio, binary_interpolant, BVToNatural, \
    get_model, is_valid, FALSE, get_env
from pysmt.shortcuts import is_sat, is_unsat, Solver, TRUE
from pprint import pprint

from pysmt.solvers.msat import MSatInterpolator


def next_var(v):
    """Returns the 'next' of the given variable"""
    return Symbol("next(%s)" % v.symbol_name(), v.symbol_type())


def at_time(v, t):
    """Builds an SMT variable representing v at time t"""
    return Symbol("%s@%d" % (v.symbol_name(), t), v.symbol_type())


def get_subs(P: FNode | Container[FNode], i: int):
    """
    Builds a map from :math:`x` to :math:`x_i` and from :math:`x'` to :math:`x_{i+1}`,
    for all :math:`x` in :math:`P`.
    """
    if isinstance(P, FNode):
        P = P.get_free_variables()
    subs_i = {}
    for v in P:
        subs_i[v] = at_time(v, i)
        subs_i[next_var(v)] = at_time(v, i + 1)
    return subs_i


def get_unrolling(P: FNode, k, j=0):
    """Unrolling of the property from :math:`j` to :math:`k`:

    E.g. :math:`P^j ∧ P^{j+1} ∧ ⋯ ∧ P^{k-1} ∧ P^k`
    """
    assert j <= k
    res = []
    for i in range(j, k + 1):
        subs_i = get_subs(P, i)
        res.append(P.substitute(subs_i))
    return And(res)


class TransitionSystem(object):
    """Trivial representation of a FOTS (First Order Transition System)."""

    def __init__(self, init: FNode, trans: FNode):
        self.variables: list[FNode] = list(set(init.get_free_variables()).union((trans.get_free_variables())))
        self.init = init
        self.trans = trans

    def get_subs(self, i):
        """See :func:`get_subs`"""
        return get_subs(self.variables, i)

    def get_unrolling(self, k, j=0):
        """See :func:`get_unrolling`"""
        return get_unrolling(self.trans, k, j)


class BMCInduction(object):
    def __init__(self, system):
        self.system = system

    def get_simple_path(self, k):
        """Simple path constraint for k-induction:
        each time encodes a different state
        """
        res = []
        for i in range(k + 1):
            subs_i = self.system.get_subs(i)
            for j in range(i + 1, k + 1):
                state = []
                subs_j = self.system.get_subs(j)
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
            subs_i = self.system.get_subs(i)
            res.append(prop.substitute(subs_i))
        return And(res)

    def get_bmc(self, prop, k):
        """Returns the BMC encoding at step k"""
        init_0 = self.system.init.substitute(self.system.get_subs(0))
        prop_k = prop.substitute(self.system.get_subs(k))
        return And(self.system.get_unrolling(k), init_0, Not(prop_k))

    def get_k_induction(self, prop, k):
        """Returns the K-Induction encoding at step K"""
        subs_k = self.system.get_subs(k)
        prop_k = prop.substitute(subs_k)
        return And(self.system.get_unrolling(k),
                   self.get_k_hypothesis(prop, k),
                   self.get_simple_path(k),
                   Not(prop_k))

    def check_property(self, prop):
        """Interleaves BMC and K-Ind to verify the property."""
        print("Checking property %s..." % prop)
        from ply.cpp import xrange
        for b in xrange(100):
            f = self.get_bmc(prop, b)
            print("   [BMC]    Checking bound %d..." % (b + 1))
            if is_sat(f):
                print("--> Bug found at step %d" % (b + 1))
                return

            f = self.get_k_induction(prop, b)
            print("   [K-IND]  Checking bound %d..." % (b + 1))
            if is_unsat(f):
                print("--> The system is safe!")
                return


from enum import unique, Enum, auto


class Status(Enum):
    UNSAFE = auto()
    SAFE = auto()
    UNSAFE1 = auto()
    UNSAFE2 = auto()
    SAT = auto()
    UNSAT = auto()
    UNKNOWN = auto()


def itp(formulas):
    class CustomMSatInterpolator(MSatInterpolator):
        def sequence_interpolant(self, formulas):
            cfg, env = None, None
            try:
                self._check_logic(formulas)

                if len(formulas) < 2:
                    from pysmt.exceptions import PysmtValueError
                    raise PysmtValueError("interpolation needs at least 2 formulae")

                import mathsat
                cfg = mathsat.msat_create_config()
                mathsat.msat_set_option(cfg, "interpolation", "true")
                from pysmt.logics import QF_BV
                from pysmt.logics import QF_AUFBVLIRA
                if self.logic in {QF_BV, QF_AUFBVLIRA}:
                    mathsat.msat_set_option(cfg, "theory.bv.eager", "false")
                    mathsat.msat_set_option(cfg, "theory.eq_propagaion", "false")
                env = mathsat.msat_create_env(cfg, self.msat_env())
                groups = []
                for f in formulas:
                    f = self.converter.convert(f)
                    g = mathsat.msat_create_itp_group(env)
                    mathsat.msat_set_itp_group(env, g)
                    groups.append(g)
                    mathsat.msat_assert_formula(env, f)

                res = mathsat.msat_solve(env)
                if res == mathsat.MSAT_UNKNOWN:
                    from pysmt.exceptions import InternalSolverError
                    raise InternalSolverError("Error in mathsat interpolation: %s" %
                                              mathsat.msat_last_error_message(env))

                if res == mathsat.MSAT_SAT:
                    return None

                pysmt_ret = []
                for i in range(1, len(groups)):
                    itp = mathsat.msat_get_interpolant(env, groups[:i])
                    f = self.converter.back(itp)
                    pysmt_ret.append(f)

                return pysmt_ret
            finally:
                if cfg:
                    mathsat.msat_destroy_config(cfg)
                if env:
                    mathsat.msat_destroy_env(env)

    from pysmt.oracles import get_logic
    return CustomMSatInterpolator(get_env(), logic=get_logic(And(formulas))).sequence_interpolant(formulas)


def bin_itp(a, b):
    return itp([a, b])


def interpolate(A: FNode, B: FNode):
    with Solver() as sA, Solver() as sB:
        sA.add_assertion(A)
        sB.add_assertion(B)
        I = TRUE()
        while True:
            if not sB.solve():
                return Status.UNSAT, I
            if sA.is_sat():
                mA = sA.get_model()
                if mA.satisfies(B):
                    return Status.SAT, sA.get_model(), TRUE()
            else:
                pass


class IMC:
    """Interpolating Model Checking"""

    def __init__(self, system: TransitionSystem):
        self.system = system

    def check_property(self, P: FNode, S=None, customInterpolator=False):
        # based on Algorithm 4 from http://verify.inf.usi.ch/sites/default/files/RolliniPhDThesis.pdf
        if not S:
            S = self.system.init
        if m := get_model(S & Not(P)):
            print(m)
            return Status.UNSAFE1
        k = 1
        i = 0
        R_i = S.substitute(self.system.get_subs(i))
        while True:
            A = R_i & self.system.get_unrolling(1)
            B = And(And(self.system.get_unrolling(1, k)), Or(get_unrolling(Not(P), k)))
            if m := is_sat(A & B):
                if is_valid(R_i.EqualsOrIff(S)):
                    print(m)
                    return Status.UNSAFE2
                else:
                    k += 1
                    i = 0
                    R_i = S.substitute(self.system.get_subs(i))
            else:
                if customInterpolator:
                    I_i = bin_itp(A, B)
                else:
                    I_i = binary_interpolant(A, B)
                if is_valid(I_i.Implies(R_i)):
                    print(f"Proved at step {i + 1}")
                    return Status.SAFE
                else:
                    R_i = R_i | I_i
                    i += 1


def get_or_and(T, P, k):
    """
    :return: :math:`\\displaystyle\\bigvee_{n=0}^k \\left(\\displaystyle\\bigwedge_{i=0}^n T(s_i,s_{i+1}) ∧ P(s_n)\\right)`
    """
    OR_formulas = TRUE()
    for n in range(k + 1):
        OR_formulas |= (get_unrolling(T, 0, n - 1) & get_unrolling(P, n, n))
    return OR_formulas


def _lift(k, Inv, Q, s):
    """
    We can implement lift using Craig interpolation
    between
    A: s = s_n and
    B: Inv (sn) ⋀_{i=n}^{n+k-1}( Q(s_i) ∧ T(s_i, s_{i+1}) ) ⇒ ¬Q(sn+k)
    because s is a CTI, and therefore we know that A ⇒ B holds.
    Hence, the resulting interpolant satisfies the criteria for C to
    be a valid lifting of s according to the requirements towards the function lift.
    """
    A = s == ...
    B = ...
    return binary_interpolant(A, B)


def pdr(P: FNode,
        TS: TransitionSystem,
        get_currently_known_invariant=...,
        strengthen=...,
        lift=...,
        k_init: int = 1,
        k_max: int = float('inf'),
        pd: bool = True,
        inc: Callable[[int], int] = lambda n: n + 1,
        ) -> bool | Status:
    """
    Iterative-Deepening k-Induction with Property Direction
    as specified at D. Beyer and M. Dangl, “Software Verification with PDR: Implementation and Empirical Evaluation of the State of the Art,” arXiv:1908.06271 [cs], Feb. 2020, Accessed: Mar. 05, 2022. [Online]. Available: http://arxiv.org/abs/1908.06271

    :param k_init: the initial value :math:`≥1` for the bound `k`
    :param k_max: an upper limit for the bound `k`
    :param inc: a function :math:`ℕ → ℕ` such that :math:`∀n ∈ ℕ: inc(n) > n`
    :param TS: Contains predicates defining the initial states and the transfer relation
    :param P: The safety property
    :param get_currently_known_invariant: used to obtain the strongest invariant currently
        available via a concurrently running (external) auxiliary-invariant generator
    :param pd: boolean flag pd (reminding of “property-directed”) is used to control
        whether failed induction checks are used to guide the algorithm towards
        a sufficient strengthening of the safety property P to prove correctness;
        if pd is set to false, the algorithm behaves exactly like standard k-induction.
    :param lift: Given a failed attempt to prove some candidate invariant :math:`Q` by induction,
        the function lift is used to obtain from a concrete counterexample-to-induction (CTI)
        state a set of CTI states described by a state predicate C. An implementation of the function
        :math:`k ∈ ℕ, \\Inv ∈ ℕ × (S → 𝔹) × (S → 𝔹) × S → (S → 𝔹)` and :math:`C = \\lift(k, \\Inv , Q, s)`,
        lift needs to satisfy the condition that for a CTI :math:`s ∈ S` where :math:`S` is the set of
        program states, the following holds:

        .. math:: C(s) ∧ \\left( ∀s_n ∈ S: C(s_n) ⇒ \\Inv(s_n) ∧ ⋀_{i=n}^{n+k−1} (Q(s_i) ∧ T(s_i ,s_{i+1})) ⇒ ¬Q(s_{n+k}) \\right)

        which means that the CTI s must be an element of the set of states described by the resulting predicate
        C and that all states in this set must be CTIs, i.e., they need to be k-predecessors of :math:`¬Q`-states,
        or in other words, each state in the set of states described by the predicate :math:`C` must reach some
        :math:`¬Q`-state via :math:`k` unrollings of the transition relation :math:`T`.
    :param strengthen: The function strengthen: :math:`ℕ × (S → 𝔹) × (S → 𝔹) → (S → 𝔹)`
        is used to obtain for a k-inductive invariant a stronger k-inductive invariant, i.e.,
        its result needs to imply the input invariant, and, just like the input invariant,
        it must not be violated within k loop iterations and must be k-inductive.
    :return: `True` if `P` holds, `Status.UNKNOWN` if `k > k_max` , `False` otherwise
    """

    # current bound
    k = k_init

    # the invariant computed by this algorithm internally
    InternalInv = True

    # the set of current proof obligations.
    O = set()

    while k <= k_max:
        O_prev = O
        O = set()

        # begin: base-case check (BMC)
        #
        # Base Case. The base case of k -induction consists of running BMC with the
        # current bound k. 4 This means that starting from all initial program states, all
        # states of the program reachable within at most k −1 unwindings of the transition
        # relation are explored. If a ¬P -state is found, the algorithm terminates.
        base_case = get_unrolling(TS.init, 0, 0) & get_or_and(TS.trans, Not(P), k - 1)
        if is_sat(base_case):
            return False
        # end ################################################################

        # begin: forward-condition check (as described in Sec. 2)
        #
        # Forward Condition. If no ¬P-state is found by the BMC in the base case, the
        # algorithm continues by performing the forward-condition check, which attempts
        # to prove that BMC fully explored the state space of the program by checking
        # that no state with distance k′ > k−1 to the initial state is reachable. If this
        # check is successful, the algorithm terminates.
        forward_condition = get_unrolling(TS.init, 0, 0) & TS.get_unrolling(0, k - 1)
        if not is_unsat(forward_condition):
            return True
        # end ################################################################

        # begin: attempt to prove each proof obligation using k-induction
        if pd:
            for o in O_prev:
                # begin: check the base case for a proof obligation o
                base_case_o = get_unrolling(TS.init, 0, 0) & get_or_and(TS.trans, Not(o), k - 1)
                if is_sat(base_case_o):
                    # If any violations of the proof obligation o are found,
                    # this means that a predecessor state of a ¬P-state,
                    # and thus, transitively, a ¬P -state, is reachable, so we return false.
                    return False
                # end ################################################################

                else:
                    # no violation was found

                    # begin: check the inductive-step case to prove o
                    #
                    # Inductive-Step Case. The forward-condition check, however, can only prove
                    # safety for programs with finite (and, in practice, short) loops. To prove safety
                    # beyond the bound k, the algorithm applies induction: The inductive-step case
                    # attempts to prove that after every sequence of k unrollings of the transition
                    # relation that did not reach a ¬P-state, there can also be no subsequent transition
                    # into a ¬P-state by unwinding the transition relation once more. In the realm
                    # of model checking of software, however, the safety property P is often not
                    # directly k-inductive for any value of k, thus causing the inductive-step-case check
                    # to fail. It is therefore state-of-the-art practice to add auxiliary invariants to this
                    # check to further strengthen the induction hypothesis and make it more likely
                    # to succeed. Thus, the inductive-step case proves a program safe if the following
                    # condition is unsatisfiable:
                    #
                    #           Inv(s_n) ⋀_{i=n}^{n+k-1}(P(s_i) ∧ T(s_i,s_{i+1})) ∧ ¬P(s_{n+k})
                    #
                    # where Inv is an auxiliary invariant, and sₙ,…,sₙ₊ₖ is any sequence of states. If
                    # this check fails, the induction attempt is inconclusive, and the program is neither
                    # proved safe nor unsafe yet with the current value of k and the given auxiliary
                    # invariant. In this case, the algorithm increases the value of k and starts over.
                    step_case_o_n = ...
                    ExternalInv = get_currently_known_invariant()
                    Inv = InternalInv & ExternalInv
                    if is_sat(... & step_case_o_n):
                        s_o = ...
                        O = O.union(Not(lift(k, Inv, P, s_o)))
                    else:
                        # if the step-case check for o is successful,
                        # we no longer track o in the set O of unproven proof obligations

                        # We could now directly use the proof obligation as an invariant,
                        # but instead, we first try to strengthen it into a stronger invariant
                        # that removes even more unreachable states from future consideration before
                        # conjoining it to our internally computed auxiliary invariant. In our
                        # implementation, we implement strengthen by attempting to drop components
                        # from a (disjunctive) invariant and checking if the remaining clause is
                        # still inductive.
                        InternalInv &= strengthen(k, Inv, o)
                    # end ################################################################
        # end: attempt to prove each proof obligation using k-induction

        # begin: check the inductive-step case for the safety property P
        #
        # This check is mostly analogous to the inductive-step case check for
        # the proof obligations described above, except that if the check is successful, we
        # immediately return true.
        step_case_n = ...

        ExternalInv = get_currently_known_invariant()
        Inv = InternalInv & ExternalInv
        if is_sat(... & step_case_n):
            if pd:
                s = ...
                O = O.union(Not(lift(k, Inv, P, s)))
        else:
            return True
        # end ################################################################

        k = inc(k)
    return Status.UNKNOWN


def main():
    trab4NormalInterpolator()


def trab4NormalInterpolator():
    from util.examples.trab4 import trab4EvenMoreSimplified, trab4FinalSimplification, trab4NoImplies
    example = trab4NoImplies(4)
    bmcind = BMCInduction(example[0])
    interp = IMC(example[0])
    for prop in example[1]:
        print(f"proving {prop[1]}")
        # bmcind.check_property(prop[0])
        print(interp.check_property(prop[0]))


def trab4CustomInterpolator():
    from util.examples.trab4 import trab4EvenMoreSimplified, trab4FinalSimplification, trab4NoImplies
    example = trab4NoImplies(4, pc_is_bv=False)
    bmcind = BMCInduction(example[0])
    interp = IMC(example[0])
    for prop in example[1]:
        print(f"proving {prop[1]}")
        # bmcind.check_property(prop[0])
        print(interp.check_property(prop[0], customInterpolator=True))


def interp(P: FNode, Q: FNode):
    # see Theorem 5 in https://www.cs.cmu.edu/~15414/f17/lectures/21-cegar.pdf
    if P.get_atoms().intersection(Q.get_atoms()):
        print(f"{P.get_atoms() = }")
        print(f"{Q.get_atoms() = }")
        return TRUE()
    D = P.get_atoms().difference(Q.get_atoms())
    if D == set():
        return P
    else:
        P_DT = P.substitute({d: TRUE() for d in D})
        P_DF = P.substitute({d: FALSE() for d in D})
        OR_P = P_DT | P_DF
        return interp(OR_P, Q).simplify()


def example_interpolation():
    A, B, D, E = Symbol("A"), Symbol("B"), Symbol("D"), Symbol("E"),
    P = Not(A & B).Implies(Not(D) & B)
    Q = (E.Implies(A)) & (E.Implies(Not(D)))
    return binary_interpolant(P, Not(Q)), interp(P, Q)


def example_interpolation2():
    from pysmt.typing import INT
    c, d = Symbol("c", INT), Symbol("d", INT)
    P = (c.NotEquals(0) | d.Equals(0)) & c.Equals(0)
    Q = d.Equals(0)
    return binary_interpolant(P, Not(Q))


def example_interpolation3():
    from pysmt.typing import INT
    x, y, c0, c1, m = Symbol("x", INT), Symbol("y", INT), Symbol("c0", INT), Symbol("c1", INT), Symbol("m", INT)
    P = x.Equals(c0) & c1.Equals(c0 + 1) & y.Equals(c1)
    Q = x.Equals(m) & y.Equals(m + 1)
    return binary_interpolant(P, Not(Q)), interp(P, Q)


def example_get_logic():
    from pysmt.oracles import get_logic
    from pysmt.typing import INT, BVType
    x = Symbol("x", INT)
    y = Symbol("y", BVType())
    print(get_logic(y.Equals(0) & x.Equals(0)))


def example_failed_interpolation1():
    from pysmt.oracles import get_logic
    from pysmt.typing import INT, BVType
    x = Symbol("x", INT)
    y = Symbol("y", BVType())
    binary_interpolant(y.Equals(0), x.Equals(0), logic="QF_IDL")


def example_failed_interpolation2():
    from pysmt.oracles import get_logic
    from pysmt.typing import INT, BVType
    x = Symbol("x", INT)
    y = Symbol("y", BVType())
    binary_interpolant(y.Equals(0), x.Equals(0))


def example_failed_interpolation3():
    from pysmt.oracles import get_logic
    from pysmt.typing import INT, BVType
    from pysmt.solvers.msat import MSatInterpolator
    x = Symbol("x", INT)
    y = Symbol("y", BVType(4))
    formulas = [x.Equals(0), y.Equals(0)]
    itp(And(formulas))


if __name__ == "__main__":
    main()
    # example_failed_interpolation3()
    # print(example_interpolation())
    # print(example_interpolation2())
    # print(example_interpolation3())

"""
Converting pc from INT to BVType allows the use of QF_BV.

Specifying QF_IDL on binary_interpolant causes error:
    Error in mathsat interpolation: eager bv solver does not support proof generation

Logic that has BV and INT is: QF_AUFBVLIRA

    from pysmt.oracles import get_logic
    from pysmt.typing import INT, BVType
    x = Symbol("x",INT)
    y = Symbol("y",BVType())
    print(get_logic(y.Equals(0) & x.Equals(0)))


"""
