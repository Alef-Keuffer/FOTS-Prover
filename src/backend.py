import textwrap
from typing import Container, Callable
from pysmt.fnode import FNode
from pysmt.shortcuts import *
from pysmt.solvers.msat import MSatInterpolator
from enum import Enum, auto
from pprint import pprint

# General
from pysmt.solvers.solver import Model
from pysmt.typing import INT
INDENT = '  '


class Status(Enum):
    UNSAFE = auto()
    SAFE = auto()
    UNSAFE1 = auto()
    UNSAFE2 = auto()
    SAT = auto()
    UNSAT = auto()
    UNKNOWN = auto()


def next_var(v: FNode):
    """Returns the 'next' of the given variable"""
    return Symbol(f"next({v.symbol_name()})", v.symbol_type())


def at_time(v: FNode, t):
    """Builds an SMT variable representing v at time t"""
    return Symbol(f"[{t}]{v.symbol_name()}", v.symbol_type())


def is_next(v: FNode):
    s = v.symbol_name()
    # return 'next(' == s[:5] and ')' == s[-1]
    return 'next(' in s


def get_name(s: FNode):
    import re
    return re.search(r'](.*)', s.symbol_name()).group(1)


def str_model(m: Model):
    d = {}
    s = []
    i = 0
    for x, v in sorted(m, key=lambda t: t[0].symbol_name()):
        n = get_name(x)
        s.append(f"{'*' * int(x.symbol_name()[1] != '0' and d[n] != v)}{x} := {v}")
        d[n] = v

    return '\n'.join(s)
    # return '\n'.join(f"{x} := {v}" for x, v in sorted(m, key=lambda t: t[0].symbol_name()))


def get_subs(P: Container[FNode] | FNode, i: int):
    """
    Builds a map from :math:`x` to :math:`x_i` and from :math:`x'` to :math:`x_{i+1}`,
    for all :math:`x` in :math:`P`.
    """
    if isinstance(P, FNode):
        P = P.get_free_variables()
        P = {v for v in P if not is_next(v)}
    subs_i = {}
    for v in P:
        subs_i[v] = at_time(v, i)
        subs_i[next_var(v)] = at_time(v, i + 1)
    return subs_i


def get_unrolling(P: FNode, k: int, j: int = 0):
    """Unrolling of the property from :math:`j` to :math:`k`:

    I.e. :math:`P^j ∧ P^{j+1} ∧ ⋯ ∧ P^{k-1} ∧ P^k`
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
        self.variables: list[FNode] = list(
            set(init.get_free_variables()).union((trans.get_free_variables())))
        self.init = init
        self.trans = trans

    def get_subs(self, i):
        """See :func:`get_subs`"""
        return get_subs(self.variables, i)

    def get_unrolling(self, k, j=0):
        """See :func:`get_unrolling`"""
        return get_unrolling(self.trans, k, j)


# BMC Induction

class BMCInduction:
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


# Interpolating Model Checking

def IMC(P: FNode,
        TS: TransitionSystem,
        S=None,
        interpolator=binary_interpolant,
        print_info=True):
    """
    Interpolating Model Checking

    As specified at S. Fulvio Rollini, “Craig Interpolation and Proof Manipulation:
    Theory and Applications to Model Checking,” Università della Svizzera Italiana. p.
    38. available at https://verify.inf.usi.ch/sites/default/files/RolliniPhDThesis.pdf

    A property to be verified is encoded as a formula :math:`P` , so that the system is
    safe if the error states where :math:`¬P` holds are not reachable from :math:`S`.

    Verifying that the system satisfies :math:`P` reduces to prove
    that :math:`P` is an inductive invariant property:

    .. math:: S ⊨ P\\qquad P ∧ T ⊨ P'

    If (i) the initial states satisfy :math:`P` and, (ii) assuming :math:`P` holds,
    it also holds after applying the transition relation, then :math:`P` holds in all
    reachable states. When the inductiveness of :math:`P` cannot be directly proved,
    it might be possible to show that another formula :math:`\\hat P`, stronger than
    :math:`P ( \\hat P ⊨ P )`, is an inductive invariant, from which :math:`P` would
    follow as a consequence; this algorithm, which combines interpolation and bounded
    model checking (BMC), is based on iteratively building such a :math:`\\hat P`.
    """

    #: S denotes the set of initial states
    if not S:
        S = TS.init

    # first makes sure P is not violated by S
    if m := get_model(S & Not(P)):
        # halt return a counterexample
        if print_info:
            print(f"[step 0] Initial state violates property:")
            print(f"{INDENT}Counterexample:")
            print(textwrap.indent(f"{m}", INDENT))
        return Status.UNSAFE1

    # bound
    k = 1

    # overapproximation of states at distance at most i from S
    i = 0
    R_i = S.substitute(TS.get_subs(i))

    # for a bound k and a current overapproximation R(i) of the states at distance at
    # most i from S, the algorithm checks if P is violated by the states reachable
    # from R(i) in at most k steps.
    while True:
        A = R_i & TS.get_unrolling(1)
        B = And(And(TS.get_unrolling(1, k)), Or(get_unrolling(Not(P), k)))
        if m := get_model(A & B):
            # the error might be real or spurious, caused by an insufficient value of k
            if is_valid(EqualsOrIff(R_i, S)):
                # error is real so the system is unsafe
                print(m)
                return Status.UNSAFE2
            else:
                # error is spurious so k is increased to allow finer
                # overapproximations, and the algorithm restarts from S.
                k += 1
                i = 0
                R_i = S.substitute(TS.get_subs(i))
        # R(i) ⋀_{j=0}^{k−1} T^j ⋁_{l=0}^k ¬P^l is unsat
        else:
            # an interpolant I(i) is computed, which represents an approximation of the
            # image of R(i) (i.e., of the states reachable from R(i) in one step).
            I_i = interpolator(A, B)

            # a fixpoint check is carried out: if I(i) |= R(i), it means that all
            # states have been covered, and the system is safe; otherwise, R(i + 1) is
            # set to R(i) ∨ I(i) and the procedure continues.
            if is_valid(I_i.Implies(R_i)):
                # the current R(i) corresponds to an inductive invariant P̂ stronger
                # than P: on one side, S |= R(i), moreover R(i) ∧ T |= I'(i) and I(i)
                # |= R(i) imply R(i) ∧ T |= R'(i); on the other side, the fact that at
                # each iteration 0 ≤ h ≤ i, R(h) ∧ ⋀_{j=0}^{k−1} T |= ⋀_{l=0}^k P^l,
                # together with R(i) being an inductive invariant, yield R(i) |= P.
                if print_info:
                    print(f"[step {i}] Proved safety: all states have been covered, "
                          f"and the system is safe")
                return Status.SAFE
            else:
                R_i = R_i | I_i
                i += 1


# PDR

def get_assignment_as_formula_from_model(M: Model):
    """
    :return: :math:`\\displaystyle\\bigwedge_{x ∈ \\operatorname{vars}(M)}\\left(\
        x ≡ ⟦x⟧_M
        \\right)`
    """
    if not M:
        return None
    return And([EqualsOrIff(x, v) for x, v in M])


def get_assignment_as_formula(F: FNode) -> None | FNode:
    """
    If formula :math:`F` is satisfiable, returns :math:`\\displaystyle\\bigwedge_{x_i ∈
    \\operatorname{vars}(F)} x_i ≡ v_i`, such that :math:`F` is true if each
    :math:`x_i` takes value :math:`v_i`otherwise returns :const:`None`.
    """
    return get_assignment_as_formula_from_model(get_model(F))


def _strenghten(k, Inv, o):
    """
    One possible implementation is attempting to drop components from a (disjunctive)
    invariant and checking if the remaining clause is still inductive.
    """


def _lift(k, Inv, Q, s, T):
    """
    We can implement lift using Craig interpolation between

    :math:`A: s = s_n` and
    :math:`B: Inv (s_n) ⋀_{i=n}^{n+k-1}( Q(s_i) ∧ T(s_i, s_{i+1}) ) ⇒ ¬Q(s_n+k)`

    because :math:`s` is a CTI, and therefore we know that :math:`A ⇒ B` holds. Hence,
    the resulting interpolant satisfies the criteria for :math:`C` to be a valid
    lifting of s according to the requirements towards the function lift.
    """
    A = get_unrolling(s, 0, 0)
    B = (get_unrolling(Inv, 0, 0) &
         get_unrolling(Q, k - 1) &
         get_unrolling(T, k - 1)
         ).Implies(Not(get_unrolling(Q, k, k)))
    from pysmt.exceptions import NoSolverAvailableError
    try:
        return binary_interpolant(A, B)
    except NoSolverAvailableError:
        return None


def get_base_case(k, I, T, P):
    """
    :return: :math:`I(0) ∧ \\displaystyle\\bigvee_{n=0}^{k-1}\\left(\\displaystyle\
        \\bigwedge_{i=0}^{n-1} T(i,i+1) ∧ ¬P(n)\
        \\right)`
    """
    return (
        get_unrolling(I, 0, 0) &
        Or([get_unrolling(T, n) &
            Not(get_unrolling(P, n, n))
            for n in range(k)])
    )


def get_step_case(k: int, T: FNode, P: FNode):
    """
    We assume this means that the forumla returned is an assertion over any k sequenece
    of states.

    :return: :math:`\\displaystyle\\bigvee_{i=n}^{n+k-1}\
        \\left(\
            P(i) ∧ T(i,i+1)\
        \\right)\
        ∧ ¬P(n)`
        with the idea that making :math:`n=0` in pySMT is equivalent to the formula above.
    """
    return (
        get_unrolling(P, k - 1) &
        get_unrolling(T, k - 1) &
        Not(get_unrolling(P, k, k))
    )


def PDR(P: FNode,
        TS: TransitionSystem,
        get_currently_known_invariant=lambda: TRUE(),
        strengthen=lambda k, Inv, o: Inv,
        lift=_lift,
        k_init: int = 1,
        k_max: int = float('inf'),
        pd: bool = True,
        inc: Callable[[int], int] = lambda n: n + 1,
        print_info=True
        ) -> bool | Status:
    """
    Iterative-Deepening k-Induction with Property Direction.

    As specified at D. Beyer and M. Dangl, “Software Verification with PDR:
    Implementation and Empirical Evaluation of the State of the Art” arXiv\:1908.06271
    [cs], Feb. 2020, Accessed: Mar. 05, 2022. [Online]. Available
    https://arxiv.org/abs/1908.06271.

    :param print_info: Whether info about the steps should be printed.
    :param k_init: the initial value :math:`≥1` for the bound `k`
    :param k_max: an upper limit for the bound `k`
    :param inc: a function :math:`ℕ → ℕ` such that :math:`∀n ∈ ℕ: \\inc(n) > n`
    :param TS: Contains predicates defining the initial states and the transfer relation
    :param P: The safety property
    :param get_currently_known_invariant: used to obtain the strongest invariant currently
        available via a concurrently running (external) auxiliary-invariant generator
    :param pd: boolean flag pd (reminding of “property-directed”) is used to control
        whether failed induction checks are used to guide the algorithm towards a
        sufficient strengthening of the safety property P to prove correctness; if pd is
        set to false, the algorithm behaves exactly like standard k-induction.
    :param lift: Given a failed attempt to prove some candidate invariant :math:`Q` by
        induction, the function lift is used to obtain from a concrete
        counterexample-to-induction (CTI) state a set of CTI states described by a state
        predicate C. An implementation of the function :math:`k ∈ ℕ, \\Inv ∈ ℕ × (S →
        𝔹) × (S → 𝔹) × S → (S → 𝔹)` and :math:`C = \\lift(k, \\Inv , Q, s)`, lift needs to
        satisfy the condition that for a CTI :math:`s ∈ S` where :math:`S` is the set of
        program states, the following holds:

        .. math:: C(s) ∧ \\left( ∀s_n ∈ S: C(s_n) ⇒\
            \\Inv(s_n) ∧
            \\displaystyle\\bigwedge_{i=n}^{n+k−1} (Q(s_i) ∧ T(s_i ,s_{i+1})) ⇒ ¬Q(s_{n+k}) \\right)

        which means that the CTI s must be an element of the set of states described by
        the resulting predicate C and that all states in this set must be CTIs, i.e.,
        they need to be k-predecessors of :math:`¬Q`-states, or in other words,
        each state in the set of states described by the predicate :math:`C` must reach
        some :math:`¬Q`-state via :math:`k` unrollings of the transition relation
        :math:`T`.
    :param strengthen: The function strengthen: :math:`ℕ × (S → 𝔹) × (S → 𝔹) → (S →
        𝔹)` is used to obtain for a k-inductive invariant a stronger k-inductive
        invariant, i.e., its result needs to imply the input invariant, and, just like the
        input invariant, it must not be violated within k loop iterations and must be
        k-inductive.
    :return: `True` if `P` holds, `Status.UNKNOWN` if `k > k_max` , `False` otherwise.
    """

    I = TS.init
    T = TS.trans

    # current bound
    k = k_init

    # the invariant computed by this algorithm internally
    InternalInv = TRUE()

    # the set of current proof obligations.
    O = set()

    while k <= k_max:
        O_prev = O
        O = set()

        # begin: base-case check (BMC)
        #
        # Base Case. The base case of k-induction consists of running BMC with the
        # current bound k. This means that starting from all initial program states, all
        # states of the program reachable within at most k−1 unwindings of the transition
        # relation are explored. If a ¬P-state is found, the algorithm terminates.
        base_case = get_base_case(k, I, T, P)
        if m := get_model(base_case):
            if print_info:
                print(f"[{k=}] base-case check failed")
                print(f"{INDENT}Counterexample:")
                # print(textwrap.indent(f"{str_model(m)}", INDENT))
                print(textwrap.indent(f"{m}", INDENT))
            return False
        # end ############################################################################

        # begin: forward-condition check (as described in Sec. 2)
        #
        # Forward Condition. If no ¬P-state is found by the BMC in the base case, the
        # algorithm continues by performing the forward-condition check, which attempts
        # to prove that BMC fully explored the state space of the program by checking
        # that no state with distance k′ > k−1 to the initial state is reachable. If this
        # check is successful, the algorithm terminates.
        forward_condition = get_unrolling(I, 0) & get_unrolling(T, k)
        if is_unsat(forward_condition):
            print(f"[{k=}] Proved correctness: successful forward condition check")
            return True
        # end ############################################################################

        # begin: attempt to prove each proof obligation using k-induction
        if pd:
            for o in O_prev:
                # begin: check the base case for a proof obligation o
                base_case_o = get_base_case(k, I, T, o)
                if is_sat(base_case_o):
                    # If any violations of the proof obligation o are found, this means
                    # that a predecessor state of a ¬P-state, and thus, transitively,
                    # a ¬P -state, is reachable, so we return false.
                    print(f"[{k=}] Found violation for proof obligation {o}")
                    return False
                # end ####################################################################

                else:
                    # no violation was found

                    # begin: check the inductive-step case to prove o
                    #
                    # Inductive-Step Case. The forward-condition check, however,
                    # can only prove safety for programs with finite (and, in practice
                    # short) loops. To prove safety beyond the bound k, the algorithm
                    # applies induction: The inductive-step case attempts to prove tha
                    # after every sequence of k unrollings of the transition relation
                    # that did not reach a ¬P-state, there can also be no subsequent
                    # transition into a ¬P-state by unwinding the transition relation
                    # once more. In the realm of model checking of software, however,
                    # the safety property P is often not directly k-inductive for any
                    # value of k, thus causing the inductive-step-case check to fail.
                    # It is therefore state-of-the-art practice to add auxiliary
                    # invariants to this check to further strengthen the induction
                    # hypothesis and make it more likely to succeed. Thus,
                    # the inductive-step case proves a program safe if the following
                    # condition is unsatisfiable:
                    #
                    #   Inv(s_n) ⋀_{i=n}^{n+k-1}(P(s_i) ∧ T(s_i,s_{i+1})) ∧ ¬P(s_{n+k})
                    #
                    # where Inv is an auxiliary invariant, and sₙ,…,sₙ₊ₖ is any
                    # sequence of states. If this check fails, the induction attempt is
                    # inconclusive, and the program is neither proved safe nor unsafe
                    # yet with the current value of k and the given auxiliary
                    # invariant. In this case, the algorithm increases the value of k
                    # and starts over.
                    step_case_o_n = get_step_case(k, T, o)
                    ExternalInv = get_currently_known_invariant()
                    Inv = InternalInv & ExternalInv
                    if m := get_model(get_unrolling(Inv, 0, 0) & step_case_o_n):
                        s_o = get_assignment_as_formula_from_model(m)
                        predicate_describing_set_of_CTI_states = lift(k, Inv, P, s_o, T)
                        if predicate_describing_set_of_CTI_states:
                            O = O.union(Not(predicate_describing_set_of_CTI_states))
                    else:
                        # If the step-case check for o is successful,
                        # we no longer track o in the set O of unproven proof obligations.

                        # We could now directly use the proof obligation as an
                        # invariant, but instead, we first try to strengthen it into a
                        # stronger invariant that removes even more unreachable states
                        # from future consideration before conjoining it to our
                        # internally computed auxiliary invariant. In our
                        # implementation, we implement strengthen by attempting to drop
                        # components from a (disjunctive) invariant and checking if the
                        # remaining clause is still inductive.
                        InternalInv &= strengthen(k, Inv, o)
                    # end ################################################################
        # end: attempt to prove each proof obligation using k-induction

        # begin: check the inductive-step case for the safety property P
        #
        # This check is mostly analogous to the inductive-step case check for the proof
        # obligations described above, except that if the check is successful,
        # we immediately return true.

        # Assume for any iteration n (k iterations from n to n + k − 1 = n) that the
        # safety property holds, and from this assumption attempt to conclude that the
        # safety property will also hold in the next iteration n + 1 (n + k).
        step_case_n = get_step_case(k, T, P)
        ExternalInv = get_currently_known_invariant()
        Inv = InternalInv & ExternalInv
        if m := get_model(get_unrolling(Inv, 0, 0) & step_case_n):
            if pd:
                s = get_assignment_as_formula_from_model(m)
                # Try to lift this state to a more abstract state that still satisfies
                # the property that all of its successors violate the safety property.
                if abstract_state := lift(k, Inv, P, s, T):
                    # Negate this abstract state to obtain the proof obligation.
                    # This means that we have learned that we should prove the
                    # invariant ¬o, such that in future induction checks, we can remove
                    # all states that satisfy `o` from the set of predecessor states
                    # that need to be considered.
                    O = O.union(Not(abstract_state))
        else:
            print(f"[{k=}] Proved correctness: safety property is inductive")
            return True
        # end ############################################################################

        k = inc(k)
    print("Property's status is unknown: exceeded maximum number of iterations")
    return Status.UNKNOWN


def test_pdr_on_trab_4():
    from util.examples.trab4 import trab4NoImplies, trab4FinalSimplification, trab4PDR
    example = trab4PDR(4)

    def get_currently_know_invariant(): return True

    for prop in example[1]:
        pprint(f"proving {prop[1]} ({prop[0].serialize()})")
        # bmcind.check_property(prop[0])
        print(PDR(prop[0], example[0], inc=lambda n: n+3),'\n')


if __name__ == "__main__":
    test_pdr_on_trab_4()

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
