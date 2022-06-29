import textwrap
from typing import Callable, Set
from pysmt.fnode import FNode
from pysmt.shortcuts import *
from enum import Enum, auto
from pprint import pprint

# General
from pysmt.solvers.solver import Model

from predicate import Predicate, str_model, get_index

INDENT = '  '


class Status(Enum):
    UNSAFE = auto()
    SAFE = auto()
    UNSAFE1 = auto()
    UNSAFE2 = auto()
    SAT = auto()
    UNSAT = auto()
    UNKNOWN = auto()


# BMC Induction


def get_variables(*ps):
    return (v for v in
            set(q for p in ps
                for q in p[0].get_free_variables()
                if get_index(q) == '0'))


def get_simple_path(I, T, P, k):
    """Simple path constraint for k-induction:
    each time encodes a different state
    """
    variables = get_variables(I, T, P)
    res = []
    for i in range(k + 1):
        for j in range(i + 1, k + 1):
            state = []
            for v in variables:
                state.append(Not(EqualsOrIff(v[i], v[j])))
            res.append(Or(state))
    return And(res)


def get_k_induction(I, T, P, k):
    """Returns the K-Induction encoding at step K"""
    return And(T[:k],
               P[:k],
               get_simple_path(I, T, P, k),
               Not(P[k]))


def get_bmc(I, T, P, k):
    """Returns the BMC encoding at step k"""
    return And(I[0], T[:k], Not(P[k]))


def BMC_IND(I, T, P):
    """Interleaves BMC and K-Ind to verify the property."""
    print(f"Checking property {P[0]}...")
    from ply.cpp import xrange
    for b in xrange(100):
        f = get_bmc(I, T, P, b)
        print(f"   [BMC]    Checking bound {b + 1}...")
        if is_sat(f):
            print(f"--> Bug found at step {b + 1}")
            return

        f = get_k_induction(I, T, P, b)
        print(f"   [K-IND]  Checking bound {b + 1}...")
        if is_unsat(f):
            print("--> The system is safe!")
            return


# Interpolating Model Checking

def IMC(S: Predicate,
        T: Predicate,
        P: Predicate,
        interpolator: Callable[[FNode, FNode], FNode] = binary_interpolant,
        print_info: bool = True):
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

    # first makes sure P is not violated by S
    print("Checking if initial states violates safety property")
    if m := get_model(S[0] & ~P[0]):
        # halt return a counterexample
        if print_info:
            print(f"[step 0] Initial state violates property:")
            print(f"{INDENT}Counterexample:")
            print(textwrap.indent(f"{m}", INDENT))
        return Status.UNSAFE1

    # bound
    k = 2

    # overapproximation of states at distance at most i from S
    i = 0
    R = S[0]

    # for a bound k and a current overapproximation R(i) of the states at distance at
    # most i from S, the algorithm checks if P is violated by the states reachable
    # from R(i) in at most k steps.
    while True:
        A = R & T[0]
        B = T[1:k - 1] & Or(~P[l] for l in range(k + 1))
        print(f"[{i=},{k=}] Checking BMC from R(i)")
        if m := get_model(A & B):
            # the error might be real or spurious, caused by an insufficient value of k
            if is_valid(EqualsOrIff(R, S[0])):
                print(f"[{i=},{k=}] Checking if R=S")
                # error is real so the system is unsafe
                print(m)
                return Status.UNSAFE2
            else:
                # error is spurious so k is increased to allow finer
                # overapproximations, and the algorithm restarts from S.
                print(f"[{i=},{k=}] R != S")
                k += 1
                i = 0
                R = S[0]
        # R(i) ⋀_{j=0}^{k−1} T^j ⋁_{l=0}^k ¬P^l is unsat
        else:
            # an interpolant I(i) is computed, which represents an approximation of the
            # image of R(i) (i.e., of the states reachable from R(i) in one step).
            print(f"[{i=},{k=}] Calculating interpolant")
            I = interpolator(A, B)

            # a fixpoint check is carried out: if I(i) |= R(i), it means that all
            # states have been covered, and the system is safe; otherwise, R(i + 1) is
            # set to R(i) ∨ I(i) and the procedure continues.
            if is_valid(I.Implies(R)):
                # the current R(i) corresponds to an inductive invariant P̂ stronger
                # than P: on one side, S |= R(i), moreover R(i) ∧ T |= I'(i) and I(i)
                # |= R(i) imply R(i) ∧ T |= R'(i); on the other side, the fact that at
                # each iteration 0 ≤ h ≤ i, R(h) ∧ ⋀_{j=0}^{k−1} T |= ⋀_{l=0}^k P^l,
                # together with R(i) being an inductive invariant, yield R(i) |= P.
                if print_info:
                    # print(f"R({i}) = ", R.simplify().serialize())
                    print(f"[{i=},{k=}] Proved safety: all states have been covered, "
                          f"and the system is safe")
                return Status.SAFE
            else:
                print(f"[{i=},{k=}] I !=> R")
                R |= I
                i += 1


# PDR

def get_assignment_as_formula_from_model(M: Model) -> None | FNode:
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


def _strenghten(k: int, Inv: Predicate, o: Predicate) -> FNode:
    """
    One possible implementation is attempting to drop components from a (disjunctive)
    invariant and checking if the remaining clause is still inductive.
    """


def _lift(k: int, Inv: Predicate, Q: Predicate, s: Predicate,
          T: Predicate) -> None | FNode:
    """
    We can implement lift using Craig interpolation between

    :math:`A: s = s_n` and
    :math:`B: Inv (s_n) ⋀_{i=n}^{n+k-1}( Q(s_i) ∧ T(s_i, s_{i+1}) ) ⇒ ¬Q(s_n+k)`

    because :math:`s` is a CTI, and therefore we know that :math:`A ⇒ B` holds. Hence,
    the resulting interpolant satisfies the criteria for :math:`C` to be a valid
    lifting of s according to the requirements towards the function lift.
    """
    A = s[0]
    B = (Inv[0] &
         Q[:k - 1] &
         T[:k - 1]
         ).Implies(Not(Q @ k))
    from pysmt.exceptions import NoSolverAvailableError
    try:
        return binary_interpolant(A, B)
    except NoSolverAvailableError:
        return None


def get_base_case(k: int, I: Predicate, T: Predicate, P: Predicate) -> FNode:
    """
    :return: :math:`I(0) ∧ \\displaystyle\\bigvee_{n=0}^{k-1}\\left(\\displaystyle\
        \\bigwedge_{i=0}^{n-1} T(i,i+1) ∧ ¬P(n)\
        \\right)`
    """
    return And(
        I[0],
        Or([T[:n - 1] & ~P[n] for n in range(k)])
    )


def get_step_case(k: int, T: Predicate, P: Predicate) -> FNode:
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
    return And(
        (P[:k - 1]),
        (T[:k - 1]),
        # Should we do Or(~P[i] for i in range(k+1)) instead of
        # ~P[k]?
        ~P[k],
        # Or(~P[i] for i in range(k+1))
    )


def PDR(I: Predicate,
        T: Predicate,
        P: Predicate,
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

    # current bound
    k: int = k_init

    # the invariant computed by this algorithm internally
    InternalInv: FNode = TRUE()

    # the set of current proof obligations.
    O: Set[Predicate] = set()

    while k <= k_max:
        O_prev: Set[Predicate] = O
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
                print(textwrap.indent(f"{str_model(m)}", INDENT))
                # print(textwrap.indent(f"{m}", INDENT))
            return False
        # end ############################################################################

        # begin: forward-condition check (as described in Sec. 2)
        #
        # Forward Condition. If no ¬P-state is found by the BMC in the base case, the
        # algorithm continues by performing the forward-condition check, which attempts
        # to prove that BMC fully explored the state space of the program by checking
        # that no state with distance k′ > k−1 to the initial state is reachable. If this
        # check is successful, the algorithm terminates.
        forward_condition = I[0] & T[:k - 1]
        if is_unsat(forward_condition):
            print(f"[{k=}] Proved correctness: successful forward condition check")
            pprint(forward_condition.serialize())
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
                    Inv = Predicate(InternalInv & ExternalInv)
                    if m := get_model(Inv[0] & step_case_o_n):
                        s_o = Predicate(get_assignment_as_formula_from_model(m))
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
        Inv = Predicate(InternalInv & ExternalInv)
        if m := get_model(Inv[0] & step_case_n):
            if pd:
                s = get_assignment_as_formula_from_model(m)
                # Try to lift this state to a more abstract state that still satisfies
                # the property that all of its successors violate the safety property.
                if abstract_state := lift(k, Inv, P, Predicate(s), T):
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
