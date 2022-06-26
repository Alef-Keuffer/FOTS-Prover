from pysmt.fnode import FNode
from pysmt.shortcuts import *

from backend import next_var


def lifting_query(s: FNode, z, T, t: FNode):
    """
    The lifting query takes the form :math:`s ∧ z ∧ T ∧ ¬t'`, which asks whether an
    :math:`s`-state has a successor other than :math:`t` under input assignment
    :math:`z`. Since this is not the case by construction, the query yields an
    unsatisfiable core that typically reveals a significantly reduced partial
    assignment that can replace :math:`s`.

    As per J. Birgmeier, A. R. Bradley, and G. Weissenbacher, “Counterexample to
    Induction-Guided Abstraction-Refinement (CTIGAR),” p.6.
    """
    unsat_core = get_unsat_core([s, z, T, Not(next_var(t))])
    return And([EqualsOrIff(x, v) for x, v in unsat_core])


def pdr_pseudo():
    # IC3 for Finite State Transition Systems
    # p.4 from ctigar
    proof_obligations = []
    I = ...
    while proof_obligations:
        s, i = proof_obligations.pop()
        # attempt to prove that the state s that is backwards
        # reachable from ¬P is unreachable from F_i.
        t = ...
        if ...:
            # attempt succeeded
            # IC3 found a clause c ⊆ ¬s satisfying consecution
            # relative to F(i) (i.e., F(i) ∧ c ∧ T ⇒ c'),
            # strengthen frames F(1) , . . . , F(i+1) by adding c.
            ...
        else:
            # attempt failed so
            # failed consecution query reveals
            # a predecessor t of s.
            if i == 0 and is_sat(t & I):
                ...
            else:
                proof_obligations.append((t, i - 1))


def ctigar_pdr_pseudo():
    proof_obligations = []
    F = []
    I = ...
    T = ...
    while proof_obligations:
        s, i = proof_obligations.pop()
        # attempt to prove that the state s that is backwards
        # reachable from ¬P is unreachable from F_i.
        tm = get_model(Not((F[i] & Not(s) & T).Implies(Not(next_var(s)))))
        if tm:
            t = And(EqualsOrIff(x, v) for x, v in tm)
            t_prime = next_var(t)
            zm = get_model(Not((F[i] & Not(t) & T).Implies(Not(t_prime))))
            z = And(EqualsOrIff(x, v) for x, v in zm)
            lift_query = get_unsat_core([s, z, T, Not(t_prime)])