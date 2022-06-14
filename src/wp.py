from pysmt.fnode import FNode
from pysmt.shortcuts import Symbol, And
from pysmt.typing import INT


def wp_(substitutions: dict[FNode, FNode], formula: FNode):
    freeSubs = {x: substitutions[x] for x in formula.get_free_variables()}
    return formula.substitute(freeSubs)


def is_next(s: str):
    return 'next(' == s[:5] and ')' == s[-1]


def prev_name(s: str):
    assert is_next(s)
    return s[5:][:-1]


def wp(ns, pos):
    """Based on https://www.cs.williams.edu/~freund/cs326/ReasoningPart1.html

    We usually want to use the precondition that guarantees correctness for the broadest set of inputs.
    Stated differently, we want the weakest precondition: the most general precondition needed to establish
    the postcondition. The terms “weak” and “strong” refer to how general or specific an assertion is.
    The weaker an assertion is, the more general it is; the stronger it is, the more specific it is.
    We write P = wp(S,Q) to indicate that P is the weakest precondition for statement S and postcondition Q."""
    wp = pos
    nextD = {}
    for phi in ns.get_atoms():
        if phi.is_equals():
            l, r = phi._content.args
            n = None
            a = None
            if l.is_symbol() and is_next(l.symbol_name()):
                n = l
                a = r
            if r.is_symbol() and is_next(r.symbol_name()):
                if n:
                    print('Equality between next variables')
                    continue
                n = r
                a = l
            if not a:
                print('No assignment made')
                continue
            nextD[prev_name(n.symbol_name())] = a
        else:
            wp &= phi
    for a in pos.get_free_variables():
        if (p := a.symbol_name()) in nextD:
            wp = wp.substitute({a: nextD[p]})
    return wp


def example1():
    """
    example:
    get
        nS: x = x + 1;
        pos: { x > 0 }
    return
        wp: { x + 1 > 0 }
    { x + 1 > 0 } = wp({ x > 0 },⟦x = x + 1⟧) -> { x > 0 }[x+1/x]
    """

    x = Symbol("x", INT)
    pos = x > 0
    return pos.substitute({x: x + 1})


def example2():
    from wd.trabalho4 import next_var
    # x = x + 1 ; assert x > 0
    x = Symbol("x", INT)
    nx = next_var(x)
    pos = And(x > 0, x > 1)
    ns = nx.Equals(x + 1)
    return wp(ns, pos)


class T:
    def __init__(self):
        self.variables = set()
        self.transitions = []

    @staticmethod
    def prime(v):
        new_name = f"{v.symbol_name()}′" if len(v.symbol_name) < 2 else f"({v.symbol_name()})′"
        return Symbol(new_name, v.symbol_type())

    def add_trans(self, S, NS):
        attributions = []
        for f in NS.get_atoms():
            if f.is_equals():
                l, r = f.args()
                l, r = (l if len(l.args()) == 0 else r, r if len(l.args()) == 0 else l)
                r = r if l != l else ...


print(example2())
