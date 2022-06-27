from pysmt.fnode import FNode
from pysmt.shortcuts import And


def is_next(v: FNode):
    name = v.symbol_name()
    return 'next(' == name[:5] and ')' == name[-1]


def prev_name(v: FNode):
    assert is_next(v)
    name = v.symbol_name()
    return name[5:][:-1]


def map_prev_to_next(variables: set[FNode]):
    return {v: nv
            for v in variables
            for nv in variables
            if is_next(nv) and v.symbol_name() == prev_name(nv)}


def get_formula_with_elements_fixed(nextVar: dict[FNode, FNode], s: FNode, ns: FNode = None):
    formula = s

    updatedVariables = set()
    if ns is not None:
        formula &= ns
        updatedVariables = ns.get_free_variables()

    formula &= And(nextVar[v].Equals(v) for v in nextVar if v not in updatedVariables)
    return formula


def get_transition_with_elements_fixed(transitions: list[tuple[FNode] | tuple[FNode, FNode]]):
    d = map_prev_to_next({v for t in transitions for f in t for v in f.get_free_variables()})

    formula = None
    for t in transitions:
        if len(t) == 1:
            phi = get_formula_with_elements_fixed(d, t[0])
        elif len(t) == 2:
            phi = get_formula_with_elements_fixed(d, t[0], t[1])
        if formula is None:
            formula = phi
        else:
            formula |= phi

    return formula


class TransitionPredicate:
    def __init__(self):
        self.__transitions: list[tuple[FNode] | tuple[FNode, FNode]] = []

    def add(self, s: FNode, ns: FNode = None):
        if ns is not None:
            self.__transitions.append((s, ns))
        else:
            self.__transitions.append(tuple([s]))

    def get(self):
        return get_transition_with_elements_fixed(self.__transitions)


def TS(s: FNode = None, ns: FNode = None, reset=False):
    if "__transitions" not in TS.__dict__:
        # __transitions: list[tuple[FNode] | tuple[FNode, FNode]]
        TS.__transitions = []

    if reset:
        TS.__transitions.clear()

    if s is not None:
        if ns is not None:
            TS.__transitions.append((s, ns))
        else:
            TS.__transitions.append(tuple([s]))

    return get_transition_with_elements_fixed(TS.__transitions)
