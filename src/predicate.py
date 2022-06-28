from pysmt.fnode import FNode
from pysmt.shortcuts import *
import re
from typing import NewType, Callable


def Variable(name: str, typename=types.BOOL) -> FNode:
    return Symbol(f"{name}@0", typename)


def at_time_plus(v: FNode, t: int = 0) -> FNode:
    """
    Builds an SMT variable representing v@k at time t, i.e., v@{k+i1}.
    If can be thought of as adding an offset `t` to the index of variable `v`.
    """
    reg = re.compile(r"(.+)@(.+)")
    var_name = reg.search(v.symbol_name()).group(1)
    var_index = int(reg.search(v.symbol_name()).group(2))
    return Symbol(f"{var_name}@{var_index + t}", v.symbol_type())


def prime(v: FNode) -> FNode:
    """
    Builds an SMT variable representing `v@k` at time `v@{k+1}`. See :func:`at_time_plus`
    """
    return at_time_plus(v, 1)


def instantiate_predicate_variables_at(P: FNode, i: int = 0) -> FNode:
    """
    Assumes the variables in :math:`P` are of the form `<var_name>'@'<number>` Will
    return a predicate with variables indexed using `i`. For example, suppose we
    create T ≡ x@1 = x@0 + 1, then x@{i+1} = x@i + 1 is returned.

    In general, given if x@k is in P, then it will be mapped to x@{k+i}

    :return: Predicate `new_P` such that for each `x@k` variable in `P` will
        correspond to `x@{k+i}` in `new_P`.
    """
    substitutions = {v: at_time_plus(v, i) for v in P.get_free_variables()}
    return P.substitute(substitutions)


class Predicate:
    def __init__(self, formula: FNode):
        self.formula = formula

    def at(self, i: int = 0) -> FNode:
        return instantiate_predicate_variables_at(self.formula, i)

    def prime(self) -> FNode:
        return self.at(1)

    def __matmul__(self, i: int = 0) -> FNode:
        return self.at(i)

    def unroll(self, start: int, end: int) -> FNode:
        # assert start <= end, "Unrolling start cannot be greater than end"
        if start > end:
            return TRUE()
        if start == end:
            return instantiate_predicate_variables_at(self.formula, start)
        return And([instantiate_predicate_variables_at(self.formula, i)
                    for i in range(start, end + 1)])

    def unroll_from_0(self, end: int) -> FNode:
        return self.unroll(0, end)

    def __xor__(self, i: int = 0) -> FNode:
        return self.unroll_from_0(i)

    def __getitem__(self, items) -> FNode:
        if isinstance(items, int):
            return self @ items
        if isinstance(items, slice):
            start = items.start
            stop = items.stop
            assert stop is not None
            if start is None:
                return self.unroll_from_0(stop)
            else:
                return self.unroll(start, stop)


def get_predicate(P: FNode) -> Callable[[int], FNode]:
    """
    Assumes the variables in :math:`P` are of the form `<var_name>'@'<number>` Will
    return a function that acts as a predicate that can be indexed. For example,
    suppose we create T ≡ x@1 = x@0 + 1, then T(i) ≡ x@{i+1} = x@i + 1
    """

    def new_P(i: int = 0) -> FNode:
        return instantiate_predicate_variables_at(P, i)

    return new_P


def main():
    x = Symbol("x@0")
    P = Predicate(x)
    print(f"{P^2 = }")
    print(f"{P@2 = }")
    print(f"{P@2 & (P^3) = }")
    print(f"{P[2] & P[:3] = }")
    print(f"{P[4:6] = }")


if __name__ == "__main__":
    main()
