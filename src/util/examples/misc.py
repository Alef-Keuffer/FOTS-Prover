from pysmt.fnode import FNode
from pysmt.shortcuts import *

from backend import BMCInduction, IMC, itp, interp


def trab4NormalInterpolator():
    from util.examples.trab4 import trab4EvenMoreSimplified, trab4FinalSimplification, trab4NoImplies
    example = trab4NoImplies(4)
    bmcind = BMCInduction(example[0])
    for prop in example[1]:
        print(f"proving {prop[1]}")
        # bmcind.check_property(prop[0])
        print(IMC(example[0], prop[0]))


def trab4CustomInterpolator():
    from util.examples.trab4 import trab4EvenMoreSimplified, trab4FinalSimplification, trab4NoImplies
    example = trab4NoImplies(4, pc_is_bv=False)
    bmcind = BMCInduction(example[0])
    for prop in example[1]:
        print(f"proving {prop[1]}")
        # bmcind.check_property(prop[0])
        print(IMC(example[0], prop[0], customInterpolator=True))



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


def main():
    """
    .. execute_code::

        from backend import *
        trab4NormalInterpolator()
    """
    trab4NormalInterpolator()


if __name__ == "__main__":
    main()
    # example_failed_interpolation3()
    # print(example_interpolation())
    # print(example_interpolation2())
    # print(example_interpolation3())
