from pysmt.shortcuts import *

from backend import *
from unfinished.interpolators import interp, itp


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
    x, y, c0, c1, m = Symbol("x", INT), Symbol("y", INT), Symbol("c0", INT), Symbol("c1",
                                                                                    INT), Symbol(
        "m", INT)
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
    from pysmt.typing import INT, BVType
    x = Symbol("x", INT)
    y = Symbol("y", BVType())
    binary_interpolant(y.Equals(0), x.Equals(0), logic="QF_IDL")


def example_failed_interpolation2():
    from pysmt.typing import INT, BVType
    x = Symbol("x", INT)
    y = Symbol("y", BVType())
    binary_interpolant(y.Equals(0), x.Equals(0))


def example_failed_interpolation3():
    from pysmt.typing import INT, BVType
    x = Symbol("x", INT)
    y = Symbol("y", BVType(4))
    formulas = [x.Equals(0), y.Equals(0)]
    itp(And(formulas))
