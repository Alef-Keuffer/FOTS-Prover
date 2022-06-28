if __name__ == '__main__':
    from pysmt.shortcuts import *

    from backend import *
    from predicate import *

    pc = Predicate(Variable("pc", INT))
    x = Predicate(Variable("x", INT))
    y = Predicate(Variable("y", INT))
    z = Predicate(Variable("z", INT))
    w = Predicate(Variable("w", INT))
    r = Predicate(Variable("r", INT))

    variables = {pc, x, y, z, w, r}
    # Variables not in s are unchanged
    t = lambda s: And([v[1].Equals(v[0]) for v in variables if v not in s])

    t1 = pc[0].Equals(0) & pc[1].Equals(1) & t({pc})
    t2 = pc[0].Equals(1) & pc[1].Equals(1) & y[1].Equals(y[0] + 1) & z[1].Equals(
        z[0] + 1) & r[0].NotEquals(0) & t({pc})
    t3 = pc[0].Equals(1) & pc[1].Equals(2) & r[0].Equals(0) & t({pc})
    t4 = pc[0].Equals(2) & pc[1].Equals(2) & t({pc})

    T = Predicate(t1 | t2 | t3 | t4)
    I = Predicate(
        pc[0].Equals(0) & x[0].Equals(w[0]) & y[0].Equals(w[0] + 1) & z[0].Equals(
            x[0] + 1))
    prop1 = Predicate(pc[0].Equals(2).Implies(y[0].Equals(z[0])))

    print(IMC(I, T, prop1))
    print(PDR(I, T, prop1))
