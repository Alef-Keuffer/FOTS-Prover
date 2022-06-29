if __name__ == '__main__':
    from pysmt.shortcuts import *
    from backend import *

    x = Symbol('x', INT)
    y = Symbol('y', INT)
    N = Symbol('N', INT)
    M = Symbol('M', INT)

    nx = next_var(x)
    ny = next_var(y)

    nN = next_var(N)
    nM = next_var(M)

    d = {x: nx, y: ny, N: nN, M: nM}
    t = lambda s: And([d[v].Equals(v) for v in d if v not in s])

    T = (
            (x > y
             & nx.Equals(x - y)
             & ny.Equals(y))
            | (y > x
               & ny.Equals(y - x)
               & nx.Equals(x))
    )

    I = x.Equals(M) & y.Equals(N)
