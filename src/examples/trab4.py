from pysmt.shortcuts import *

from backend import *

"""
assume m >= 0 and n >= 0 and r == 0 and x == m and y == n
0: while y > 0:
1:    if y & 1 == 1:
            y , r  = y-1 , r+x
2:    x , y = x<<1  ,  y>>1
3: assert r == m * n

V ≡ (y - pc) + 3
positivo ≡ V ≥ 0
decresce ≡ T ⟹ V' ≤ V ∨ V' = 0
terminacao ≡ V = 0 ⟹ pc=3
INV ≡ (m ⋅ n = x ⋅ y + r) ∧ y ≥ 0
"""

# g = {v: Symbol(v, BVType(bit_count)) for v in {'x', 'm', 'n', 'y', 'r'}}

def trab4NoImplies(bit_count, pc_is_bv=True):
    from pysmt.typing import BVType, INT

    # Variables
    x = Symbol("x", BVType(bit_count))
    m = Symbol("m", BVType(bit_count))
    n = Symbol("n", BVType(bit_count))
    y = Symbol("y", BVType(bit_count))
    r = Symbol("r", BVType(bit_count))

    if pc_is_bv:
        pc = Symbol("pc", BVType(bit_count))
    else:
        pc = Symbol("pc", INT)

    npc = next_var(pc)
    ny = next_var(y)
    nx = next_var(x)
    nr = next_var(r)

    d = {x: nx, y: ny, r: nr, pc: npc}
    t = lambda s: And([d[v].Equals(v) for v in d if v not in s])

    # pc = 0 ∧ y > 0 ∧ pc′ = 1                  enters WHILE
    p1 = pc.Equals(0) & (y > 0) & npc.Equals(1) & t({pc})
    # pc = 0 ∧ y ≤ 0 ∧ pc′ = 3                 doesn't enters WHILE
    p2 = pc.Equals(0) & (y <= 0) & npc.Equals(3) & t({pc})
    # pc = 1 ∧ y & 1 = 1 ∧ y′ = y − 1 ∧ r′ = r + x ∧ pc′ = 2      IF condition is true
    p3 = pc.Equals(1) & (y & 1).Equals(1) & npc.Equals(2) & ny.Equals(y - 1) & nr.Equals(r + x) & t({pc, y, r})
    # pc = 1 ∧ y & 1 ≠ 1 ∧ pc′ = 2                      IF condition is false
    p4 = pc.Equals(1) & (y & 1).NotEquals(1) & npc.Equals(2) & t({pc})
    # pc = 2 ∧ y′ = y >> 1 ∧ x′ = x << 1 ∧ pc′ = 0      loop back after attributions
    p5 = pc.Equals(2) & npc.Equals(0) & nx.Equals(x << 1) & ny.Equals(y >> 1) & t({pc, x, y})
    # pc = 3 ∧ pc ′ = 3         end of program
    p6 = pc.Equals(3) & t({})

    pre = ((m >= 0) &  # m ≥ 0
           (n >= 0) &  # n ≥ 0
           r.Equals(0) &  # r = 0
           x.Equals(m) &  # x = m
           y.Equals(n)  # y = n
           )

    init = pc.Equals(0) & pre

    trans = Or(p1, p2, p3, p4, p5, p6)

    if pc_is_bv:
        V = (y - pc) + 3
        nV = (ny - npc) + 3
    else:
        V = (BVToNatural(y) - pc) + 3
        nV = (BVToNatural(ny) - npc) + 3

    prop_positivo = V >= 0
    prop_decresce = (trans & (y < 13)).Implies((nV < V) | nV.Equals(0))
    prop_terminacao = ((V.Equals(0) & (y < 13)).Implies(pc.Equals(3)))
    invariant = (m * n).Equals(x * y + r) & (y >= 0)
    prop_pre_implies_inv = pre.Implies(invariant)
    prop_cond3 = (invariant & (y <= 0) & trans).Implies(r.Equals(m * n) & npc.Equals(3))
    prop_cond3_2 = (invariant & (y <= 0)).Implies(r.Equals(m * n) & pc.Equals(0))

    inv_prop_cond3 = (invariant & (y <= 0) & pc.Equals(0)).Implies(r.Equals(m * n))
    subprop = (invariant & (y <= 0) & trans).Implies(npc.Equals(3))  # falso como????
    mypost = pc.Equals(3).Implies(r.Equals(m * n))  # nao consegue
    return (
        TransitionSystem(init, trans),
        [(prop_positivo, "prop_positivo"),
         (prop_terminacao, "prop_terminacao"),
         (prop_pre_implies_inv, "prop_pre_implies_inv"),
         (inv_prop_cond3, "inv_prop_cond3"),
         (prop_decresce, "prop_decresce"),
         (prop_cond3, "prop_cond3"),
         (prop_cond3_2, "prop_cond3_2"),
         (mypost, "mypost"),
         (subprop, "subprop"),
         ])


def trab4PDR(bit_count, pc_is_bv=True):
    from pysmt.typing import BVType, INT

    # Variables
    x = Symbol("x", BVType(bit_count))
    m = Symbol("m", BVType(bit_count))
    n = Symbol("n", BVType(bit_count))
    y = Symbol("y", BVType(bit_count))
    r = Symbol("r", BVType(bit_count))
    if pc_is_bv:
        pc = Symbol("pc", BVType(bit_count))
    else:
        pc = Symbol("pc", INT)

    npc = next_var(pc)
    ny = next_var(y)
    nx = next_var(x)
    nr = next_var(r)

    nm = next_var(m)
    nn = next_var(n)

    d = {x: nx, y: ny, r: nr, pc: npc, n: nn, m: nm}

    t = lambda s: And([d[v].Equals(v) for v in d if v not in s])
    # pc = 0 ∧ y > 0 ∧ pc′ = 1                  enters WHILE
    p1 = pc.Equals(0) & (y > 0) & npc.Equals(1) & t({pc})
    # pc = 0 ∧ y ≤ 0 ∧ pc′ = 3                 doesn't enters WHILE
    p2 = pc.Equals(0) & (y <= 0) & npc.Equals(3) & t({pc})
    # pc = 1 ∧ y & 1 = 1 ∧ y′ = y − 1 ∧ r′ = r + x ∧ pc′ = 2      IF condition is true
    p3 = pc.Equals(1) & (y & 1).Equals(1) & npc.Equals(2) & ny.Equals(y - 1) & nr.Equals(r + x) & t({pc, y, r})
    # pc = 1 ∧ y & 1 ≠ 1 ∧ pc′ = 2                      IF condition is false
    p4 = pc.Equals(1) & (y & 1).NotEquals(1) & npc.Equals(2) & t({pc})
    # pc = 2 ∧ y′ = y >> 1 ∧ x′ = x << 1 ∧ pc′ = 0      loop back after attributions
    p5 = pc.Equals(2) & npc.Equals(0) & nx.Equals(x << 1) & ny.Equals(y >> 1) & t({pc, x, y})
    # pc = 3 ∧ pc ′ = 3         end of program
    p6 = pc.Equals(3) & t({})

    pre = ((m >= 0) &  # m ≥ 0
           (n >= 0) &  # n ≥ 0
           r.Equals(0) &  # r = 0
           x.Equals(m) &  # x = m
           y.Equals(n)  # y = n
           )

    init = pc.Equals(0) & pre

    trans = Or(p1, p2, p3, p4, p5, p6)

    """
    V ≡ (y - pc) + 3
    positivo ≡ V ≥ 0
    decresce ≡ T ⟹ V' ≤ V ∨ V' = 0
    terminacao ≡ V = 0 ⟹ pc=3
    INV ≡ (m ⋅ n = x ⋅ y + r) ∧ y ≥ 0
    """

    if pc_is_bv:
        V = (y - pc) + 3
        nV = (ny - npc) + 3
    else:
        V = (BVToNatural(y) - pc) + 3
        nV = (BVToNatural(ny) - npc) + 3

    n2y = next_var(ny)
    n2pc = next_var(npc)
    n3y = next_var(n2y)
    n3pc = next_var(n2pc)
    n3V = (n3y - n3pc) + 3
    prop_decresce_com_unrolling = (get_unrolling(trans, 3) & (y < 13)).Implies((n3V < V) | n3V.Equals(0))

    prop_positivo = V >= 0
    prop_decresce = (trans & (y < 13)).Implies((nV < V) | nV.Equals(0))
    prop_terminacao = (V.Equals(0) & (y < 13)).Implies(pc.Equals(3))
    invariant = (m * n).Equals(x * y + r) & (y >= 0)
    prop_pre_implies_inv = pre.Implies(invariant)
    prop_cond3 = (invariant & (y <= 0) & trans).Implies(r.Equals(m * n) & npc.Equals(3))
    prop_cond3_2 = (invariant & (y <= 0)).Implies(r.Equals(m * n) & pc.Equals(0))

    inv_prop_cond3 = (invariant & (y <= 0) & pc.Equals(0)).Implies(r.Equals(m * n))
    subprop = (invariant & (y <= 0) & trans).Implies(npc.Equals(3))  # falso como????
    mypost = pc.Equals(3).Implies(r.Equals(m * n))  # nao consegue
    return (
        TransitionSystem(init, trans),
        [(prop_positivo, "prop_positivo"),
         (prop_decresce_com_unrolling, "prop_decresce_com_unrolling"),
         (prop_terminacao, "prop_terminacao"),
         (prop_pre_implies_inv, "prop_pre_implies_inv"),
         (inv_prop_cond3, "inv_prop_cond3"),
         (prop_decresce, "prop_decresce"),
         (prop_cond3, "prop_cond3"),
         (prop_cond3_2, "prop_cond3_2"),
         (mypost, "mypost"),
         (subprop, "subprop"),
         ])


def trab4Simplified(bit_count):
    from pysmt.typing import BVType

    # Variables
    x = Symbol("x", BVType(bit_count))
    m = Symbol("m", BVType(bit_count))
    n = Symbol("n", BVType(bit_count))
    y = Symbol("y", BVType(bit_count))
    r = Symbol("r", BVType(bit_count))
    pc = Symbol("pc", BVType(bit_count))

    npc = next_var(pc)
    ny = next_var(y)
    nx = next_var(x)
    nr = next_var(r)

    from util.transition_deprecated import T_v1
    T_v1(variables=[x, nx, y, ny, r, nr, pc, npc])

    # pc = 0 ∧ y > 0 ∧ pc′ = 1                  enters WHILE
    p1 = T_v1(pc.Equals(0) & (y > 0), npc.Equals(1))
    # pc = 0 ∧ y ≤ 0 ∧ pc′ = 3                 doesn't enters WHILE
    p2 = T_v1(pc.Equals(0) & (y <= 0), npc.Equals(3))
    # pc = 1 ∧ y & 1 = 1 ∧ y′ = y − 1 ∧ r′ = r + x ∧ pc′ = 2      IF condition is true
    p3 = T_v1(pc.Equals(1) & (y & 1).Equals(1), npc.Equals(2) & ny.Equals(y - 1) & nr.Equals(r + x))
    # pc = 1 ∧ y & 1 ≠ 1 ∧ pc′ = 2                      IF condition is false
    p4 = T_v1(pc.Equals(1) & (y & 1).NotEquals(1), npc.Equals(2))
    # pc = 2 ∧ y′ = y >> 1 ∧ x′ = x << 1 ∧ pc′ = 0      loop back after attributions
    p5 = T_v1(pc.Equals(2), npc.Equals(0) & nx.Equals(x << 1) & ny.Equals(y >> 1))
    # pc = 3 ∧ pc ′ = 3         end of program
    p6 = T_v1(pc.Equals(3))

    pre = ((m >= 0) &  # m ≥ 0
           (n >= 0) &  # n ≥ 0
           r.Equals(0) &  # r = 0
           x.Equals(m) &  # x = m
           y.Equals(n)  # y = n
           )

    init = pc.Equals(0) & pre

    trans = Or(p1, p2, p3, p4, p5, p6)

    V = (y - pc) + 3
    prop_positivo = V >= 0
    prop_terminacao = (V.Equals(0).Implies(pc.Equals(3)))
    invariant = (m * n).Equals(x * y + r) & (y >= 0)
    prop_pre_implies_inv = pre.Implies(invariant)
    prop_cond3 = (invariant & (y <= 0)).Implies(r.Equals(m * n) & pc.NotEquals(2))
    subprop = (invariant & (y <= 0)).Implies(pc.Equals(3))  # falso como????
    mypost = pc.Equals(3).Implies(r.Equals(m * n))  # nao consegue

    return (
        TransitionSystem(init, trans),
        [prop_positivo, prop_terminacao, prop_pre_implies_inv, prop_cond3, mypost, subprop])


def prog4(m, n):
    x = m
    y = n
    r = 0
    assert m >= 0 and n >= 0 and r == 0 and x == m and y == n

    s = lambda: '(' + ', '.join([f"{k} = {v}" for k, v in {'r': r, 'x': x, 'y': y, 'm': m, 'n': n}.items()]) + ')'


    pc = 0
    print(f"[{pc=} V={y-pc+3}] {s()}")
    while y > 0:
        pc += 1
        print(f"[{pc=} V={y-pc+3}] start cycle: {s()}")
        if y & 1 == 1:
            y -= 1
            r += x
        pc += 1
        print(f"[{pc=} V={y-pc+3}] after if: {s()}")
        x <<= 1
        y >>= 1
        pc = 0
        print(f"[{pc=} V={y-pc+3}] {s()}")
    assert r == m * n
    print(f"[{pc=} V={y-pc+3}] after cycle: {s()}")


def trab4EvenMoreSimplified(bit_count):
    from pysmt.typing import BVType

    # Variables
    x = Symbol("x", BVType(bit_count))
    m = Symbol("m", BVType(bit_count))
    n = Symbol("n", BVType(bit_count))
    y = Symbol("y", BVType(bit_count))
    r = Symbol("r", BVType(bit_count))
    pc = Symbol("pc", BVType(bit_count))

    npc = next_var(pc)
    ny = next_var(y)
    nx = next_var(x)
    nr = next_var(r)

    from util.transition import TS

    # pc = 0 ∧ y > 0 -> pc′ = 1                  enters WHILE
    TS(pc.Equals(0) & (y > 0), npc.Equals(1))
    # pc = 0 ∧ y ≤ 0 -> pc′ = 3                 doesn't enters WHILE
    TS(pc.Equals(0) & (y <= 0), npc.Equals(3))
    # pc = 1 ∧ y & 1 = 1 -> y′ = y − 1 ∧ r′ = r + x ∧ pc′ = 2      IF condition is true
    TS(pc.Equals(1) & (y & 1).Equals(1), npc.Equals(2) & ny.Equals(y - 1) & nr.Equals(r + x))
    # pc = 1 ∧ y & 1 ≠ 1 -> pc′ = 2                      IF condition is false
    TS(pc.Equals(1) & (y & 1).NotEquals(1), npc.Equals(2))
    # pc = 2 -> y′ = y >> 1 ∧ x′ = x << 1 ∧ pc′ = 0      loop back after attributions
    TS(pc.Equals(2), npc.Equals(0) & nx.Equals(x << 1) & ny.Equals(y >> 1))
    # pc = 3         end of program
    TS(pc.Equals(3))

    pre = ((m >= 0) &  # m ≥ 0
           (n >= 0) &  # n ≥ 0
           r.Equals(0) &  # r = 0
           x.Equals(m) &  # x = m
           y.Equals(n)  # y = n
           )

    init = pc.Equals(0) & pre

    V = (y - pc) + 3
    prop_positivo = V >= 0
    prop_terminacao = (V.Equals(0).Implies(pc.Equals(3)))
    invariant = (m * n).Equals(x * y + r) & (y >= 0)
    prop_pre_implies_inv = pre.Implies(invariant)
    prop_cond3 = (invariant & (y <= 0)).Implies(r.Equals(m * n) & pc.NotEquals(2))
    mypost = pc.Equals(3).Implies(r.Equals(m * n))  # nao consegue
    subprop = (invariant & (y <= 0)).Implies(npc.Equals(3))  # falso como????

    return (
        TransitionSystem(init, TS()),
        [prop_positivo, prop_terminacao, prop_pre_implies_inv, prop_cond3, mypost, subprop])


def trab4FinalSimplification(bit_count):
    from pysmt.typing import BVType

    # Variables
    x = Symbol("x", BVType(bit_count))
    m = Symbol("m", BVType(bit_count))
    n = Symbol("n", BVType(bit_count))
    y = Symbol("y", BVType(bit_count))
    r = Symbol("r", BVType(bit_count))
    pc = Symbol("pc", BVType(bit_count))

    npc = next_var(pc)
    ny = next_var(y)
    nx = next_var(x)
    nr = next_var(r)

    from util.transition import TransitionPredicate

    T = TransitionPredicate()

    # pc = 0 ∧ y > 0 -> pc′ = 1                  enters WHILE
    T.add(pc.Equals(0) & (y > 0), npc.Equals(1))
    # pc = 0 ∧ y ≤ 0 -> pc′ = 3                 doesn't enters WHILE
    T.add(pc.Equals(0) & (y <= 0), npc.Equals(3))
    # pc = 1 ∧ y & 1 = 1 -> y′ = y − 1 ∧ r′ = r + x ∧ pc′ = 2      IF condition is true
    T.add(pc.Equals(1) & (y & 1).Equals(1), npc.Equals(2) & ny.Equals(y - 1) & nr.Equals(r + x))
    # pc = 1 ∧ y & 1 ≠ 1 -> pc′ = 2                      IF condition is false
    T.add(pc.Equals(1) & (y & 1).NotEquals(1), npc.Equals(2))
    # pc = 2 -> y′ = y >> 1 ∧ x′ = x << 1 ∧ pc′ = 0      loop back after attributions
    T.add(pc.Equals(2), npc.Equals(0) & nx.Equals(x << 1) & ny.Equals(y >> 1))
    # pc = 3         end of program
    T.add(pc.Equals(3))

    pre = ((m >= 0) &  # m ≥ 0
           (n >= 0) &  # n ≥ 0
           r.Equals(0) &  # r = 0
           x.Equals(m) &  # x = m
           y.Equals(n)  # y = n
           )

    init = pc.Equals(0) & pre
    V = (y - pc) + 3
    prop_positivo = V >= 0
    prop_terminacao = (V.Equals(0).Implies(pc.Equals(3)))
    invariant = (m * n).Equals(x * y + r) & (y >= 0)
    prop_pre_implies_inv = pre.Implies(invariant)
    prop_cond3 = (invariant & (y <= 0) & npc.Equals(3))
    mypost = pc.Equals(3).Implies(r.Equals(m * n))  # nao consegue
    subprop = (invariant & (y <= 0)).Implies(npc.Equals(3))  # falso como????

    return (
        TransitionSystem(init, T.get()),
        [(prop_positivo, "prop_positivo"),
         (prop_terminacao, "prop_terminacao"),
         (prop_pre_implies_inv, "prop_pre_implies_inv"),
         (prop_cond3, "prop_cond3"),
         (mypost, "mypost"),
         (subprop, "subprop")])
