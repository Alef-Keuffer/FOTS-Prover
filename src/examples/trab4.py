from backend import *
from predicate import *


def main():
    bit_count = 4
    x = Predicate(Variable('x', BVType(bit_count)))
    m = Predicate(Variable("m", BVType(bit_count)))
    n = Predicate(Variable("n", BVType(bit_count)))
    y = Predicate(Variable("y", BVType(bit_count)))
    r = Predicate(Variable("r", BVType(bit_count)))
    pc = Predicate(Variable('pc', BVType(bit_count)))

    variables = {x, y, r, m, n, pc}
    # Variables not in s are unchanged
    t = lambda s: And([v[1].Equals(v[0]) for v in variables if v not in s])

    WhileCondition = Predicate(y[0] > 0)

    #: pc = 0 ∧ y > 0 ∧ pc′ = 1                  WHILE condition is True
    p1 = And(
        pc[0].Equals(0),
        pc[1].Equals(1),
        WhileCondition[0],
        t({pc})
    )

    #: pc = 0 ∧ y ≤ 0 ∧ pc′ = 3                  WHILE condition is False
    p2 = And(
        pc[0].Equals(0),
        pc[1].Equals(3),
        Not(WhileCondition[0]),
        t({pc})
    )

    IfCondition = Predicate((y[0] & 1).Equals(1))

    #: pc = 1 ∧ y & 1 = 1 ∧ y′ = y − 1 ∧ r′ = r + x ∧ pc′ = 2      IF condition is true
    p3 = And(
        pc[0].Equals(1),
        pc[1].Equals(2),
        IfCondition[0],
        y[1].Equals(y[0] - 1),
        r[1].Equals(r[0] + x[0]),
        t({pc, y, r})
    )

    # pc = 1 ∧ y & 1 ≠ 1 ∧ pc′ = 2                      IF condition is false
    p4 = And(
        pc[0].Equals(1),
        pc[1].Equals(2),
        Not(IfCondition[0]),
        t({pc})
    )

    # pc = 2 ∧ y′ = y >> 1 ∧ x′ = x << 1 ∧ pc′ = 0      loop back after attributions
    p5 = And(
        pc[0].Equals(2),
        pc[1].Equals(0),
        x[1].Equals(x[0] << 1),
        y[1].Equals(y[0] >> 1),
        t({pc, x, y})
    )

    # pc = 3 ∧ pc′ = 3         end of program
    p6 = pc[0].Equals(3) & t({})

    trans = Or(p1, p2, p3, p4, p5, p6)
    T = Predicate(trans)

    pre = And(
        (m[0] >= 0),  # m ≥ 0
        (n[0] >= 0),  # n ≥ 0
        r[0].Equals(0),  # r = 0
        x[0].Equals(m[0]),  # x = m
        y[0].Equals(n[0])  # y = n
    )

    post = r[0].Equals(m[0] * n[0])
    init = pc[0].Equals(0) & pre
    I = Predicate(init)

    #: Variant
    V = Predicate((y[0] - pc[0]) + 3)

    # Necessary because we are working in the theory of bit vectors.
    # We are working in the theory of bit vectors because no interpolator is available in
    # pySMT when bit vectors are mixed with integers.
    overflow_condition_for_variant = 2 ** bit_count - 3
    variant_is_non_negative = V[0] >= 0
    variant_is_strictly_decreasing = (
            T[0:2] &
            (y[0] < overflow_condition_for_variant)).Implies(
        (V[3] < V[0]) | V[3].Equals(0))
    variant_equals_zero_implies_termination = (
        (V[0].Equals(0) &
         (y[0] < overflow_condition_for_variant)).Implies(
            pc[0].Equals(3)))

    invariant = (m[0] * n[0]).Equals(x[0] * y[0] + r[0]) & (y[0] >= 0)
    precondition_implies_invariant = pre.Implies(invariant)
    loop_termination_implies_postcondition = (
            invariant &
            (~WhileCondition[0])).Implies(post)
    invariant_is_true_after_loop = ...

    wrong_prop = (n[0].NotEquals(0) & pc[0].Equals(3)).Implies(y[0].NotEquals(0))
    wrong_prop2 = (n[0].Equals(12) & pc[0].Equals(3)).Implies(y[0].NotEquals(0))

    # prop_cond3 = (invariant & (y <= 0) & trans).Implies(r.Equals(m * n) & npc.Equals(3))
    # prop_cond3_2 = (invariant & (y <= 0)).Implies(r.Equals(m * n) & pc.Equals(0))
    # inv_prop_cond3 = (invariant & (y <= 0) & pc.Equals(0)).Implies(r.Equals(m * n))
    # subprop = (invariant & (y <= 0) & trans).Implies(npc.Equals(3))  # falso como????
    # mypost = pc.Equals(3).Implies(r.Equals(m * n))  # nao consegue

    properties = [
        (variant_is_non_negative, "variant_is_non_negative"),
        (variant_is_strictly_decreasing, "variant_is_strictly_decreasing"),
        (variant_equals_zero_implies_termination,
         "variant_equals_zero_implies_termination"),
        (precondition_implies_invariant, "precondition_implies_invariant"),
        (
            loop_termination_implies_postcondition,
            "loop_termination_implies_postcondition"),
        (wrong_prop, "wrong_prop"),
        (wrong_prop2, "wrong_prop2"),
        # (~wrong_prop, "~wrong_prop"),
        # (~variant_is_strictly_decreasing, "Not variant_is_strictly_decreasing"),
        # (inv_prop_cond3, "inv_prop_cond3"),
        # (prop_cond3, "prop_cond3"),
        # (prop_cond3_2, "prop_cond3_2"),
        # (mypost, "mypost"),
        # (subprop, "subprop"),
    ]

    for algo in [PDR, IMC]:
        print(f"Using {algo.__name__}:")
        for prop, prop_name in properties:
            print(f"proving {prop_name}")
            print(algo(I, T, Predicate(prop)))

    # print("\nUsing finite_run:")
    # for prop, prop_name in properties:
    #     print(f"proving {prop_name}")
    #     print(finite_run(I, T, Predicate(prop), 3))


def prog4(m, n):
    """
    An attempt to codify the following piece of code:

    .. code-block::

        assume m >= 0 and n >= 0 and r == 0 and x == m and y == n
        0: while y > 0:
        1:    if y & 1 == 1:
                    y , r  = y-1 , r+x
        2:    x , y = x<<1  ,  y>>1
        3: assert r == m * n

    Executing it will print the value of pc and the variables at different points.
    The purpose of this function is to compare its output with traces provided by
    model checkers when returning counterexamples.
    """
    x = m
    y = n
    r = 0
    assert m >= 0 and n >= 0 and r == 0 and x == m and y == n

    s = lambda: '(' + ', '.join(
        [f"{k} = {v}" for k, v in
         {'r': r, 'x': x, 'y': y, 'm': m, 'n': n}.items()]) + ')'

    pc = 0
    print(f"[{pc=} V={y - pc + 3}] {s()}")
    while y > 0:
        pc += 1
        print(f"[{pc=} V={y - pc + 3}] start cycle: {s()}")
        if y & 1 == 1:
            y -= 1
            r += x
        pc += 1
        print(f"[{pc=} V={y - pc + 3}] after if: {s()}")
        x <<= 1
        y >>= 1
        pc = 0
        print(f"[{pc=} V={y - pc + 3}] {s()}")
    assert r == m * n
    print(f"[{pc=} V={y - pc + 3}] after cycle: {s()}")


if __name__ == "__main__":
    main()
