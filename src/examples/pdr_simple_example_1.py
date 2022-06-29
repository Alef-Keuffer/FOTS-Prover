if __name__ == '__main__':
    from pysmt.shortcuts import *
    from backend import PDR, IMC, BMCInduction, BMC_IND
    from predicate import Variable, Predicate

    """
    .. code-block

        x = 10
        while x > 1:
            x = x - 1

    example from p.7 of D. Beyer and M. Dangl, “Software Verification with PDR:
    Implementation and Empirical Evaluation of the State of the Art,” arXiv:1908.06271
    [cs], Feb. 2020, Accessed: Mar. 05, 2022. [Online]. Available:
    http://arxiv.org/abs/1908.06271 """

    x = Predicate(Variable('x', INT))
    I = Predicate(x[0].Equals(10))
    T = Predicate(x[1].Equals(2 * x[0] - 1))
    P_true = Predicate(x[0] > 0)

    # bmcind(I, T, P)
    print("Checking true property:")
    for algo in [BMC_IND, PDR, IMC]:
        print(f"Using {algo.__name__}:")
        algo(I, T, P_true)

    P_false = Predicate(x[0] < 0)
    print("Checking false property:")
    for algo in [BMC_IND, PDR, IMC]:
        algo(I, T, P_false)
