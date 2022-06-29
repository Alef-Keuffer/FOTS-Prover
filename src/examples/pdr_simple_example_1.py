if __name__ == '__main__':
    from pysmt.shortcuts import *
    from backend import PDR, IMC
    from predicate import Variable, Predicate

    """
    .. code-block

        x = 2
        while True:
            x = x + 1

    example from p.7 of D. Beyer and M. Dangl, “Software Verification with PDR:
    Implementation and Empirical Evaluation of the State of the Art,” arXiv:1908.06271
    [cs], Feb. 2020, Accessed: Mar. 05, 2022. [Online]. Available:
    http://arxiv.org/abs/1908.06271 """

    x = Predicate(Variable('x', INT))
    I = Predicate(x[0].Equals(2))
    T = Predicate(x[1].Equals(2 * x[0] - 1))
    P = Predicate(x[0] > 0)

    PDR(P, I, T)
    IMC(P, I, T)

    P_false = Predicate(x[0] < 0)
    PDR(P_false, I, T)
    IMC(P_false, I, T)
