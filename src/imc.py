from backend import Status
from predicate import *

"""
Based on K. L. McMillan, “Interpolation and SAT-Based Model Checking,”. doi:
10.1007/978-3-540-45069-6_1.
"""


def bmc(k: int, j: int, I: Predicate, T: Predicate, F: Predicate):
    return I[0] & T[:k - 1] & Or(F[i] for i in range(j, k + 1))


def pref(l: int, I: Predicate, T: Predicate):
    return I[-l] & T[-l:-1]


def suff(k: int, j: int, T: Predicate, F: Predicate):
    return T[:k - 1] & Or(F[i] for i in range(j, k + 1))


def finite_run(I: Predicate, T: Predicate, P: Predicate, k: int):
    F = Predicate(~P[0])
    if is_sat(I[0] & F[0]):
        return Status.UNSAFE1
    R = I[0]
    while True:
        A = R & T[0]
        B = T[1:k - 1] & Or(F[l] for l in range(k + 1))
        if is_sat(A & B):
            if is_valid(EqualsOrIff(R, I[0])):
                return Status.UNSAFE2
            else:
                return Status.UNKNOWN
        else:
            P = Predicate(binary_interpolant(A, B))
            R_prime = P[0]
            if is_valid(R_prime.Implies(R)):
                return Status.SAFE
            R |= R_prime
