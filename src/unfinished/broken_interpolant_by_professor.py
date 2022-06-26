from pysmt.shortcuts import *
from pysmt.typing import *

"""
Codigo do professor
"""


# Auxiliares

def prime(v):
    return Symbol("prime(%s)" % v.symbol_name(), v.symbol_type())


def fresh(v):
    return FreshSymbol(typename=v.symbol_type(), template=v.symbol_name() + "_%d")


def Sub(formula, vs, us):
    return formula.substitute(dict(zip(vs, us)))


def Eq(vs, us):
    return And([EqualsOrIff(a, b) for (a, b) in zip(vs, us)])


class Bug(Exception):
    pass


# Weak Precondition Model

def Skip():
    return lambda phi: phi


def Assert(beta, wp=True):
    return Assume(beta, not wp)


def Assume(alpha, wp=True):
    if wp:
        return lambda phi: Implies(alpha, phi)
    else:
        return lambda phi: alpha


def Atrib(Vars, Exps, wp=True):
    if wp:
        return lambda phi: Sub(phi, Vars, Exps)
    else:
        freshs = [fresh(v) for v in Vars]
        Exps_ = [Sub(e, Vars, freshs) for e in Exps]
        #        return lambda phi: Exists(freshs, And(Eq(Vars, Exps_), Sub(phi, Vars, 
        #        freshs)))
        return lambda phi: And(Eq(Vars, Exps_), Sub(phi, Vars, freshs))


def Choice(*comds, wp=True):
    if wp:
        return lambda phi: And([cmd(phi) for cmd in comds])
    else:
        return lambda phi: Or([cmd(phi) for cmd in comds])


def IfThenElse(cond, true_cmd, false_cmd, wp=True):
    if wp:
        return lambda phi: Ite(cond, true_cmd(phi), false_cmd(phi))
    else:
        return lambda phi: Or(true_cmd(And(phi, cond)), false_cmd(And(phi, Not(cond))))


def Compose(*cmds, wp=True):
    if len(cmds) == 0:
        return Skip()
    else:
        cmd, *cmds = cmds
        if wp:
            return lambda phi: cmd(Compose(*cmds)(phi))
        else:
            return lambda phi: Compose(*cmds, wp=False)(cmd(phi))


class EPU(object):
    """violação da segurança"""

    def __init__(self, variables, init, error, WP=None, SP=None, T=None):

        self.vars = variables
        self.WP = WP
        self.SP = SP
        self.T = T

        self.init = init
        self.error = error

        self.solver = Solver("z3")

    def eq_sat(self, As, Bs):
        return self.solver.solve(As) == self.solver.solve(Bs)

    def is_consistent(self, spec, wp=True):

        this, other = spec

        try:
            primes = [prime(v) for v in self.vars]
            if self.T and self.WP and wp:
                As = [this, Not(self.WP(other))]
                Bs = [this, self.T, Sub(other, self.vars, primes)]
                if self.eq_sat(As, Bs):
                    print("transition relation is WP consistent for %s " % str(
                        this) + "," + str(other))
                    return True
                else:
                    raise Bug("transition relation is WP  inconsistent for %s " % str(
                        this) + "," + str(other))
            elif self.T and self.SP and not wp:
                As = [self.SP(this), other]
                Bs = [this, self.T, Sub(other, self.vars, primes)]
                if not self.eq_sat(As, Bs):
                    raise Bug("transition relation is SP inconsistent for %s " % str(
                        this) + "," + str(other))
                else:
                    print("transition relation is SP consistent for %s " % str(
                        this) + "," + str(other))
                    return True
            else:
                raise Bug("transition relation or trans former is not defined")
        except Bug as inst:
            print(inst)
            return False

    def is_inductive(self, prop, aux=None, wp=True):
        if aux is None:
            aux = TRUE()
        if wp and self.WP:
            return not self.solver.solve([aux, prop, Not(self.WP(prop))])
        elif (not wp) and self.SP:
            return not self.solver.solve([aux, self.SP(prop), Not(prop)])
        else:
            raise Bug("transformer missing")

    def unroll(self, limit=20):
        errors = [self.init, self.error];
        k = 0
        while k < limit:
            if self.solver.solve(errors):
                bug = self.solver.get_model()
                raise Bug(str(bug), k)
            else:
                U = errors[-1]
                errors.append(self.WP(U))
                k = k + 1
        print("iteration %d: no error states found " % k)
        return True

    def unroll_verify(self, size=20):
        try:
            self.unroll(size)
            return True
        except Bug as inst:
            bug, k = inst.args
            print("iteration %d: error state %s" % (k, bug))
            return False

    #        except Exception as inst:
    #            print(inst)
    #            return False

    def interpolant_verify(self, limit=10):
        U = self.error
        k = 0
        while k < limit:
            S = self.init
            while not self.solver.solve([S, U]):
                C = binary_interpolant(S, U)
                if self.is_inductive(C, aux=U):
                    return True
                S = C
            print('Using WP')
            U = self.WP(U)
        return False

    def interpolant_verify_notebook(self, limit=10):
        U = self.error
        k = 0
        while k < limit:
            S = self.init
            while not self.solver.solve([S, U]):
                if not (C := binary_interpolant(S, U)):
                    return False
                # verify if interpolant exists
                if self.is_inductive(C, aux=U):
                    break
                S = self.SP(C)
            print('Using WP and SP')
            U = self.WP(U)
        return False


# constantes auxiliares
bits = 8
L = 2 ** (bits // 2) - 1
N = BV(L, width=bits)
zero = BV(0, width=bits)
um = BV(1, width=bits)
dois = BV(2, width=bits)

# m    = BV(randint(1,L), width=bits)
# n    = BV(randint(1,L), width=bits)

# variáveis
x = Symbol("x", BVType(bits))
m = Symbol("m", BVType(bits))
n = Symbol("n", BVType(bits))
y = Symbol("y", BVType(bits))
r = Symbol("r", BVType(bits))

variables = [x, m, n, y, r]

# Conditions

init = And([BVUGT(m, zero),  # m > 0
            BVUGT(n, zero),  # n > 0
            Equals(r, zero),  # r = 0
            Equals(x, m),  # x = m
            Equals(y, n),  # y = n
            BVULE(m, N),  # m <= N
            BVULE(n, N)])  # n <= N

post = Equals(r, m * n)  # r = m * n

cond = y > 0  # y > 0

flag = Equals(y & um, um)  # (y & 1) == 1
# Trans

fixed = [m, n]

left = And(Equals(prime(y), BVLShr(BVSub(y, um), um)),  # y' = (y-1) >> 1
           Equals(prime(r), BVAdd(r, x)),  # r' = r + x
           Equals(prime(x), BVLShl(x, um)))  # x' = x << 1

right = And(Equals(prime(y), BVLShr(y, um)),  # y' = y >> 1
            Equals(prime(x), BVLShl(x, um)),  # x' = x << 1
            Equals(prime(r), r))  # r' = r             

body = Ite(Equals(BVAnd(y, um), um), left, right)  # if (y & 1 == 1) then left else right

fix_vars = And([Equals(prime(v), v) for v in fixed])


def main():
    # O SFOTS

    trans = And(cond, body, fix_vars)

    # Weakest PreCondition

    leftWP = Atrib([y, r, x], [BVLShr(BVSub(y, um), um), BVAdd(r, x), BVLShl(x, um)])
    # (y' , r' , x') = ((y - 1) >> 1 , r + x , x << 1)

    rightWP = Atrib([y, x], [BVLShr(y, um), BVLShl(x, um)])
    # (y' , x') = (y >> 1 , x << 1)

    bodyWP = IfThenElse(flag, leftWP, rightWP)

    WP = Compose(Assume(cond), bodyWP)
    # Strongest PosCondition

    leftSP = Atrib([y, r, x], [BVLShr(BVSub(y, um), um), BVAdd(r, x), BVLShl(x, um)],
                   wp=False)

    rightSP = Atrib([y, x], [BVLShr(y, um), BVLShl(x, um)], wp=False)

    bodySP = IfThenElse(flag, leftWP, rightWP, wp=False)

    SP = Compose(Assume(cond), bodySP, wp=False)
    # %%
    errors = [# Not(cond) & Not(post),
        # Not(cond) & post,
        # post,
        # Not(post), # reachable (loops)
        cond,  # reachable (loop)
        Not(cond), ]

    for error in errors:
        S = EPU(variables, init, error, WP, SP)
        #    S.unroll_verify(10)
        # print(S.interpolant_verify())
        print(S.interpolant_verify_notebook())


# S = EPU(variables, init, error, WP=WP, SP=SP, T=trans)
# S.is_consistent(init,wp=False)
# S.is_inductive(BVUGE(y,zero), wp=False)

# teste simples
def simple_test():
    init = Equals(x, N)
    error = Equals(x, zero)
    trans = Equals(prime(x), x - um)

    W = Atrib([x], [x - um])
    S = Atrib([x], [x - um], wp=False)

    Sys = EPU(variables, init, error, WP=W, SP=S, T=trans)
    # %%
    A = W(error)
    print(A)
    # %%
    B = S(init)
    print(B)
    # %%
    Sys.is_consistent((init, error), wp=False)
    # %%
    Sys.interpolant_verify(limit=10)


if __name__ == '__main__':
    main()
