from ast import Eq
from pysmt.shortcuts import *
from pysmt.typing import *

from main import FirstOrderTransitionSystem, KInduction_FOTS, next_var

word_len = 16

BV16 = BVType(word_len)

# constantes auxiliares
L = 2**word_len - 1
N    = BV(L,width=word_len)
zero = BV(0,width=word_len)
um   = BV(1,width=word_len)
dois = BV(2,width=word_len)

# Variáveis
x  = Symbol("x",BVType(word_len))
m  = Symbol("m",BVType(word_len))
n  = Symbol("n",BVType(word_len))
y  = Symbol("y",BVType(word_len))
r  = Symbol("r",BVType(word_len))
pc = Symbol("pc", INT)

variables = [x,m,n,r,y]

pre  =  And([BVUGT(m,zero),  # m > 0
             BVUGT(n,zero),  # n > 0
             Equals(r,zero), # r = 0
             Equals(x,m),    # x = m
             Equals(y,n),    # y = n
             BVULT(m,N),     # m < N
             BVULT(n,N),
             Equals(pc, Int(0))])    # n < N

while_check   =  And(BVUGT(y , zero), Equals(pc, Int(0)))      # y > 0, pc == 0

pc1      =  And(Equals(next_var(y), BVSub(y, um)),     # y = y-1
                Equals(next_var(r), BVAdd(r, x)),       # r = r + x
                Equals(next_var(x), BVLShl(x, um)),     # x = x << 1
                Equals(next_var(pc), Int(2)))

pc2     =  And(Equals(next_var(next_var(y)), BVLShr(next_var(y), um)),
               Equals(next_var(next_var(x)), BVLShl(next_var(x), um)),
               Equals(next_var(next_var(pc)), Int(0)))

pc2_     =  And(Equals(next_var(y), BVLShr(y, um)),
               Equals(next_var(x), BVLShl(x, um)),
               Equals(next_var(pc), Int(2)))

skip = And([EqualsOrIff(v,next_var(v)) for v in variables])

body  = Ite(And(Equals(pc, Int(1)), Equals(BVAnd(y, um), um)), And(pc1, pc2), skip)               # if (y & 1 == 1) then left else right

end = And([EqualsOrIff(v,next_var(v)) for v in variables], Equals(pc, Int(3)))

trans  = Ite(while_check, body, end)

variante =  Plus(Minus(BVToNatural(y), pc), Int(3))
positivo = GE(variante, Int(0))

fots = FirstOrderTransitionSystem(variables, pre, trans)


fots_k_ind = KInduction_FOTS(fots)

fots_k_ind.k_induction_always(positivo, 3, "QF_BV")
