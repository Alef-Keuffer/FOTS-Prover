from pysmt.shortcuts import *

from backend import next_var, TransitionSystem, PDR, IMC

x = Symbol('x',INT)
nx = next_var(x)
I = x.Equals(2)
T = nx.Equals(2 * x - 1)
P = x > 0

TS = TransitionSystem(I, T)
PDR(P, TS)
IMC(P, TS)

P_false = x < 0
PDR(P_false, TS)
IMC(P_false, TS)

