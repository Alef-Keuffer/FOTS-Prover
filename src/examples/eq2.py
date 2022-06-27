from pysmt.shortcuts import *

from backend import *

pc = Symbol("pc", INT)
x = Symbol("x", INT)
y = Symbol("y", INT)
z = Symbol("z", INT)
w = Symbol("w", INT)
r = Symbol("r", INT)
npc = next_var(pc)
nx = next_var(x)
ny = next_var(y)
nz = next_var(z)
nw = next_var(w)
nr = next_var(r)

d = {x: nx, y: ny, r: nr, pc: npc, w: nw, z: nz}
t = lambda s: And([d[v].Equals(v) for v in d if v not in s])

I = pc.Equals(0) & x.Equals(w) & y.Equals(w+1) & z.Equals(x+1)
t1 = pc.Equals(0) & npc.Equals(1) & t({pc})
t2 = pc.Equals(1) & npc.Equals(1) & ny.Equals(y + 1) & nz.Equals(z+1) & r.NotEquals(0) & t({pc})
t3 = pc.Equals(1) & npc.Equals(2) & r.Equals(0) & t({pc})
t4 = pc.Equals(2) & npc.Equals(2) & t({pc})
T = t1 | t2 | t3 | t4

prop1 = pc.Equals(2).Implies(y.Equals(z))

TS = TransitionSystem(I, T)

print(IMC(prop1, TS))

print(PDR(prop1, TS))
