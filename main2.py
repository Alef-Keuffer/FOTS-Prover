from pysmt.shortcuts import *
from pysmt.typing import *

from main import FirstOrderTransitionSystem, KInduction_FOTS

word_len = 16

BV16 = BVType(word_len)


def bitVecIntComp(vec, i, bin_op, size=word_len):
    intVec = BV(i, size)
    if i == 0:
        intVec = BVZero(size)
    elif i == 1:
        intVec = BVOne(size)
    if bin_op == "EQ":
        return Equals(vec, intVec)
    elif bin_op == "NEQ":
        return Equals(vec, intVec)
    elif bin_op == "GT":
        return BVUGT(vec, intVec)
    elif bin_op == "GE":
        return BVUGE(vec, intVec)
    elif bin_op == "LT":
        return BVULT(vec, intVec)
    elif bin_op == "LE":
        return BVULE(vec, intVec)
    raise ValueError("Wrong operator supplied to helper function bitVecIntComp!")


def init(state):
    l = []

    l.append(bitVecIntComp(state['m'], 0, "GE"))
    l.append(bitVecIntComp(state['n'], 0, "GE"))
    l.append(bitVecIntComp(state['r'], 0, "EQ"))
    l.append(Equals(state['x'], state['m']))
    l.append(Equals(state['y'], state['n']))
    l.append(Equals(state['pc'], Int(0)))

    return And(l)


def trans(curr, prox):
    l = []

    state1 = [Equals(curr['pc'], Int(0)),
              bitVecIntComp(curr['y'], 0, "GT"),
              Equals(prox['y'], curr['y']),
              Equals(prox['m'], curr['m']),
              Equals(prox['r'], curr['r']),
              Equals(prox['x'], curr['x']),
              Equals(prox['n'], curr['n']),
              Equals(prox['pc'], Int(1))]
    l.append(And(state1))

    state2 = [Equals(curr['pc'], Int(0)),
              bitVecIntComp(curr['y'], 0, "LE"),
              Equals(prox['y'], curr['y']),
              Equals(prox['m'], curr['m']),
              Equals(prox['r'], curr['r']),
              Equals(prox['x'], curr['x']),
              Equals(prox['n'], curr['n']),
              Equals(prox['pc'], Int(3))]
    l.append(And(state2))

    state3 = [Equals(curr['pc'], Int(1)),
              Equals(BVAnd(curr['y'], BVOne(word_len)), BVOne(word_len)),
              Equals(prox['y'], BVSub(curr['y'], BVOne(word_len))),
              Equals(prox['r'], BVAdd(curr['r'], curr['x'])),
              Equals(prox['x'], curr['x']),
              Equals(prox['m'], curr['m']),
              Equals(prox['n'], curr['n']),
              Equals(prox['pc'], Int(2))]
    l.append(And(state3))

    state4 = [Equals(curr['pc'], Int(1)),
              NotEquals(BVAnd(curr['y'], BVOne(word_len)), BVOne(word_len)),
              Equals(prox['y'], curr['y']),
              Equals(prox['r'], curr['r']),
              Equals(prox['x'], curr['x']),
              Equals(prox['m'], curr['m']),
              Equals(prox['n'], curr['n']),
              Equals(prox['pc'], Int(2))]
    l.append(And(state4))

    state5 = [Equals(curr['pc'], Int(2)),
              Equals(prox['x'], BVLShl(curr['x'], BVOne(word_len))),
              Equals(prox['y'], BVLShr(curr['y'], BVOne(word_len))),
              Equals(prox['m'], curr['m']),
              Equals(prox['n'], curr['n']),
              Equals(prox['r'], curr['r']),
              Equals(prox['pc'], Int(0))]
    l.append(And(state5))

    state6 = [Equals(curr['pc'], Int(3)),
              Equals(prox['y'], curr['y']),
              Equals(prox['m'], curr['m']),
              Equals(prox['r'], curr['r']),
              Equals(prox['x'], curr['x']),
              Equals(prox['n'], curr['n']),
              Equals(prox['pc'], Int(3))]
    l.append(And(state6))

    return Or(l)


state = {}
state['x'] = Symbol('x', BV16)
state['y'] = Symbol('y', BV16)
state['r'] = Symbol('r', BV16)
state['m'] = Symbol('m', BV16)
state['n'] = Symbol('n', BV16)
state['pc'] = Symbol('pc', INT)

fots = FirstOrderTransitionSystem(
    [
        state['x'],
        state['y'],
        state['r'],
        state['m'],
        state['n'],
        state['pc']
    ], init(state), trans)


def variante(state):
    return Plus(Minus(BVToNatural(state['y']), state['pc']), Int(3))


def positivo(state):
    prop = GE(variante(state), Int(0))
    return prop


fots_k_ind = KInduction_FOTS(fots)

fots_k_ind.k_induction_always(positivo, 3, "QF_BV")
