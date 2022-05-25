from pysmt.fnode import FNode


def T_v1(s: FNode = None, ns: FNode = None, variables=None, __vars={}):
    if variables:
        def is_next(v: FNode):
            name = v.symbol_name()
            return 'next(' == name[:5] and ')' == name[-1]

        def prev_name(v: FNode):
            assert is_next(v)
            name = v.symbol_name()
            return name[5:][:-1]

        __vars.update({v: nv
                       for v in variables
                       for nv in variables
                       if is_next(nv) and v.symbol_name() == prev_name(nv)})
    if not __vars:
        print("Transition function without variables")
        exit(1)

    if s is None and ns is None:
        return

    formula = s

    updatedVariables = set()
    if ns is not None:
        formula &= ns
        updatedVariables = ns.get_free_variables()

    from pysmt.shortcuts import And
    formula &= And(__vars[v].Equals(v) for v in __vars if v not in updatedVariables)

    return formula
