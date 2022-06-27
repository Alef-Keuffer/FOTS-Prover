from pysmt.fnode import FNode
from pysmt.shortcuts import *

from backend import Status


def itp(formulas):
    from pysmt.solvers.msat import MSatInterpolator
    class CustomMSatInterpolator(MSatInterpolator):
        def sequence_interpolant(self, formulas):
            cfg, env = None, None
            try:
                self._check_logic(formulas)

                if len(formulas) < 2:
                    from pysmt.exceptions import PysmtValueError
                    raise PysmtValueError("interpolation needs at least 2 formulae")

                import mathsat
                cfg = mathsat.msat_create_config()
                mathsat.msat_set_option(cfg, "interpolation", "true")
                from pysmt.logics import QF_BV
                from pysmt.logics import QF_AUFBVLIRA
                if self.logic in {QF_BV, QF_AUFBVLIRA}:
                    mathsat.msat_set_option(cfg, "theory.bv.eager", "false")
                    mathsat.msat_set_option(cfg, "theory.eq_propagaion", "false")
                env = mathsat.msat_create_env(cfg, self.msat_env())
                groups = []
                for f in formulas:
                    f = self.converter.convert(f)
                    g = mathsat.msat_create_itp_group(env)
                    mathsat.msat_set_itp_group(env, g)
                    groups.append(g)
                    mathsat.msat_assert_formula(env, f)

                res = mathsat.msat_solve(env)
                if res == mathsat.MSAT_UNKNOWN:
                    from pysmt.exceptions import InternalSolverError
                    raise InternalSolverError(
                        f"Error in mathsat interpolation: "
                        f"{mathsat.msat_last_error_message(env)}")

                if res == mathsat.MSAT_SAT:
                    return None

                pysmt_ret = []
                for i in range(1, len(groups)):
                    itp = mathsat.msat_get_interpolant(env, groups[:i])
                    f = self.converter.back(itp)
                    pysmt_ret.append(f)

                return pysmt_ret
            finally:
                if cfg:
                    mathsat.msat_destroy_config(cfg)
                if env:
                    mathsat.msat_destroy_env(env)

    from pysmt.oracles import get_logic
    return CustomMSatInterpolator(
        get_env(),
        logic=get_logic(And(formulas))
    ).sequence_interpolant(formulas)


def bin_itp(a, b):
    return itp([a, b])


def interpolate(A: FNode, B: FNode):
    with Solver() as sA, Solver() as sB:
        sA.add_assertion(A)
        sB.add_assertion(B)
        I = TRUE()
        while True:
            if not sB.solve():
                return Status.UNSAT, I
            if sA.is_sat():
                mA = sA.get_model()
                if mA.satisfies(B):
                    return Status.SAT, sA.get_model(), TRUE()
            else:
                pass


def interp(P: FNode, Q: FNode):
    # see Theorem 5 in https://www.cs.cmu.edu/~15414/f17/lectures/21-cegar.pdf
    if P.get_atoms().intersection(Q.get_atoms()):
        print(f"{P.get_atoms() = }")
        print(f"{Q.get_atoms() = }")
        return TRUE()
    D = P.get_atoms().difference(Q.get_atoms())
    if D == set():
        return P
    else:
        P_DT = P.substitute({d: TRUE() for d in D})
        P_DF = P.substitute({d: FALSE() for d in D})
        OR_P = P_DT | P_DF
        return interp(OR_P, Q).simplify()