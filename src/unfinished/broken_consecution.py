from pysmt.shortcuts import *
from pysmt.typing import *

def prime(v):
    """Returns the 'next' of the given variable"""
    return Symbol("prime(%s)" % v.symbol_name(), v.symbol_type())

def fresh(v):
    return FreshSymbol(typename=v.symbol_type(),template=v.symbol_name()+"_%d")


class PDR(object):

    def __init__(self , fots, solver = "z3"):
        self.fots = fots
        self.frames = [fots.init]
        self.solver = Solver(name = solver)


    def solve(self, formula):
        """
        Provides a satisfiable assignment to the state variables that are consistent with the input formula
        If formula F is valid, returns x_1≡v_1 ∧ ⋯ ∧ x_n≡v_n where x_i is a variable in F and F is true
        if each x_i takes value v_i.
        If the formula is not satisfiable, returns None.
        """
        if self.solver.solve([formula]):
            return And([EqualsOrIff(v, self.solver.get_value(v)) for v in self.system.variables])
        return None
 
    def getCTI(self,prop):
        return self.solve(And(self.frames[-1],Not(prop)))
    
    def lift(self,cti,prop):
        return binary_interpolant(cti,prop)
    
    def consecution(self,formula):
        new_formula = TRUE()
        variables = [self.solver.get_value(v) for v in formula]
        for var in range(len(variables)):
            for other_vars in range(var,len(variables)):
                new = GE(variables[var],variables[other_vars])
                if new:
                    new_formula = And(new_formula,Not(new))
                else:
                    new_formula = And(new_formula,new)

        return new_formula

    def recursive_block(self, cube):
        """Blocks the cube at each frame, if possible.

        Returns True if the cube cannot be blocked.
        """
        for i in range(len(self.frames)-1, 0, -1):
            cubeprime = cube.substitute(dict(zip(self.system.variables,self.system.prime_variables)))
            cubepre = self.solve(And(self.frames[i-1], self.system.trans, Not(cube), cubeprime))
            if cubepre is None:
                for j in range(1, i+1):
                    self.frames[j] = And(self.frames[j], Not(cube))
                return False
            cube = cubepre
        return True
        
    def inductive(self):
        """Checks if last two frames are equivalent """
        return len(self.frames) > 1 and is_valid(Not(EqualsOrIff(self.frames[-1], self.frames[-2])))
    
    def prove_property(self, prop):
        self.frames.append(prop)
        
        while True:
            # Blocking phase
            m = get_model(And(Not(prop),self.frames[-1]))
            if not m:
                print("not m")
        
            cti = And([EqualsOrIff(v, m.get_value(v)) for v in self.system.variables])
            lifted = self.lift(cti,prop)
            if lifted is not None:
                cube = self.consecution(lifted)
                if self.recursive_block(cube):
                    print("--> Bug found at step %d" % (len(self.frames)))
                    break
                else:
                    print("   [PDR] Cube blocked '%s'" % str(cube))
            # Propagation phase
            else:
                if self.inductive():
                    print("--> The system is safe!")
                    break
                else:
                    print("   [PDR] Adding frame %d..." % (len(self.frames)))
                    self.frames.append(TRUE())


            

            

"""
As by p. 5 of CTIGAR
consecution_query_s = get_model(Not((F_i & Not(s) & T).Implies(Not(next(s)))))
if consecution_query_s:
    # A CTI can be expressed in any theory as a conjunction of equations between state variables
    # and values.
    concrete_CTI_t = And([v.EqualsOrIff(m.get_value(v)) for v in TransitionSystem.variables()])

    t = concrete_CTI_t
    consecution_query_t = get_model(Not((F_i & Not(t) & T).Implies(Not(next(t)))))
    if consecution_query_t:
        concrete_CTI_s = And([v.EqualsOrIff(consecution_query_t.get_value(v)) for v in TransitionSystem.variables()])
        z = assignment to primary inputs of consecution_query_t
        lifting_query = get_model(Not(s & z & T & Not(next(t))))
        # lifting_query is not None by construction

        # Partial assignment can replace s
        reduced_partial_assignment = And([v.EqualsOrIff(lifting_query.get_value(v)) for v in TransitionSystem.variables()])

"""
    

