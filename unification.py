
from pl1_formula import *

class Substitution(dict):
    """
    Representing a substitution set. The dictionary keys must be Variable
    objects. There are three ways of creating a Substitution objects:
        1) Substitution()      # Creates the empty set.
        2) Singleton(x, t)     # Creates a substitution containing the single 
                               # element {x/t}. x must be a Variable object, t
                               # can be an arbitrary term (i.e., Constant,
                               # Variable, or Function).
        3) Composition(s1, s2) # Creates the composed substitution s1s2. s1
                               # and s2 must both be Substitution objects.
    
    You can use Substitution objects pretty much the same as dictionaries. For
    example, given a Substitution object s, iterating over s can be done as
    follows:
        for var in s:
            term = s[var]
            # ... do something
    or directly via
        for (var, term) in s.iteritems():
            # ... do something ...
    To extend s by x2/t2, do
        s[x2] = t2
    To check whether s defines a substitution for x:
        if x in s:
            # ... do something
    To print s:
        print(s)
    """

    @staticmethod
    def Singleton(var, term):
        assert(isinstance(var, Variable))
        assert(isinstance(term, Variable) or isinstance(term, Constant) or isinstance(term, Function))
        s = Substitution()
        s[var] = term
        return s

    @staticmethod
    def Composition(s1, s2):
        assert(isinstance(s1, Substitution))
        assert(isinstance(s2, Substitution))
        comp = Substitution()

        for v in s1:
            tmp = s1[v]
            for k in s2:
                if(tmp.contains_variable(k)):
                    tmp = tmp.apply_substitutions(Substitution({k: s2[k]}))
            if(v != tmp):
                comp[v] = tmp

        for v in s2:
            if(s1.get(v) is None):
                comp[v] = s2[v]
            

        return comp

    def __str__(self):
        return "{%s}" % ", ".join(["%s/%s" % (var, self[var]) for var in self])


def compute_disagreement_set(atoms):
    """
    Compute the disagreement set for the provided set of atoms.

    Result must be a collection (list, set, etc) of term objects (Variable,
    Constant, Function).

    You can assume that all atoms are over the same predicate.
    """
    if len(atoms) <= 1:
        return []

    lF = len(atoms[0].terms)
    for i in range(1, len(atoms)):
        if(lF is not len(atoms[i].terms)):
            return []
    
    disc = -99999

    for i in range(lF):
        tmp = atoms[0].terms[i]
        if(disc != -99999):
            break
        if isinstance (tmp, Function):
            FunctionMatch = True
        else:
            FunctionMatch = None
        for j in range(1, len(atoms)):
            tmp2 = atoms[j].terms[i]
            if(tmp != tmp2):
                disc = i
            if(tmp != tmp2 and isinstance(tmp2, Function) and tmp.symbol == tmp2.symbol and isinstance(tmp, Function)):
                continue
            else:
                FunctionMatch = False
                break

    if disc == -99999:
        return []

    lst = [atom.terms[disc] if not FunctionMatch else atom.terms[disc].terms[0] for atom in atoms]
    return lst


def unification(atoms):
    """
    Runs the unification algorithm on the given set of atoms. If there exists
    a unifier for atoms, returns an idempotent mgu. Otherwise, returns None.
    """

    sub = Substitution()
    atm = atoms
    
    while len(set(atm)) > 1:
        dSet = compute_disagreement_set(atm)
        hasConsFunc = False
        for i in range(len(dSet)):
            itm1 = dSet[i]
            for j in range(i + 1, len(dSet)):
                itm2 = dSet[j]
                if  (isinstance(itm1, Constant) and isinstance(itm2, Constant)) or (isinstance(itm1, Function) and isinstance(itm2, Function)) or \
                    (isinstance(itm1, Function) and isinstance(itm2, Constant)) or (isinstance(itm2, Function) and isinstance(itm1, Constant)):
                    hasConsFunc = True

        if (not any([isinstance(itm1, Variable) for itm1 in dSet]) or hasConsFunc):
            return None

        sub2 = Substitution()

        itm1 = None
        for x in dSet:
            if isinstance(x, Variable):
                itm1 = x

        itm2 = None
        for x in dSet:
            if itm1 != x:
                itm2 = x

        if not (itm1 and itm2):
            return None

        if not itm2.contains_variable(itm1):
            sub2[itm1] = itm2
        else:
            return None

        sub = Substitution.Composition(sub, sub2)

        for i, atom in enumerate(atm):
            atm[i] = atom.apply_substitutions(sub2)

        atm = list(sorted(set(atm), key=atm.index))

    return sub



def run_disagreement_set_print_result(atoms):
    print("Clause: {%s}" % (", ".join([str(e) for e in atoms])))
    d = compute_disagreement_set(atoms)
    print("Disagreement set: {%s}" % (", ".join([str(e) for e in d])))
    print("")


def run_unification_print_result(atoms):
    print("Clause: {%s}" % (", ".join([str(e) for e in atoms])))
    s = unification(atoms)
    if s is None:
        print("Is not unifiable!")
    else:
        print("Unifier: %s" % s)
    print("")


if __name__ == "__main__":
    # Define predicate symbols, function symbols, as well as variables and
    # constants:
    P = PredicateSymbol("P", 3)
    f = FunctionSymbol("f", 1)
    g = FunctionSymbol("g", 1)
    v = Variable("v")
    w = Variable("w")
    x = Variable("x")
    y = Variable("y")
    z = Variable("z")
    a = Constant("a")
    b = Constant("b")
    c = Constant("c")


    # Disagreement set
    # Examples of slide 25 of chapter 8
    run_disagreement_set_print_result([P(x, c, f(y)), P(x, z, z)])
    run_disagreement_set_print_result([P(x, a, f(y)), P(y, a, f(y))])
    run_disagreement_set_print_result([P(v, f(z), g(w)), P(v, f(z), g(f(z)))])
    run_disagreement_set_print_result([P(v, f(z), g(w)), P(v, f(z), g(f(z))), P(v, f(z), f(x))])

   
    # # Unification
    # # Example of slide 27 of chapter 8
    run_unification_print_result([P(x, f(y), y), P(z, f(b), b)])
    # run_unification_print_result([P(x, f(y), b), P(z, f(w), c)])
    # run_unification_print_result([P(v, f(z), g(w)), P(v, f(z), g(f(z)))])
    # run_unification_print_result([P(a, f(y), b), P(b, f(w), c)])
    # run_unification_print_result([P(f(y),a, z), P(g(w), x, c)])
    # run_unification_print_result([P(f(x),a, z), P(x, y, c)])

