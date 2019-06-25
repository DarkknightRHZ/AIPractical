"""
pl1_formula.py -- basic classes for representing single clauses of a PL1 formula
in clausal normal form for the unification exercise

Examples:

# Formula: for all x. for all y. for all z. P(x, c, f(y)) or P(x, z, z)
# or in set notation: {P(x, c, f(y)), P(x, z, z)}

P = PredicateSymbol("P", 3)
f = FunctionSymbol("f", 1)
x = Variable("x")
y = Variable("y")
z = Variable("z")
c = Constant("c")
formula = [P(x, c, f(y)), P(x, z, z)]

Useful functions:
Every Expression object e (variables, constants, function calls, e.g., f(y)
above, and predicate instantiations, e.g., P(x, z, z) above) supports the
following two functions:
    e.contains_variable(var_object) # returning True if e contains the given
                                    # variable object, and False otherwise
    e.apply_substitutions(s)        # returns a new expression object where the
                                    # given substitution object is applied

The following functions may become useful (with their obvious meaning),
the parameter exprs gives a list of expressions:
    get_variable(exprs) # returns None if exprs does not contain any Variable object
    expressions_to_string(exprs) 
    print_expressions(exprs)     

"""

import copy

class Expression(object):
    def __ne__(self, other):
        return not self.__eq__(other)
    def contains_variable(self, var):
        raise NotImplementedError("Expression base class does not provide a contains_variable implementation")
    def apply_substitutions(self, s):
        raise NotImplementedError("Expression base class does not provide an apply_substitutions implementation")

class Term(Expression):
    pass

class Variable(Term):
    def __init__(self, name):
        self.name = name
    def __eq__(self, other):
        return isinstance(other, Variable) and self.name == other.name
    def __repr__(self):
        return "Variable(%s)" % self.name
    def __str__(self):
        return self.name
    def __hash__(self):
        return hash(self.__repr__())
    def contains_variable(self, var):
        return self == var
    def apply_substitutions(self, s):
        if self in s:
            return copy.copy(s[self])
        return Variable(self.name)

class Constant(Term):
    def __init__(self, name):
        self.name = name
    def __eq__(self, other):
        return isinstance(other, Constant) and self.name == other.name
    def __str__(self):
        return self.name
    def __repr__(self):
        return "Constant(%s)" % self.name
    def __hash__(self):
        return hash(self.__repr__())
    def contains_variable(self, var):
        return False
    def apply_substitutions(self, s):
        return Constant(self.name)

class Function(Term):
    def __init__(self, symbol, terms):
        self.symbol = symbol
        self.terms = terms
        assert(all([isinstance(t, Term) for t in terms]))
        assert(len(self.terms) == self.symbol.arity)
    def __eq__(self, other):
        return isinstance(other, Function) and self.symbol == other.symbol and all([self.terms[i] == other.terms[i] for i in range(self.symbol.arity)])
    def __str__(self):
        return "%s(%s)" % (self.symbol, ", ".join([str(t) for t in self.terms]))
    def __repr__(self):
        return "Function(%r, %r)" % (self.symbol, self.terms)
    def __hash__(self):
        return hash(self.__repr__())
    def contains_variable(self, var):
        return any([t.contains_variable(var) for t in self.terms])
    def apply_substitutions(self, s):
        return Function(self.symbol, [t.apply_substitutions(s) for t in self.terms])

class Atom(Expression):
    def __init__(self, symbol, terms):
        self.symbol = symbol
        self.terms = terms
        assert(all([isinstance(t, Term) for t in terms]))
        assert(len(self.terms) == self.symbol.arity)
    def __eq__(self, other):
        return isinstance(other, Atom) and self.symbol == other.symbol and all([self.terms[i] == other.terms[i] for i in range(self.symbol.arity)])
    def __str__(self):
        return "%s(%s)" % (self.symbol.name, ", ".join([str(t) for t in self.terms]))
    def __repr__(self):
        return "Atom(%r, %r)" % (self.symbol, self.terms)
    def __hash__(self):
        return hash(self.__repr__())
    def contains_variable(self, var):
        return any([t.contains_variable(var) for t in self.terms])
    def apply_substitutions(self, s):
        return Atom(self.symbol, [ t.apply_substitutions(s) for t in self.terms ])

class FunctionSymbol(object):
    def __init__(self, name, arity):
        self.name = name
        self.arity = arity
    def __repr__(self):
        return "FunctionSymbol(%s, %d)" % (self.name, self.arity)
    def __eq__(self, other):
        return isinstance(other, FunctionSymbol) and self.name == other.name and self.arity == other.arity
    def __ne__(self, other):
        return not self.__eq__(other)
    def __str__(self):
        return self.name
    def __hash__(self):
        return hash(self.__repr__())
    def __call__(self, *args):
        assert(len(args) == self.arity)
        return Function(self, args)

class PredicateSymbol(object):
    def __init__(self, name, arity):
        self.name = name
        self.arity = arity
    def __repr__(self):
        return "PredicateSymbol(%s, %d)" % (self.name, self.arity)
    def __eq__(self, other):
        return isinstance(other, PredicateSymbol) and self.name == other.name and self.arity == other.arity
    def __ne__(self, other):
        return not self.__eq__(other)
    def __str__(self):
        return self.name
    def __hash__(self):
        return hash(self.__repr__())
    def __call__(self, *args):
        assert(len(args) == self.arity)
        return Atom(self, args)

def get_variable(expressions):
    for x in expressions:
        if isinstance(x, Variable):
            return x
    return None

def expressions_to_string(expressions):
    return ("{%s}" % ", ".join(str(e) for e in expressions))

def print_expressions(expressions):
    print (expressions_to_string(expressions))
