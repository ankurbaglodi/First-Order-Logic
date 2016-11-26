import re
import copy
import pdb
import sys

counter = 0
visited_facts = list()


# Better check for is_variable
# RunTime Error -> return False
# Parse input text file

def extend(var, val, theta):
    _theta = theta.copy()
    _theta[var] = val
    return _theta


def unify_var(x, y, theta):
    if x in theta:
        return unify(theta[x], y, theta)
    elif y in theta:
        return unify(x, theta[y], theta)
    else:
        return extend(x, y, theta)


def is_list(x):
    return hasattr(x, '__len__')


def is_variable(x):
    return x == x.lower()


def unify(x, y, theta={}):
    # pdb.set_trace()
    # base case
    if theta == None:
        return None
    elif x == y:
        return theta

    elif isinstance(x, str) and is_variable(x):
        return unify_var(x, y, theta)
    elif isinstance(y, str) and is_variable(y):
        return unify_var(y, x, theta)
    elif isinstance(x, str) or isinstance(y, str) or not x or not y:
        return theta if x == y else None
    elif is_list(x) and is_list(y) and len(x) == len(y):
        return unify(x[1:], y[1:], unify(x[0], y[0], theta))
    else:
        return None


def subst_in_list(theta, x):
    _x = list(x)
    for var in theta:
        if var in x:
            indices = [i for (i, j) in enumerate(x) if j == var]
            for k in indices:
                _x[k] = theta[var]

    return _x


assert (unify(['x', 'y'], ['John', 'Bob'], {}) == {'x': 'John', 'y': 'Bob'})
assert (unify(['x', 'y'], ['John', 'Bob', 'Chris'], {}) == None)
assert (unify(['x', 'y', 'z'], ['John', 'Bob'], {}) == None)
assert (unify(['x', 'Bob'], ['John', 'Bob'], {}) == {'x': 'John'})
assert (unify(['John', 'y'], ['John', 'Bob'], {}) == {'y': 'Bob'})
assert (unify(['John', 'Bob'], ['John', 'Bob'], {}) == {})
assert (unify(['John', 'Chris'], ['John', 'Bob'], {}) == None)

assert (subst_in_list({'x': 'John', 'y': 'Bob'}, ['x', 'y']) == ['John', 'Bob'])
assert (subst_in_list({'x': 'John', 'y': 'Bob'}, ['x']) == ['John'])
assert (subst_in_list({'x': 'John', }, ['x', 'y']) == ['John', 'y'])


class Atomic():
    def __copy__(self):
        return Atomic(self.op, self.terms)

    def __hash__(self):
        return hash((self.op, tuple(self.terms)))

    def __eq__(self, other):
        return self.op == other.op and self.terms == other.terms

    def __init__(self, op, terms):
        self.op = op
        self.terms = terms


def is_negation(x):
    return '~' in x


def atomify(x):
    op = ''.join(re.findall(r'(\W?\w+)\(', x))
    terms = ''.join(re.findall(r'\(([\w+]|[\w+,\w+]*)\)', x)).split(',')
    return Atomic(op, terms)


assert (atomify('A(x,y)') == Atomic('A', ['x', 'y']))
assert (atomify('A(x)') == Atomic('A', ['x']))
assert (atomify('A(x,John)') == Atomic('A', ['x', 'John']))


def atomify_conjuncts(x):
    return [atomify(y) for y in x.split(' ^ ')] if x else []


def get_lhs(x):
    return x.split(" => ")[0] if "=>" in x else None


assert (atomify_conjuncts(get_lhs("A(x)")) == [])
assert (get_lhs("A(x) ^ B(x) => C(x)") == "A(x) ^ B(x)")
assert (get_lhs("A(x)") == None)


def get_rhs(x):
    return x.split(" => ")[-1]


assert (get_rhs("A(x) ^ B(x) => C(x)") == "C(x)")
assert (get_rhs("A(x)") == "A(x)")


def standardize(lhs, rhs, theta=None):
    global counter
    if theta is None: theta = {}
    args = []
    for x in lhs:
        for y in x.terms:
            args.append(y)

    args = args + rhs.terms
    # pdb.set_trace()

    for term in args:
        if is_variable(term):
            if term not in theta:
                # pdb.set_trace()
                counter = counter + 1
                theta[term] = "v_%d" % counter

    for x in lhs:
        x.terms = subst_in_list(theta, x.terms)
    rhs.terms = subst_in_list(theta, rhs.terms)

    return lhs, rhs


def is_fact(x):
    for i in x.terms:
        if is_variable(i):
            return False

    return True


assert (is_fact(Atomic('F', ['x', 'y'])) == False)
assert (is_fact(Atomic('F', ['x', 'v'])) == False)
assert (is_fact(Atomic('F', ['S', 'SS'])) == True)


def subst_in_predicate(theta, x):
    _x = copy.deepcopy(x)
    for var in theta:
        if var in x.terms:
            _x.terms[_x.terms.index(var)] = theta[var]

    return _x
def bc_or(KB, goal, visited_facts, theta={}):
        # pdb.set_trace()

        if not isinstance(goal, Atomic):
            goal = atomify(goal)
            visited_facts.append(goal)

        # pdb.set_trace()

        for rule in KB:
            # and_visited_facts = copy.deepcopy(visited_facts)

            lhs = atomify_conjuncts(get_lhs(rule))
            rhs = atomify(get_rhs(rule))

            # pdb.set_trace()
            if rhs.op == goal.op:
                if is_fact(rhs):
                    if rhs not in visited_facts:
                        visited_facts.append(rhs)
                else:
                    return

                lhs, rhs = standardize(lhs, rhs)
                # pdb.set_trace()
                for subst_in_and_subtree in  bc_and(KB, lhs, unify(rhs.terms, goal.terms, theta),
                           visited_facts):

                    yield subst_in_and_subtree

def bc_ask(KB, query):
    return bc_or(KB, query, [], {})

def read_logic_data(file_handle):
    no_of_queries = int(file_handle.readline().rstrip('\r\n'))
    queries = [str(file_handle.readline().rstrip('\r\n')) \
               for _ in xrange(no_of_queries)]
    no_of_facts = int(file_handle.readline().rstrip('\r\n'))
    KB = [str(file_handle.readline().rstrip('\r\n')) \
          for _ in xrange(no_of_facts)]

    return queries, KB


def bc_and(KB, goals, theta, and_visited_facts):
    # pdb.set_trace()
    if theta == None:
        return
    # if set(goals) & set(visited_facts):
    #     return
    elif len(goals) == 0:
        yield theta
    else:
        first, rest = goals[0], goals[1:]
        # pdb.set_trace()
        for subst_in_or_subtree in bc_or(KB, subst_in_predicate(theta, first),\
                  and_visited_facts, theta):
            for subst_in_and_subtree in bc_and(KB, rest, theta, and_visited_facts):
                yield subst_in_and_subtree

    def stringify(goal):
        csv = [str(term) + ',' for term in goal.terms]
        csv = ''.join(csv)
        csv = csv.rstrip(',')
        return str(goal.op) + '(' + csv + ')'

    assert (stringify(Atomic('A', ['Bob'])) == 'A(Bob)')
    assert (stringify(Atomic('A', ['Bob', 'Jack'])) == 'A(Bob,Jack)')


def main():
    global visited_facts
    global counter
    InputFileName = "input.txt"
    OutputFileName = "output.txt"
    input_file_handle = open(InputFileName, 'r')
    output_file_handle = open(OutputFileName, 'w')
    # output_file_handle = open('output.txt','w')
    queries, KB = read_logic_data(input_file_handle)

    for query in queries:
        try:
            result = "TRUE\n" if (len(list(bc_ask(KB, query))) > 0) \
                else "FALSE\n"
            print result
        except RuntimeError:
            # Hack to handle infinite loop in var names alone
            result = "FALSE\n",'Suraj'
        # result = "TRUE\n" if (len(list(bc_ask(KB, query))) > 0)\
        #          else "FALSE\n"
        output_file_handle.write(result)
        visited_facts = list()
        counter = 0

    output_file_handle.close()
    input_file_handle.close()

if __name__ == '__main__':
    main()

