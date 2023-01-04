import pdb
from copy import deepcopy

def power_set(A):
    """A is an iterable (list, tuple, set, str, etc)
    returns a set which is the power set of A."""
    length = len(A)
    l = [a for a in A]
    ps = set()

    for i in range(2 ** length):
        selector = f'{i:0{length}b}'
        subset = {l[j] for j, bit in enumerate(selector) if bit == '1'}
        ps.add(frozenset(subset))

    return ps

def closure_superset(S):
    closure = set()
    for s in S:
        if not any( t < s for t in S ):
            closure.add(s)
    return closure

def closure_subset(S):
    closure = set()
    for s in S:
        if not any( t > s for t in S ):
            closure.add(s)
    return closure

def closure_bool(S, W : set):
    closure = S.copy()
    for s in S:
        if W.difference(s) in closure and s in closure:
                closure.remove(W.difference(s))
        for t in S:
            if not (t <= s or t >= s):
                if s.union(t) in closure:
                    closure.remove(s.union(t))
                if s.intersection(t) in closure:
                    closure.remove(s.intersection(t))
    return closure

def disjoint_union(A : set, B : set):
    if not A&B: return A | B
    return {(a,0) for a in A} | {(b,1) for b in B}

def surjective(d : dict, codomain : set):
    return all( any( d[x] == y for x in d.keys() ) for y in codomain)

def injective(d : dict):
    return all( x1 == x2 or d[x1] != d[x2] for x1 in d.keys() for x2 in d.keys())

def bijective(d : dict, codomain):
    return injective(d) and surjective(d, codomain)

def functions_between(domain : set, codomain : set):
    if not codomain and domain: return [] # no function
    if not domain: return [dict()] # others empty cases -> only empty function
    functions_tree = [[dict()]]
    for x in domain:
        functions_tree += [[]]
        for f in functions_tree[-2]:
            for y in codomain:
                f2 = deepcopy(f)
                f2[x] = y
                functions_tree[-1] += [f2]
    return functions_tree[-1]

