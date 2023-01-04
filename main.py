import pdb
from copy import deepcopy
from tools import *

class CartesianFrame:
    def __init__(self, agent : set, environment : set, world : set, dot : dict = {}):
        self.agent = deepcopy(agent)
        self.env = deepcopy(environment)
        self.world = deepcopy(world)
        self.dot = deepcopy(dot)
        for a in self.agent:
            for e in self.env:
                if not (a,e) in self.dot.keys(): self.dot[(a,e)] = (a,e)
        assert all( w in self.world for w in self.dot.values() )
        if self.image(): # if self has no empty Agent/Environment
            self.indent = max(len(str(a)) for a in self.agent) + 2
            self.D = self._prerepr()
    def __call__(self, a, e):
        assert a in self.agent
        assert e in self.env
        return self.dot[(a,e)]
    def image(self):
        return {self(a,e) for a in self.agent for e in self.env}
    def _prerepr(self):
        step = max ( max(len(str(e)) for e in self.env), max(len(str(w)) for w in self.world) ) + 1
        D_a = dict()
        D_e = dict()
        D_w = dict()
        for a in self.agent:
            D_a[a] = str(a) + ' '*(self.indent  - len(str(a)))
        for e in self.env:
            D_e[e] = str(e) + ' '*(step  - len(str(e)))
        for w in self.world:
            D_w[w] = str(w) + ' '*(step  - len(str(w)))
        return [D_a, D_e, D_w]
    def __repr__(self):
        if self != ~self: 
            print('Bixtensional reduction:')
            print(~self)
            print('Not reduced:')
        if not self.image(): # if self has empty Agent or Environment
            if not self.agent and not self.env: return('null')
            if len(self.env) == 1: return('0')
            if len(self.agent) == 1: return('T')
            if not self.agent: return ' '.join([str(e) for e in self.env])
            if not self.env: return '\n'.join([str(a) for a in self.agent])

        if len(self.agent) == 1:
            print('1')
        if len(self.env) == 1:
            print('⊥')

        first_line = ' '*(self.indent) + ''.join([self.D[1][e] for e in self.env])
        lines = [first_line]
        for a in self.agent:
            line = self.D[0][a]
            for e in self.env:
                line += self.D[2][self(a,e)]
            lines += [line]
        return '\n'.join(lines)
    def ensurable(self, S : set):
        assert S.issubset(self.world)
        return any( all(self(a,e) in S for e in self.env) for a in self.agent )
    def preventable(self, S : set):
        assert S.issubset(self.world)
        return any( all(self(a,e) not in S for e in self.env) for a in self.agent )
    def ensure(self):
        ens = set()
        for S in power_set(self.world):
            if self.ensurable(S):
                ens.add(S)
        return ens
    def prevent(self):
        ens = set()
        for S in power_set(self.world):
            if self.preventable(S):
                ens.add(S)
        return ens
    def controllable(self, S : set):
        assert S.issubset(self.world)
        return self.ensurable(S) and self.preventable(S)
    def control(self):
        return self.ensure().intersection(self.prevent())
    def conditional_policies(self, S, a0, a1):
        assert S.issubset(self.world)
        assert a0 in self.agent
        assert a1 in self.agent
        cond = set()
        for a in self.agent:
            if all ( self(a,e) == (self(a0,e) if self(a,e) in S else self(a1,e)) for e in self.env ):
                cond.add(a)
        return cond
    def observable(self, S : set):
        assert S.issubset(self.world)
        return all (self.conditional_policies(S, a0, a1) for a0 in self.agent for a1 in self.agent)
    def observe(self):
        ens = set()
        for S in power_set(self.world):
            if self.observable(S):
                ens.add(S)
        return ens
    def morphisms_to(self, D):
        assert self.world == D.world

        if not self.image() or not D.image(): # empty cases
            return [ (g,h) for g in functions_between(self.agent, D.agent) for h in functions_between(D.env, self.env) ]

        possibilities = dict()
        for a in self.agent:
            for f in D.env:
                possibilities[(a,f)] = []
                for e in self.env:
                    for b in D.agent:
                        if self(a,e) == D(b,f):
                            possibilities[(a,f)] += [(b,e)]
                if possibilities[(a,f)] == []: return []
        morphisms_tree = [ [(dict(), dict())] ] # initialization for non-empty hom(self, D)
        for a in self.agent:
            for f in D.env:
                morphisms_tree += [[]] # new layer of the tree
                for m in morphisms_tree[-2]: # previous layer of the tree
                    constraint = [a in m[0].keys() , f in m[1].keys()]
                    for p in possibilities[(a,f)]:
                        g = deepcopy(m[0])
                        h = deepcopy(m[1])
                        if not constraint[0] and not constraint[1]: # no constraint
                            g[a] = p[0] # b
                            h[f] = p[1] # e
                            morphisms_tree[-1] += [(g,h)]
                        if all(constraint) and g[a] == p[0] and h[f] == p[1]:
                            morphisms_tree[-1] += [(g,h)]
                        if constraint[0] and not constraint[1] and g[a] == p[0]: # compatibility with g[a] previous constraint
                            h[f] = p[1] # e
                            morphisms_tree[-1] += [(g,h)]
                        if not constraint[0] and constraint[1] and h[f] == p[1]: # compatibility with h[f] previous constraint
                            g[a] = p[0] # b
                            morphisms_tree[-1] += [(g,h)]
        
                if not all( m1 is m2 or m1 != m2 for m1 in morphisms_tree[-1] for m2 in morphisms_tree[-1]):
                    pdb.set_trace()
        #pdb.set_trace()
        return morphisms_tree[-1]
    def isomorphisms_to(self, D):
        isomorphisms = []
        for m in self.morphisms_to(D):
            g = deepcopy(m[0])
            h = deepcopy(m[1])
            if bijective(g, D.agent) and bijective(h, self.env):
                isomorphisms += [m]
        return isomorphisms
    def __eq__(self, D):
        return bool(self.isomorphisms_to(D))
    def dual(self):
        return CartesianFrame(self.env, self.agent, self.world, {(e,a) : self(a,e) for a in self.agent for e in self.env})
    def __add__(self, D):
        assert self.world == D.world
        A = disjoint_union(self.agent, D.agent)
        E = {(e1,e2) for e1 in self.env for e2 in D.env}
        if self.agent&D.agent:
            dot = {(a,(e1,e2)) : D(a[0],e2) if a[1] else self(a[0],e1) for a in A for e1 in self.env for e2 in D.env} # using the boolean label of the disjoint_union
        else:
            dot = {(a,(e1,e2)) : self(a,e1) if a in self.agent else D(a,e2) for a in A for e1 in self.env for e2 in D.env}
        return CartesianFrame(A, E, self.world, dot)
    def __and__(self, D): # product
        assert self.world == D.world
        return (self.dual() + D.dual()).dual()
    def __invert__(self): # biextensional reduction
        agent = list(self.agent)
        env = list(self.env)
        A = []
        for a in agent:
            line = [self(a,e) for e in env]
            if all(line != [self(a0,e) for e in env] for a0 in A):
                A += [a]
        E = []
        for e in env:
            column = [self(a,e) for a in agent]
            if all(column != [self(a,e0) for a in agent] for e0 in E):
                E += [e]
        return CartesianFrame(set(A), set(E), self.world, {(a,e) : self(a,e) for a in A for e in E})
    def __mod__(self, D): # biextensional equivalence
        return ~self == ~D
    def __le__(self, D): # subagency relationship (covering definition)
        CtoD = self.morphisms_to(D)
        return all( any(e == m[1][f] for f in D.env for m in CtoD) for e in self.env )
    def mutual_subagency(self, D):
        return self <= D and D <= self
    def __mul__(self, D): # tensor product
        A = {(a1,a2) for a1 in self.agent for a2 in D.agent }
        E = self.morphisms_to(D.dual())
        dot = {(a,str(e)) : self(a[0],e[1][a[1]]) for a in A for e in E} # this a is the mathematical (a,b); this e is the (g,h) one; e[1] is h; hence ((a,b),(g,h)) : a.h(b)
        E = {str(e) for e in E } # making hashable for set
        return CartesianFrame(A, E, self.world, dot)
    def par(self, D): # ⅋ product
        return (self.dual() * D.dual()).dual()
    def __sub__(self, D): # lollipop
        A = self.morphisms_to(D)
        E = {(a,f) for a in self.agent for f in D.env }
        dot = {(str(a),e) : self(e[0],a[1][e[1]]) for a in A for e in E} # this a is (g,h); this e is the mathematical (a,f); e[1] is f; hence ((g,h),(a,f)) : a.h(f)
        A = {str(a) for a in A } # making hashable for set
        return CartesianFrame(A, E, self.world, dot)
    def __contains__(self, D):
        return self <= D and D.dual() <= self.dual()

def ensure(C : CartesianFrame, closure = True):
    print('\n')
    to_show = C.ensure()
    if closure:
        to_show = closure_superset(to_show)
        print("(Closed under supersets)")
    for S in to_show:
        print(set(S))

def prevent(C : CartesianFrame, closure = True):
    print('\n')
    to_show = C.prevent()
    if closure:
        to_show = closure_subset(to_show)
        print("(Closed under subsets)")
    for S in to_show:
        print(set(S))

def control(C : CartesianFrame):
    print('\n')
    for S in C.control():
        print(set(S))

def observe(C : CartesianFrame, closure = True):
    print('\n')
    to_show = C.observe()
    if closure:
        to_show = closure_bool(to_show, C.world)
        print("(Closed under boolean operations)")
    for S in to_show:
        print(set(S))


A = {'umbrella', 'no'}
E = {'rain', 'sun'}
W = {(a,e) for a in A for e in E}
D = CartesianFrame(A, E, W)
A2 = {'umbrella2', 'no2'}
E2 = {'rain2', 'sun2'}
d2 = {(a,e) : (a[0:-1],e[0:-1]) for a in A2 for e in E2}
D2 = CartesianFrame(A2, E2, W, d2)
A3 = deepcopy(A)
A3.add('umbrella3')
d3 = {(a,e) : ('umbrella',e) if a == 'umbrella3' else (a,e) for a in A3 for e in E}
D3 = CartesianFrame(A3, E, W, d3)
A.add('u~r')
A.add('u~s')
d = dict()
d[('u~r', 'rain')] = ('umbrella', 'rain')
d[('u~r', 'sun')] = ('no', 'sun')
d[('u~s', 'rain')] = ('no', 'rain')
d[('u~s', 'sun')] = ('umbrella', 'sun')
C = CartesianFrame(A, E, W, d)
rain = {('umbrella', 'rain'), ('no', 'rain')}
no_us = {('umbrella', 'rain'), ('no', 'rain'), ('no', 'sun')}
T = CartesianFrame({'a'},{},W)
nT = CartesianFrame(W, 'e', W, {(w,'e') : w for w in W})
uno = nT.dual()
zero = T.dual()
D1 = CartesianFrame({0,1}, {0,1}, {0,1}, {(b1,b2) : b1*b2 for b1 in {0,1} for b2 in {0,1}})
print(D1*D1)
pdb.set_trace()