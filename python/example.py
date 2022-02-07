from z3 import *

hi = Int('hi')
lo = Int('lo')

j = Const('j', IntSort()) 

l1 = Int('l1')
h1 = Int('h1')

sum0 = Function('sum', IntSort(), IntSort(),  IntSort())
s0 = Function('s', IntSort(), IntSort(), IntSort() )
arr = Function('arr', IntSort(), IntSort())

s = Solver()

s.add(ForAll([j], arr(j) == j + 1))
s.add(h1 == 31)
s.add(l1 == 0)
s.add(ForAll([lo, hi], sum0(lo, hi) == s0(lo, hi), patterns=[sum0(lo, hi)]))
s.add(ForAll([lo, hi], Implies(And(lo >= hi, hi < h1, hi >= l1, lo >= l1, lo < h1), s0(lo, hi) == 0), patterns=[sum0(lo, hi)]))
s.add(ForAll([hi, lo], Implies(And(hi < h1, hi >= l1, lo >= l1, lo < h1, lo < hi), s0(lo, hi) == arr(hi - 1)  + s0(lo, hi - 1)), patterns=[sum0(lo, hi)])) 

s.add(sum0(0, 30) == 465)
print(s.check())
# print(s.model())
print(s.sexpr())

