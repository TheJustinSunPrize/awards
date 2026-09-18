from itertools import combinations, combinations_with_replacement
from collections import Counter
import json

def sums(xs,k):
    return Counter(map(sum,combinations(xs,k)))

results=[]
for k in range(3,9):
    n=k-3
    c=[-5,-1,0,1,2,3]
    for j in range(n):
        c += [10+j,-(10+j)]
    a=[11+n+x for x in c]
    b=[11+n-x for x in c]
    assert len(set(a))==len(set(b))==2*k
    assert min(a)>0 and min(b)>0 and set(a)!=set(b)
    assert sums(a,k)==sums(b,k)
    results.append({'k':k,'cardinality':2*k,'combinations':sum(sums(a,k).values()),'pass':True})
seen={}
for xs in combinations_with_replacement(range(-5,6),3):
    ps=tuple(sorted(map(sum,combinations(xs,2))))
    assert sum(ps)%2==0
    total=sum(ps)//2
    recovered=tuple(sorted(total-v for v in ps))
    assert recovered==xs
    assert ps not in seen or seen[ps]==xs
    seen[ps]=xs
print(json.dumps({'all_k_finite_checks':results,'three_entry_recovery_checks':len(seen),
    'scope':'Finite checks; universal proofs are in Complement.lean'},indent=2))
