"""Finite checks of omission witnesses; no finite test proves the density theorem."""
from pathlib import Path
from itertools import combinations
from math import isqrt
import json

ROOT=Path(__file__).resolve().parents[1]

def cbrt(n):
    lo,hi=0,n+1
    while hi-lo>1:
        mid=(lo+hi)//2
        if mid**3<=n:lo=mid
        else:hi=mid
    return lo

def distinct_blocks(a):
    products=set()
    for i in range(len(a)):
        p=1
        for x in a[i:]:
            p*=x
            if p in products:return False
            products.add(p)
    return True

def witness_check(a,n):
    m=isqrt(n);r=cbrt(n);t=isqrt(m)
    aset=set(a)
    holes=set(range(1,m+1))-aset
    pairs={a[i]*a[i+1] for i in range(len(a)-1) if t<a[i] and a[i+1]<=m}
    triples={a[i]*a[i+1]*a[i+2] for i in range(len(a)-2) if t<a[i] and a[i+2]<=r}
    assert not holes & pairs and not holes & triples and not pairs & triples
    all_holes=set(range(1,n+1))-aset
    assert holes|pairs|triples <= all_holes
    en=len(all_holes);er=r-sum(x<=r for x in a)
    assert m+r<=en+er+2*t+3

def main():
    valid=0;cases=0
    for size in range(17):
        for a in combinations(range(2,18),size):
            if not distinct_blocks(a):continue
            valid+=1
            for n in range(18):
                witness_check(a,n);cases+=1
    # Build and verify an actual finite greedy product-distinct prefix using exact integers.
    a=[];products=set();ends=set()
    for x in range(2,151):
        new={x}|{x*p for p in ends}
        if new & products:continue
        a.append(x);products.update(new);ends=new
    assert distinct_blocks(a)
    for n in range(151):witness_check(a,n);cases+=1
    # A weaker adjacency-only greedy sequence is not enough for the new finite inequality.
    limit=10**6;forbidden=set();last=None;omissions=[0]*(limit+1)
    for x in range(1,limit+1):
        if x==1 or x in forbidden:omissions[x]=omissions[x-1]+1
        else:
            omissions[x]=omissions[x-1]
            if last is not None and last*x<=limit:forbidden.add(last*x)
            last=x
    n=limit;m=isqrt(n);r=cbrt(n);t=isqrt(m)
    rhs=omissions[n]+omissions[r]+2*t+3
    assert m+r>rhs, 'Expected an adjacency-only negative control'
    # A density-one sequence alone is insufficient: all integers from 2 onward.
    assert m+r>1+1+2*t+3
    # Exact natural roots from Lean agree with independent binary search.
    lean=json.loads((ROOT/'verification/evaluation.log').read_text())
    assert lean==[cbrt(n) for n in range(1001)]
    report={'subsets_examined':2**16,'product_distinct_subsets':valid,
      'finite_witness_checks':cases,'greedy_prefix_length':len(a),
      'lean_cube_roots_matched':1001,
      'adjacency_only_negative_control':{'N':n,'left':m+r,'right':rhs,'E_N':omissions[n],'E_cube_root':omissions[r]},
      'all_integers_negative_control':True}
    (ROOT/'verification/small-cases.json').write_text(json.dumps(report,indent=2)+'\n')
    print(json.dumps(report,indent=2))

if __name__=='__main__':main()
