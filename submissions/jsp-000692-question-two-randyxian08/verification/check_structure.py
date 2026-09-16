"""Finite tests of the extremal-colouring argument; not Lean verification."""
import itertools, json

def bits(mask):
    while mask:
        low = mask & -mask
        yield low.bit_length() - 1
        mask ^= low

def alon(r):
    n = 2*r-2
    full = (1 << n)-1
    def masks(k):
        return [sum(1 << x for x in a) for a in itertools.combinations(range(n), k)]
    edges = set(masks(r))
    halves = [a for a in masks(r-1) if a & 1]
    for j, a in enumerate(halves):
        y = 1 << (n+j)
        edges.add(a|y)
        edges.add((full^a)|y)
    return (sorted(edges),)

def check(edges, label):
    H=set(edges)
    r=next(iter(H)).bit_count()
    U=0
    for e in H: U |= e
    assert all(e.bit_count()==r for e in H)
    assert all(e&f for e,f in itertools.combinations(H,2))
    s=max((e&f).bit_count() for e,f in itertools.combinations(H,2))
    tested=0
    for e in H:
        R=e
        for y in list(bits(U^R)):
            candidate=R | 1<<y
            if all(f==e or (f&candidate)!=f for f in H): R=candidate
        B=U^R
        assert all(f==e or (f&R)!=f for f in H)
        g={}
        for x in bits(e):
            matches=[f for f in H if f&R==1<<x]
            assert matches, (label, 'missing singleton witness',e,R,x)
            g[x]=matches[0]
        f={}
        for y in bits(B):
            matches=[t for t in H if t!=e and t & (R | 1<<y)==t]
            assert matches
            f[y]=matches[0]
        for x0 in bits(e):
            A=e^(1<<x0); C=g[x0]^(1<<x0)
            assert A.bit_count()==C.bit_count()==r-1 and C&B==C
            rows=[sum(bool(g[x]>>y&1) for y in bits(C)) for x in bits(A)]
            cols=[sum(not bool(g[x]>>y&1) for x in bits(A)) for y in bits(C)]
            assert all(v<=s for v in rows)
            assert all(v<=s for v in cols)
            assert sum(rows)+sum(cols)==(r-1)**2
            assert r<=2*s+1
            tested+=1
    return dict(family=label,rank=r,max_intersection=s,base_edge_pivot_tests=tested,
                extremal_colouring_witnesses_valid=True,matrix_counts_valid=True)

triples=[(0,1,2),(0,3,4),(0,5,6),(1,3,5),(1,4,6),(2,3,6),(2,4,5)]
rows=[check([sum(1<<v for v in e) for e in triples],'Fano')]
for r in range(2,6): rows.append(check(alon(r)[-1],f'Alon r={r}'))
print(json.dumps({'status':'PASS','kind':'FINITE_SANITY_CHECK_NOT_A_PROOF','cases':rows},indent=2))
