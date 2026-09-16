#!/usr/bin/env python3
"""Translate ordered RUP hints to ordinary propositional Lean proofs.
Clause L is encoded as (not L[0]) -> ... -> False. No native evaluation.
"""
from pathlib import Path
import argparse

def atom(lit):
    return f'p {abs(lit)}' if lit>0 else f'¬ p {abs(lit)}'
def ctype(c):
    return ' → '.join([f'({atom(-lit)})' for lit in c]+['False'])
def main():
    ap=argparse.ArgumentParser()
    ap.add_argument('--cnf',type=Path,default=Path('evidence/core.cnf'))
    ap.add_argument('--lrat',type=Path,default=Path('evidence/core.lrat'))
    ap.add_argument('--out',type=Path,default=Path('JSP000746/Resolution.lean'))
    ap.add_argument('--shard-size',type=int,default=250)
    a=ap.parse_args(); initial=[]
    for l in a.cnf.read_text().splitlines():
        if l and l[0] not in 'cp':
            r=list(map(int,l.split()));assert r[-1]==0;initial.append(r[:-1])
    cs={i+1:c for i,c in enumerate(initial)};hs={}
    for l in a.lrat.read_text().splitlines():
        r=l.split()
        if r[1]=='d':continue
        r=list(map(int,r));i=r[0];z=r.index(0);assert r[-1]==0
        cs[i]=r[1:z];hs[i]=r[z+1:-1];assert all(0<h<i for h in hs[i])
    empty=max(hs);assert not cs[empty];need={empty};todo=[empty]
    while todo:
        for d in hs[todo.pop()]:
            if d in hs and d not in need:need.add(d);todo.append(d)
    need=sorted(need);a.out.parent.mkdir(parents=True,exist_ok=True);shards=[]
    for start in range(0,len(need),a.shard_size):
        s=a.out.with_name(f'ResolutionPart{start//a.shard_size:03d}.lean');shards.append(s)
        out=['import Init.Classical\n\nset_option maxHeartbeats 0\nset_option maxRecDepth 100000\n\nnamespace JSP000746.RUP\n']
        for i in need[start:start+a.shard_size]:
            ds=list(dict.fromkeys(hs[i]));out.append(f'\ntheorem c{i} (p : Nat → Prop)\n')
            out.extend(f'    (d{d} : {ctype(cs[d])})\n' for d in ds)
            out.append(f'    : {ctype(cs[i])} := by\n');env={}
            if cs[i]:
                out.append('  intro '+' '.join(f'a{k}' for k in range(len(cs[i])))+'\n')
                env={-lit:f'a{k}' for k,lit in enumerate(cs[i])}
            conflict=False
            for k,d in enumerate(hs[i]):
                c=cs[d];assert not any(lit in env for lit in c),(i,d,'satisfied')
                rem=[lit for lit in c if -lit not in env];assert len(rem)<=1,(i,d,rem)
                if not rem:
                    out.append('  exact d'+str(d)+' '+' '.join(env[-lit] for lit in c)+'\n');conflict=True;break
                unit=rem[0];term='d'+str(d)+' '+' '.join('u' if lit==unit else env[-lit] for lit in c)
                proof=f'Classical.byContradiction (fun u => {term})' if unit>0 else f'(fun u => {term})'
                out.append(f'  have v{k} : {atom(unit)} := {proof}\n');env[unit]=f'v{k}'
            assert conflict,i
        out.append('\nend JSP000746.RUP\n');s.write_text(''.join(out))
    out=[f'import JSP000746.{s.stem}\n' for s in shards]
    out.append('\nset_option maxHeartbeats 0\nset_option maxRecDepth 100000\n\nnamespace JSP000746\n\ntheorem resolution (p : Nat → Prop)\n')
    out.extend(f'    (h{i} : {ctype(c)})\n' for i,c in enumerate(initial,1));out.append('    : False := by\n')
    for i in need:
        ds=list(dict.fromkeys(hs[i]));out.append(f'  have h{i} := RUP.c{i} p '+' '.join(f'h{d}' for d in ds)+'\n')
    out.append(f'  exact h{empty}\n\n#print axioms resolution\n\nend JSP000746\n');a.out.write_text(''.join(out))
    print(f'{len(need)} lemmas, {len(shards)} shards, {len(initial)} initial clauses')
if __name__=='__main__':main()
