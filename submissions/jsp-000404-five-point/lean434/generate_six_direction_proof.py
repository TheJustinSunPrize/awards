"""Generate a Lean proof, using Z3 only to prune a finite case tree.

Each emitted leaf is a Lean linarith proof from explicit hypotheses. Z3 is
not trusted by the finished theorem. This proves a six-label necessary
condition only; geometric realization and the all-N bound remain separate.
"""
from itertools import combinations
from pathlib import Path
import json
import z3

W=Path(__file__).parent
pairs=list(combinations(range(6),2))
triples=list(combinations(range(6),3))
t=z3.Real('t')
x={ij:z3.Real(f'x{ij[0]}{ij[1]}') for ij in pairs}
s=z3.Solver()
labels={}
counter=0
leaves=0
splits=0
maxdepth=0
def track(expr,lean):
    global counter
    label=f'row{counter}'
    counter+=1
    labels[label]=lean
    s.assert_and_track(expr,z3.Bool(label))

track(t<z3.RealVal('3'),'ht')
for ij in pairs:
    name=f'r{ij[0]}{ij[1]}'
    track(x[ij]>=0,name+'.1')
    track(x[ij]<t,name+'.2')

def tree(depth,indent):
    global leaves,splits,maxdepth
    if s.check()==z3.unsat:
        leaves+=1
        maxdepth=max(maxdepth,depth)
        refs=[labels[str(a)] for a in s.unsat_core()]
        return indent+'linarith only ['+', '.join(refs)+']\n'
    if depth==len(triples):
        raise RuntimeError('Countermodel found: '+str(s.model()))
    splits+=1
    i,j,k=triples[depth]
    name=f'h{i}{j}{k}'
    a,b,c=x[i,j],x[i,k],x[j,k]
    out=indent+f'rcases {name} with ⟨{name}a, {name}b, {name}c, {name}d, {name}e⟩ | ⟨{name}a, {name}b, {name}c, {name}d, {name}e⟩\n'
    branches=[[a<=b,b<=c,c-a>=1,b-a<=t-1,c-b<=t-1],
              [c<=b,b<=a,a-c>=1,a-b<=t-1,b-c<=t-1]]
    for branch in branches:
        s.push()
        for suffix,expr in zip('abcde',branch): track(expr,name+suffix)
        child=tree(depth+1,indent+'  ')
        out+=indent+'· '+child[len(indent)+2:]
        s.pop()
    return out

header='''import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Linarith

/-!
A sharp necessary condition for six ordered planar-direction labels.
Generated finite case split; every leaf is checked by Lean's kernel.
This does not yet prove a theorem about actual planar point sets. In particular,
it assumes explicit direction-triple constraints and does not assert that
an arbitrary point configuration has been mapped to them.
-/
namespace SendovSixDirections

def Triangle (t a b c : ℝ) : Prop :=
  (a ≤ b ∧ b ≤ c ∧ 1 ≤ c-a ∧ b-a ≤ t-1 ∧ c-b ≤ t-1) ∨
  (c ≤ b ∧ b ≤ a ∧ 1 ≤ a-c ∧ a-b ≤ t-1 ∧ b-c ≤ t-1)

set_option maxRecDepth 4096
set_option maxHeartbeats 20000000

theorem three_le
'''
header+='    (t '+' '.join(f'x{i}{j}' for i,j in pairs)+' : ℝ)\n'
for i,j in pairs: header+=f'    (r{i}{j} : 0 ≤ x{i}{j} ∧ x{i}{j} < t)\n'
for i,j,k in triples: header+=f'    (h{i}{j}{k} : Triangle t x{i}{j} x{i}{k} x{j}{k})\n'
header+='    : 3 ≤ t := by\n  by_contra hn\n  have ht : t < 3 := lt_of_not_ge hn\n'
header+='  unfold Triangle at '+' '.join(f'h{i}{j}{k}' for i,j,k in triples)+'\n'
proof=tree(0,'  ')
text=header+proof+'\n#print axioms three_le\nend SendovSixDirections\n'
(W/'SendovSixDirections.lean').write_text(text,encoding='utf-8',newline='\n')
receipt=dict(leaf_count=leaves,split_count=splits,max_depth=maxdepth,
             z3_version=z3.get_version_string(),scope='Six abstract direction labels; Lean check required.')
(W/'SendovSixDirections.generation.json').write_text(json.dumps(receipt,indent=2),encoding='utf-8',newline='\n')
print(receipt,flush=True)

