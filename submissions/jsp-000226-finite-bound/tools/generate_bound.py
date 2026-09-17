import json
from pathlib import Path
x=json.load(open('generated-work/proof-index.json'));p=Path('Erdos261Finite/FiniteBound.lean')
with p.open('w') as f:
 f.write(f'import Erdos261Finite.Cert{x["chunks"]-1:03}\n\nset_option maxRecDepth 4096\nset_option maxHeartbeats 0\nnamespace Erdos261Finite\n\n')
 leaves=[]
 for lo in range(2,10001,100):
  hi=min(lo+99,10000);name=f'tails_{lo}_{hi}';leaves.append((lo,hi,name))
  f.write(f'theorem {name} (n : ℕ) (hlo : {lo} ≤ n) (hhi : n ≤ {hi}) :\n    Represents (n + 1) (n - 1) := by\n  interval_cases n\n')
  for n in range(lo,hi+1):f.write(f'  · exact cert_{x["tails"][str(n)]}\n')
  f.write('\n')
 def combine(ls):
  if len(ls)==1:return ls[0]
  l=combine(ls[:len(ls)//2]);r=combine(ls[len(ls)//2:]);lo,mid,ln=l;rl,hi,rn=r;name=f'tails_{lo}_{hi}'
  f.write(f'theorem {name} (n : ℕ) (hlo : {lo} ≤ n) (hhi : n ≤ {hi}) :\n    Represents (n + 1) (n - 1) := by\n  by_cases h : n ≤ {mid}\n  · exact {ln} n hlo h\n  · exact {rn} n (by omega) hhi\n\n')
  return(lo,hi,name)
 combine(leaves)
 f.write('''/-- Formal verification of the finite bound in TUZ (2020), Theorem 3.5,
including the n=1 case from the public formal-conjectures statement. -/
theorem le_10000 {n : ℕ} (hn_pos : 0 < n) (hn : n ≤ 10000) : Erdos261Prop n := by
  by_cases h : n = 1
  · subst n
    exact property_one
  · have hn2 : 2 ≤ n := by omega
    exact property_of_tail n hn2 (tails_2_10000 n hn2 hn)

end Erdos261Finite
''')
