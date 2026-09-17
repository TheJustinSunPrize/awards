"""Generate exact polynomial identities, checked by Lean ring, not a trusted oracle."""
from fractions import Fraction as F
from math import comb
from pathlib import Path
root=Path(__file__).resolve().parent
C=F('4.309405275');D=C-F('4.3');A=F('2.3051746100259');s=F('0.31')
def add(a,b):
 r=[F(0)]*max(len(a),len(b))
 for i,v in enumerate(a):r[i]+=v
 for i,v in enumerate(b):r[i]+=v
 return r
def neg(a):return [-v for v in a]
def mul(a,b):
 r=[F(0)]*(len(a)+len(b)-1)
 for i,u in enumerate(a):
  for j,v in enumerate(b):r[i+j]+=u*v
 return r
def pw(a,n):
 r=[F(1)]
 for _ in range(n):r=mul(r,a)
 return r
def bernstein(p):
 n=len(p)-1
 b=[sum((p[j]*D**j*F(comb(k,j),comb(n,j)) for j in range(k+1)),F(0)) for k in range(n+1)]
 assert all(v>0 for v in b),b
 # p(x)=sum (b_k*binomial(n,k)/D^n) x^k (D-x)^(n-k)
 return [v*comb(n,k)/D**n for k,v in enumerate(b)]
def q(x):return f'({x.numerator} : ℝ) / {x.denominator}'
c=[C,-F(1)];ell=[A,-s]
polys=[('orientation_positive',add(pw(add(c,[F(1)]),7),neg(pw(add(pw(c,4),[-F(1)]),2))),
 '(c+1)^7 - (c^4-1)^2'),
 ('affine_below_root',add(add(pw(c,4),[F(1)]),neg(pw(ell,7))),
 'c^4 + 1 - line c ^ 7'),
 ('affine_contradiction',add(add(mul(c,pw(ell,5)),pw(ell,4)),neg(pw(add(pw(c,2),[-F(1)]),2))),
 'c * line c ^ 5 + line c ^ 4 - (c^2-1)^2')]
out=['import ThreeGenerator\n\nnoncomputable section\nnamespace JSP791\n',
 'def cutoff : ℝ := '+q(C)+'\n',
 'def line (c : ℝ) : ℝ := '+q(A)+' - ('+q(s)+')*(cutoff-c)\n']
for name,p,expression in polys:
 bs=bernstein(p); n=len(p)-1
 print(name,'degree',n,'minimum Bernstein coefficient',float(min(bs)))
 terms=[f'({q(v)}) * x^{k} * (d-x)^{n-k}' for k,v in enumerate(bs)]
 out += [f'lemma {name} {{c : ℝ}} (hl : (43:ℝ)/10 ≤ c) (hu : c ≤ cutoff) :\n    0 < {expression} := by\n',
 '  let x : ℝ := cutoff-c\n  let d : ℝ := '+q(D)+'\n',
 '  have hx : 0 ≤ x := by dsimp [x]; linarith\n',
 '  have hd : 0 ≤ d-x := by dsimp [d,x,cutoff] at *; linarith\n',
 '  have hdpos : 0 < d := by norm_num [d]\n',
 f'  have identity : {expression} =\n    '+' +\n    '.join(terms)+' := by\n    dsimp [line,cutoff,x,d]\n    ring\n',
 '  rw [identity]\n  by_cases hh : x = 0\n  · simp only [hh]\n    norm_num [d]\n',
 '  · have hxp : 0 < x := lt_of_le_of_ne hx (Ne.symm hh)\n    positivity\n']
out+=['end JSP791\n', '#print axioms JSP791.orientation_positive\n#print axioms JSP791.affine_below_root\n#print axioms JSP791.affine_contradiction\n']
(root/'LowerCertificate.lean').write_text('\n'.join(out),encoding='utf-8',newline='\n')
