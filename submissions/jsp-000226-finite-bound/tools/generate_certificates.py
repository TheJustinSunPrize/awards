from array import array
from pathlib import Path
A=array('I',[0]);R=array('I',[0]);S=array('I',[0]);I=array('I',[0]);
for line in open('generated-work/greedy-dag.tsv'):
 a,r,s=map(int,line.split());A.append(a);R.append(r);S.append(s);I.append(0)
for s in S[1:]: I[s]+=1
D=array('I',[0])*len(A);E=array('I',[0])*len(A);B=bytearray(len(A)); selected=[];roots={};tails={}
for i in range(1,len(A)):
 s=S[i];D[i]=1 if s==0 or B[s] else D[s]+1;E[i]=s if s==0 or B[s] else E[s]
 root=A[i]==R[i] and 2<=A[i]<=10000
 tail=A[i]>=3 and A[i]<=10001 and R[i]==A[i]-2
 if I[i]>1 or tail or D[i]>=256:
  B[i]=1;selected.append(i)
 if root:roots[A[i]]=i
 if tail:tails[A[i]-1]=i
p=Path('Erdos261Finite');p.mkdir(exist_ok=True)
for fi,start in enumerate(range(0,len(selected),500)):
 prev='Erdos261Finite' if fi==0 else f'Erdos261Finite.Cert{fi-1:03}'
 with open(p/f'Cert{fi:03}.lean','w') as out:
  out.write(f'import {prev}\n\nset_option maxRecDepth 4096\nset_option maxHeartbeats 0\nnamespace Erdos261Finite\n\n')
  for i in selected[start:start+500]:
   e=E[i];k=D[i];a=A[i];r=R[i];b=A[e] if e else a+k;s=R[e] if e else 0
   proof=f'cert_{e}' if e else f'(zero_represents {b})'
   out.write(f'theorem cert_{i} : Represents {a} {r} :=\n  segment {k} {a} {r} {b} {s} (by rfl) {proof}\n\n')
  out.write('end Erdos261Finite\n')
import json
json.dump({'roots':roots,'tails':tails,'chunks':fi+1,'segments':len(selected),'states':len(A)-1},open('generated-work/proof-index.json','w'))
print('states',len(A)-1,'segments',len(selected),'chunks',fi+1,'roots',len(roots))

for f in p.glob("Cert*.lean"):
 if int(f.stem[4:]) >= fi+1: f.unlink()
