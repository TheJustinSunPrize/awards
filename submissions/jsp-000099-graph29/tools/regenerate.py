#!/usr/bin/env python3
"""Generate untrusted search certificates, then compare the exact Lean source bytes.
Only Lean's proved checker and its kernel establish the mathematical result.
"""
from pathlib import Path
import argparse, re, subprocess, tempfile, json
FULL=(1<<29)-1

def generate(raw,d,adj):
 s=raw;lo=s.index(':=\n')+3;hi=s.index('\n theorem checked',lo);tokens=iter(re.findall(r'\.[a-z]+|\d+|[()]',s[lo:hi]))
 def parse():
  t=next(tokens)
  if t=='.small':return ('small',[],[])
  assert t=='(';tag=next(tokens)[1:];args=[int(next(tokens))]
  if tag=='checkpoint':args.append(int(next(tokens)))
  children=[parse() for _ in range(0 if tag=='bad' else 2 if tag=='split' else 1)]
  assert next(tokens)==')';return tag,args,children
 tree=parse();assert next(tokens,None) is None
 defs=[];theorems=[]
 def package(name,expr,S,U,proof):
  definition=f'@[irreducible] def {name} : FastCert := {expr}\n'
  proof=f'theorem {name}_ok : fcheck 7 {d} {S} {U} {name} = true := by\n  unfold {name}\n  exact {proof}\n'
  defs.append(definition+proof)
 def walk(node,S,U):
  tag,args,children=node
  if tag=='small':expr='.small';size=1;proof='(by decide +kernel)'
  else:
   v=args[0];mask=1<<v if tag!='checkpoint' else 0
   if tag=='bad':states=[]
   elif tag=='drop':states=[(S,U&~mask)]
   elif tag=='fill':states=[(S|(adj[v]&U),U)]
   elif tag=='empty':states=[(S,U&~(adj[v]&~S))]
   elif tag=='split':states=[(S|mask,U),(S,U&~mask)]
   else:
    assert tag=='checkpoint' and args==[S,U]
    states=[(S,U)]
   child=[walk(ch,*st) for ch,st in zip(children,states)]
   expr='(.'+tag+' '+' '.join(map(str,args))+(' '+' '.join(e for e,_,_ in child) if child else '')+')'
   size=1+sum(n for _,n,_ in child)
   if tag=='bad':proof='(by decide +kernel)'
   elif tag=='split':proof='(accept_split '+child[0][2]+' '+child[1][2]+')'
   else:proof='(accept_'+tag+' (by decide +kernel) '+child[0][2]+')'
  if size>60:
   name=f'c{d}_{len(defs)}';package(name,expr,S,U,proof);return name,1,name+'_ok'
  return expr,size,proof
 expr,_,proof=walk(tree,0,FULL);package(f'cert{d}',expr,0,FULL,proof)
 out='import CertificateSteps\nset_option maxHeartbeats 0\nset_option maxRecDepth 10000\nnamespace Erdos82Finite\nopen RegularCertificate\n\n'+'\n'.join(defs)
 out+=f'\ntheorem checked{d} : fcheck 7 {d} 0 full cert{d} = true := cert{d}_ok\n\ntheorem no_regular_{d} (T : Finset (Fin 29)) (h : 7 ≤ T.card) : ¬ RegularOn neighbors T {d} :=\n  fcheck_sound {d} cert{d} checked{d} T h\n\n#print axioms no_regular_{d}\nend Erdos82Finite\n'
 return out,len(defs)

def split_module(source,d):
 prefix,rest=source.split("@[irreducible] def ",1)
 blocks=["@[irreducible] def "+b for b in rest.split("@[irreducible] def ")]
 if len(source.encode()) <= 350000:
  return {f"Degree{d}.lean":source}
 groups=[];current=[];size=0
 for block in blocks[:-1]:
  if current and size+len(block.encode())>300000:
   groups.append(current);current=[];size=0
  current.append(block);size+=len(block.encode())
 if current:groups.append(current)
 result={};previous="CertificateSteps"
 for i,group in enumerate(groups):
  name=f"Degree{d}Part{i}"
  result[name+".lean"]=prefix.replace("import CertificateSteps", "import "+previous)+"\n".join(group)+"\nend Erdos82Finite\n"
  previous=name
 result[f"Degree{d}.lean"]=prefix.replace("import CertificateSteps", "import "+previous)+blocks[-1]
 return result

def main():
 parser=argparse.ArgumentParser()
 parser.add_argument("--project",type=Path,default=Path(__file__).resolve().parent.parent)
 parser.add_argument("--data",type=Path)
 parser.add_argument("--generator",type=Path)
 parser.add_argument("--write",action="store_true")
 args=parser.parse_args();project=args.project.resolve()
 data=(args.data or project/"supporting-computation").resolve()
 generator=(args.generator or Path(__file__).resolve().parent/"generate_cert29.cpp").resolve()
 adj=json.loads((data/"e82-witness.json").read_text())["adjacency_masks"]
 with tempfile.TemporaryDirectory(prefix="erdos82-certificate-") as tmp:
  tmp=Path(tmp);binary=tmp/"generator"
  subprocess.run(["clang++","-O3","-std=c++17",str(generator),"-o",str(binary)],check=True)
  subprocess.run([str(binary),str(data/"e82-witness.g6"),str(tmp)],check=True,capture_output=True,text=True)
  generated={};high="import CertificateSteps\nset_option maxHeartbeats 0\nset_option maxRecDepth 10000\nnamespace Erdos82Finite\nopen RegularCertificate\n"
  for d in range(29):
   source,n=generate((tmp/f"Degree{d}.lean").read_text(),d,adj)
   if d<11:generated.update(split_module(source,d))
   else:high+=source.split("namespace Erdos82Finite\n",1)[1].rsplit("end Erdos82Finite",1)[0]+"\n"
  generated["HighDegrees.lean"]=high+"end Erdos82Finite\n"
  for name,content in generated.items():
   if args.write:(project/name).write_text(content)
   elif not (project/name).is_file() or (project/name).read_bytes()!=content.encode():
    raise SystemExit("Certificate differs: "+name)
  print(("Wrote" if args.write else "Exact byte comparison passed for")+f" {len(generated)} certificate modules.")
if __name__=="__main__":main()
