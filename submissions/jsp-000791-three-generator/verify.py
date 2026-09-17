"""Build and kernel-check all four modules with pinned, clean dependencies."""
from pathlib import Path
from datetime import datetime, timezone
import hashlib,json,re,shutil,subprocess
ROOT=Path(__file__).resolve().parent
OUT=ROOT/'verification'
MODULES=['ThreeGenerator','LowerCertificate','SharpLower','SequenceBridge']
ALLOWED={'propext','Classical.choice','Quot.sound'}
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
def main():
    OUT.mkdir(exist_ok=True)
    lake=shutil.which('lake')
    if not lake:raise RuntimeError('Put Lean 4.34.0 and Lake on PATH')
    manifest=json.loads((ROOT/'lake-manifest.json').read_text())
    deps={}
    for pkg in manifest['packages']:
        assert pkg['type']=='git'
        path=ROOT/manifest['packagesDir']/pkg['name']
        rev=subprocess.check_output(['git','rev-parse','HEAD'],cwd=path,text=True).strip()
        dirty=subprocess.check_output(['git','status','--porcelain','--untracked-files=no'],cwd=path,text=True).strip()
        assert rev==pkg['rev'] and not dirty, pkg['name']
        deps[pkg['name']]=rev
    assert deps['mathlib']=='5ed2965256430c3649e86755f9576b54eca72435'
    files=[n+'.lean' for n in MODULES]+['lean-toolchain','lakefile.toml','lake-manifest.json',
        'verify.py','verify_independent.py','generate_lower_certificate.py','README.md','INDEPENDENT.md','.gitignore','.gitattributes']
    before={n:sha(ROOT/n) for n in files}
    commands=[('version',['env','lean','--version'],None),('build',['build'],None)]
    for n in MODULES:
        text=(ROOT/(n+'.lean')).read_text(encoding='utf-8')
        assert not re.search(r'\b(sorry|admit|axiom|native_decide|unsafe|implemented_by)\b',text),n
        targets=set(re.findall(r'^#print axioms ([\w.]+)',text,re.M))
        assert targets,n
        commands.append((n,['env','lean','--trust=0','-j1','-M2500','-o',
            '.lake/build/lib/lean/'+n+'.olean',n+'.lean'],targets))
    results=[]
    for label,args,targets in commands:
        print('Checking',label,flush=True)
        result=subprocess.run([lake,*args],cwd=ROOT,stdout=subprocess.PIPE,stderr=subprocess.STDOUT,
            encoding='utf-8',timeout=600)
        log=OUT/(label+'.log');log.write_text(result.stdout,encoding='utf-8',newline='\n')
        if result.returncode:raise RuntimeError(result.stdout[-5000:])
        if label=='version':assert 'Lean (version 4.34.0,' in result.stdout
        if targets:
            found=re.findall(r"'([^']+)' depends on axioms: \[([^]]*)\]",result.stdout)
            found += [(n,'') for n in re.findall(r"'([^']+)' does not depend on any axioms",result.stdout)]
            assert {n for n,_ in found}==targets,(label,found)
            for target,axioms in found:assert {x.strip() for x in axioms.split(',') if x.strip()}<=ALLOWED,target
        results.append(dict(command=['lake',*args],exit_code=0,log=log.name,sha256=sha(log)))
    assert before=={n:sha(ROOT/n) for n in files},'Files changed during verification'
    record=dict(checked_at_utc=datetime.now(timezone.utc).isoformat(),problem='JSP-000791 / Erdos 951',
        target='JSP791.sequence_third_generator_gt_cutoff',lean='4.34.0',dependencies=deps,
        scope='Third generator > 4.309405275 for every strictly increasing sequence satisfying full exponent-vector separation',
        complete_original_problem=False,new_mathematical_result=False,priority='not asserted',
        environment='Windows; pinned sources and Mathlib compiled caches',network_isolated=False,
        independent_checker=False,official_verification=False,files=before,checks=results)
    (OUT/'result.json').write_text(json.dumps(record,indent=2)+'\n',encoding='utf-8',newline='\n')
    print('All four source modules passed kernel checks; official review is separate.',flush=True)
if __name__=='__main__':main()
