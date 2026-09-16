"""Download one pinned prior dependency and verify this proof in a fresh build.
The upstream copyright/license are not determined by this submission.
The supplied Lean and Mathlib trees are read-only inputs.
"""
import argparse, hashlib, json, os, platform, re, shutil, subprocess, time
from datetime import datetime, timezone
from pathlib import Path
from urllib.request import urlopen
ROOT=Path(__file__).resolve().parent
MODULES=['Erdos882Existing','Erdos882Upper','AsymptoticCore','Erdos882Asymptotic']
MATHLIB_COMMIT='db584cd6d46c92f209a44c0f1c829460d327499d'
LEAN_COMMIT='d8b18978322de05a8f3dba51ef03cf5461676c17'
UPSTREAM_URL='https://raw.githubusercontent.com/plby/lean-proofs/8822f7ddef30fadbd92e1c6ab4ed897af356af5e/src/latest/ErdosProblems/Erdos882.lean'
UPSTREAM_SHA256='6797aeb572234c660b0990767b814d9cd8065356258085f2ef9a7d5d670c3f35'
sha=lambda data:hashlib.sha256(data).hexdigest()
def active_code(s):
    out=[]; i=0; depth=0
    while i<len(s):
        if depth:
            if s[i:i+2]=='/-': depth+=1; i+=2
            elif s[i:i+2]=='-/': depth-=1; i+=2
            else: out.append('\n' if s[i]=='\n' else ' '); i+=1
        elif s[i:i+2]=='/-': depth=1; i+=2
        elif s[i:i+2]=='--':
            end=s.find('\n',i); i=len(s) if end<0 else end
        elif s[i]=='"':
            i+=1
            while i<len(s):
                if s[i]=='\\': i+=2
                elif s[i]=='"': i+=1; break
                else: i+=1
        else: out.append(s[i]); i+=1
    if depth: raise RuntimeError('Unclosed source comment')
    return ''.join(out)
def fetch():
    curl=shutil.which('curl.exe') or shutil.which('curl')
    if curl:
        data=subprocess.check_output([curl,'--silent','--show-error','--fail','--location',
            '--proto','=https','--proto-redir','=https','--connect-timeout','15','--max-time','90',UPSTREAM_URL])
    else:
        with urlopen(UPSTREAM_URL,timeout=90) as response: data=response.read()
    if sha(data)!=UPSTREAM_SHA256: raise RuntimeError('Upstream source hash mismatch')
    return data

def main():
    ap=argparse.ArgumentParser()
    ap.add_argument('--lean-bin',type=Path,required=True)
    ap.add_argument('--mathlib',type=Path,required=True)
    ap.add_argument('--output',type=Path,required=True,help='New nonexistent directory; earlier evidence is never overwritten')
    args=ap.parse_args()
    out=args.output.resolve(); out.mkdir(parents=True,exist_ok=False)
    build=out/'build'; build.mkdir()
    ext='.exe' if os.name=='nt' else ''
    bindir=args.lean_bin.resolve(); lean=bindir/('lean'+ext); checker=bindir/('leanchecker'+ext)
    mathlib=args.mathlib.resolve()
    report=dict(result='incomplete',started_utc=datetime.now(timezone.utc).isoformat(),
        platform=platform.system(),arch=platform.machine(),
        verification_kind='fresh public helper end-to-end with downloaded pinned dependency',
        imported_mathlib_cache_used=True,network_isolation=False,
        checker='bundled leanchecker; same Lean kernel, not independently implemented',
        upstream_url=UPSTREAM_URL,upstream_sha256=UPSTREAM_SHA256,
        source_hashes={},steps=[],axiom_reports=[],helper_sha256=sha(Path(__file__).read_bytes()))
    env={k:v for k,v in os.environ.items() if not k.startswith(('LEAN_','LAKE_'))}
    paths=[build,mathlib/'.lake/build/lib/lean']+sorted((mathlib/'.lake/packages').glob('*/.lake/build/lib/lean'))
    env.update(LEAN_PATH=os.pathsep.join(map(str,paths)),LEAN_SYSROOT=str(bindir.parent),
               LEAN_NUM_THREADS='1',PATH=str(bindir)+os.pathsep+env.get('PATH',''))
    with (out/'verification.log').open('w',encoding='utf-8') as log:
        def write(s): log.write(s+'\n'); log.flush(); print(s,flush=True)
        def run(command,description):
            write('$ '+description); start=time.monotonic()
            r=subprocess.run(command,cwd=build,env=env,capture_output=True,text=True,encoding='utf-8',errors='replace')
            text=r.stdout+r.stderr
            for actual,alias in [(str(build),'<build>'),(str(ROOT),'<project>'),(str(out),'<output>'),(str(mathlib),'<mathlib>'),(str(bindir),'<lean-bin>')]:
                text=text.replace(actual,alias)
            write(text.rstrip()); write('exit='+str(r.returncode))
            report['steps'].append(dict(command=description,exit_code=r.returncode,seconds=round(time.monotonic()-start,3)))
            report['axiom_reports'] += [s for s in text.splitlines() if 'depends on axioms:' in s]
            if r.returncode: raise RuntimeError('Verification step failed: '+description)
        try:
            rev=subprocess.check_output(['git','-C',str(mathlib),'rev-parse','HEAD'],text=True).strip()
            if rev!=MATHLIB_COMMIT: raise RuntimeError('Mathlib revision mismatch')
            version=subprocess.check_output([str(lean),'--version'],env=env,text=True).strip()
            if 'version 4.33.0' not in version or LEAN_COMMIT not in version: raise RuntimeError('Lean release/commit mismatch')
            report.update(lean=version,mathlib_commit=rev,lean_sha256=sha(lean.read_bytes()),checker_sha256=sha(checker.read_bytes()))
            provenance=json.loads((ROOT/'provenance.json').read_text(encoding='utf-8'))
            if provenance['download_url']!=UPSTREAM_URL or provenance['sha256']!=UPSTREAM_SHA256:
                raise RuntimeError('Provenance mismatch')
            write(version); write('Mathlib '+rev)
            upstream=fetch(); write('Downloaded pinned upstream; SHA-256 verified: '+UPSTREAM_SHA256)
            for module in MODULES:
                name=module+'.lean'; data=upstream if module=='Erdos882Existing' else (ROOT/name).read_bytes()
                report['source_hashes'][name]=sha(data)
                forbidden=re.findall(r'\b(?:sorry|admit|axiom|native_decide|unsafe|implemented_by|extern)\b',active_code(data.decode('utf-8')))
                if forbidden: raise RuntimeError('Forbidden construct in '+name+': '+str(forbidden))
                (build/name).write_bytes(data)
            for module in MODULES:
                run([str(lean),'-j1','-M4096','-o',module+'.olean',module+'.lean'],f'lean -j1 -M4096 -o {module}.olean {module}.lean')
            for module in MODULES:
                run([str(checker),'--verbose',module],f'leanchecker --verbose {module}')
            for theorem in ['Erdos882.maximumSize_asymptotic','Erdos882.maximumSize_pow_le','Erdos882.erdos_882']:
                matches=[s for s in report['axiom_reports'] if "'"+theorem+"'" in s]
                if not matches: raise RuntimeError('Missing axiom report for '+theorem)
                for line in matches:
                    axioms=set(re.search(r'\[(.*)\]',line)[1].replace(' ','').split(','))-{''}
                    if not axioms<={'propext','Classical.choice','Quot.sound'}: raise RuntimeError('Unexpected axioms')
            for name,expected in report['source_hashes'].items():
                if sha((build/name).read_bytes())!=expected: raise RuntimeError('Build source changed')
                if name!='Erdos882Existing.lean' and sha((ROOT/name).read_bytes())!=expected: raise RuntimeError('Package source changed')
            if sha(Path(__file__).read_bytes())!=report['helper_sha256']: raise RuntimeError('Helper changed')
            report['output_hashes']={p.name:sha(p.read_bytes()) for p in sorted(build.glob('*.olean*'))}
            report['result']='pass'; write('PASS: pinned download, four compiles, four local-module replays, and axiom checks.')
        except BaseException as error:
            report['result']='fail'; report['error_type']=type(error).__name__; raise
        finally:
            log.flush(); report['finished_utc']=datetime.now(timezone.utc).isoformat()
            report['log_sha256']=sha((out/'verification.log').read_bytes())
            (out/'verification.json').write_text(json.dumps(report,indent=2)+'\n',encoding='utf-8')
if __name__=='__main__': main()
