"""Compile all project sources and replay each local module with leanchecker.

Supply an already installed pinned Lean runtime and Mathlib checkout/cache.
This script never writes to the supplied runtime or Mathlib directory.
"""
import argparse, hashlib, json, os, platform, re, subprocess, sys, time
from pathlib import Path

ROOT=Path(__file__).resolve().parent
MODULES=['Erdos882Existing','Erdos882Upper','AsymptoticCore','Erdos882Asymptotic']
MATHLIB_COMMIT='db584cd6d46c92f209a44c0f1c829460d327499d'

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
    return ''.join(out)

def main():
    ap=argparse.ArgumentParser()
    ap.add_argument('--lean-bin',type=Path,required=True)
    ap.add_argument('--mathlib',type=Path,required=True)
    ap.add_argument('--output',type=Path,default=ROOT/'verification')
    args=ap.parse_args()
    out=args.output.resolve(); out.mkdir(parents=True,exist_ok=True)
    build=out/('build-'+time.strftime('%Y%m%d-%H%M%S')); build.mkdir()
    ext='.exe' if os.name=='nt' else ''
    lean=args.lean_bin.resolve()/('lean'+ext)
    checker=args.lean_bin.resolve()/('leanchecker'+ext)
    mathlib=args.mathlib.resolve()
    rev=subprocess.check_output(['git','-C',str(mathlib),'rev-parse','HEAD'],text=True).strip()
    if rev!=MATHLIB_COMMIT: raise RuntimeError('Mathlib revision mismatch: '+rev)
    version=subprocess.check_output([str(lean),'--version'],text=True).strip()
    if 'version 4.33.0' not in version: raise RuntimeError('Lean version mismatch: '+version)
    paths=[build,mathlib/'.lake/build/lib/lean']
    paths += [p/'.lake/build/lib/lean' for p in sorted((mathlib/'.lake/packages').iterdir())
              if (p/'.lake/build/lib/lean').is_dir()]
    env=dict(os.environ,LEAN_PATH=os.pathsep.join(map(str,paths)))
    report=dict(lean=version,mathlib_commit=rev,platform=platform.system(),arch=platform.machine(),
        imported_mathlib_cache_used=True,network_isolation=False,
        checker='bundled leanchecker; same Lean kernel, not independently implemented',
        source_hashes={},steps=[],axiom_reports=[])
    with (out/'verification.log').open('w',encoding='utf-8') as log:
        def write(s): log.write(s+'\n'); log.flush(); print(s,flush=True)
        def run(command,description):
            write('$ '+description)
            start=time.monotonic()
            r=subprocess.run(command,cwd=build,env=env,capture_output=True,text=True,encoding='utf-8',errors='replace')
            text=r.stdout+r.stderr
            for actual,alias in [(str(ROOT),'<project>'),(str(build),'<build>'),(str(mathlib),'<mathlib>'),(str(args.lean_bin.resolve()),'<lean-bin>')]:
                text=text.replace(actual,alias)
            write(text.rstrip()); write('exit='+str(r.returncode))
            report['steps'].append(dict(command=description,exit_code=r.returncode,seconds=round(time.monotonic()-start,3)))
            report['axiom_reports'] += [line for line in text.splitlines() if 'depends on axioms:' in line]
            if r.returncode: raise RuntimeError('Verification step failed: '+description)
        write(version); write('Mathlib '+rev)
        for module in MODULES:
            source=ROOT/(module+'.lean'); data=source.read_bytes()
            report['source_hashes'][source.name]=hashlib.sha256(data).hexdigest()
            forbidden=re.findall(r'\b(?:sorry|admit|axiom|native_decide|unsafe|implemented_by|extern)\b',active_code(data.decode()))
            if forbidden: raise RuntimeError('Forbidden source construct in '+source.name+': '+str(forbidden))
            copied=build/source.name; copied.write_bytes(data)
            run([str(lean),'-j1','-M4096','-o',module+'.olean',copied.name],
                f'lean -j1 -M4096 -o {module}.olean {module}.lean')
        for module in MODULES:
            run([str(checker),'--verbose',module],f'leanchecker --verbose {module}')
        required=['Erdos882.maximumSize_asymptotic','Erdos882.maximumSize_pow_le','Erdos882.erdos_882']
        for theorem in required:
            matches=[line for line in report['axiom_reports'] if "'"+theorem+"'" in line]
            if not matches: raise RuntimeError('Missing axiom report for '+theorem)
            for line in matches:
                axioms=set(re.search(r'\[(.*)\]',line)[1].replace(' ','').split(','))-{''}
                if not axioms<={'propext','Classical.choice','Quot.sound'}:
                    raise RuntimeError('Unexpected theorem axiom report')
        report['result']='pass'
        write('PASS: all four source modules compiled and replayed; final axiom reports checked.')
    report['log_sha256']=hashlib.sha256((out/'verification.log').read_bytes()).hexdigest()
    (out/'verification.json').write_text(json.dumps(report,indent=2),encoding='utf-8')

if __name__=='__main__': main()
