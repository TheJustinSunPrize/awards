#!/usr/bin/env python3
"""Reproduce the closed-set bridge with read-only Mathlib and fresh private output.

Python 3.10+. Default/--plan runs no subprocess and downloads nothing. Explicit
--execute downloads two fixed sources, compiles three modules, checks the two
final theorem axiom reports, and replays the bridge. No Lake or cache writes.
"""
import argparse, hashlib, json, os, re, subprocess, sys, time, urllib.request
from datetime import datetime, timezone
from pathlib import Path

HERE = Path(__file__).resolve().parent
UPSTREAM_SHA256 = '63e84cd2a1f3c295c64c0ccd389560da6ef75aa9e56c99ac00d0d92954d5b2a6'
SOURCE_REVISION_SHA256 = '19a386ae01229ed414ef880b5e3db82d51fb6bdfaaf201c5a0d2c4dd62f3edb2'
STANDARD = {'propext', 'Classical.choice', 'Quot.sound'}

def sha(data): return hashlib.sha256(data).hexdigest()

def require(ok, message):
    if not ok: raise ValueError(message)

def save(path, value):
    path.write_bytes((json.dumps(value, ensure_ascii=False, indent=2)+'\n').encode('utf-8'))

def tool(directory, name):
    return directory / (name+'.exe' if (directory/(name+'.exe')).is_file() else name)

def load():
    raw = (HERE/'upstream.json').read_bytes()
    require(sha(raw) == UPSTREAM_SHA256, 'Pinned upstream metadata changed')
    refs = json.loads(raw)
    evidence = json.loads((HERE/'verification.json').read_text(encoding='utf-8'))
    bridge = (HERE/'JSP410ClosedBridge.lean').read_bytes()
    revision_path = HERE/'bridge-source-revision.json'
    if revision_path.exists():
        revision_bytes = revision_path.read_bytes()
        require(sha(revision_bytes) == SOURCE_REVISION_SHA256, 'Current-source revision metadata changed')
        revision = json.loads(revision_bytes)
        require(revision['original_sha256'] == evidence['bridge_sha256'] and
                revision['original_size_bytes'] == evidence['bridge_size_bytes'], 'Source revision does not refer to historical verified bytes')
        require(sha(bridge) == revision['current_sha256'] and len(bridge) == revision['current_size_bytes'], 'Current bridge source pin differs')
        edit = revision['edit']
        require(edit['kind'] == 'replace_exact_comment_once', 'Unsupported source revision')
        old, new = edit['old_comment'].encode('utf-8'), edit['new_comment'].encode('utf-8')
        require(old.startswith(b'/-- ') and old.endswith(b' -/') and new.startswith(b'/-- ') and new.endswith(b' -/'), 'Expected full doc-comment replacement')
        require(bridge.count(new) == 1 and bridge.count(old) == 0, 'Doc-comment replacement is not unique')
        original = bridge.replace(new,old,1)
        require(sha(original) == evidence['bridge_sha256'] and len(original) == evidence['bridge_size_bytes'],
                'Changes extend beyond the one recorded doc comment')
    else:
        require(sha(bridge) == evidence['bridge_sha256'] and len(bridge) == evidence['bridge_size_bytes'], 'Bridge bytes differ from verified record')
    require([r['module'] for r in refs['files']] == ['ErdosProblems.Erdos229','ErdosProblems.Erdos511'], 'Changed dependency order')
    require(refs['mathlib_commit'] == evidence['mathlib_commit'] and refs['lean_toolchain'] == evidence['lean_toolchain'], 'Environment records differ')
    require([t['name'] for t in evidence['theorems']] == ['JSP410Closed.arbitrarily_many_large_closed_components',
            'JSP410Closed.not_uniformly_bounded_closed_components'], 'Both exact final theorem names are required')
    return refs, evidence, bridge

def command_plan(refs, lean_bin, output):
    stages = []
    for module in [r['module'] for r in refs['files']] + ['JSP410ClosedBridge']:
        rel = module.replace('.','/')
        stages.append({'module':module,'stage':'compile','command':[str(tool(lean_bin,'lean')),'-j1','-M8192','-o',str(output/'build'/(rel+'.olean')),rel+'.lean']})
    stages.append({'module':'JSP410ClosedBridge','stage':'replay','command':[str(tool(lean_bin,'leanchecker')),'--verbose','JSP410ClosedBridge']})
    return stages

def parse_axioms(text, names):
    reports = {}
    for match in re.finditer(r"'([^']+)' (?:depends on axioms:\s*\[([^]]*)\]|does not depend on any axioms)",text,re.S):
        name = match[1]
        if name not in names: continue
        require(name not in reports, 'Duplicate axiom report: '+name)
        axioms = []
        for token in re.split(r',\s*(?![^{}]*\})',match[2] or ''):
            if not token.strip(): continue
            atom = re.fullmatch(r'([A-Za-z_][A-Za-z_0-9]*(?:\.[A-Za-z_][A-Za-z_0-9]*)*)(?:\.\{[^{}]+\})?',token.strip())
            require(atom is not None,'Malformed printed axiom')
            axioms.append(atom[1])
        require(len(axioms)==len(set(axioms)) and set(axioms)<=STANDARD,'Nonstandard or repeated target axiom')
        reports[name]={'raw':match[0],'axioms':axioms}
    require(set(reports)==set(names),'Missing final theorem axiom report')
    return reports

class RejectRedirects(urllib.request.HTTPRedirectHandler):
    def redirect_request(self,req,fp,code,msg,headers,newurl): return None

def download(row):
    with urllib.request.build_opener(RejectRedirects()).open(row['url'],timeout=60) as response:
        require(response.status==200 and response.geturl()==row['url'],'Response differs from exact pinned URL')
        data=response.read(row['size_bytes']+1)
    require(len(data)==row['size_bytes'] and sha(data)==row['sha256'],'Downloaded hash/size mismatch')
    require(hashlib.sha1(b'blob '+str(len(data)).encode()+b'\0'+data).hexdigest()==row['git_blob_sha1'],'Downloaded Git blob mismatch')
    return data

def execute(refs,evidence,bridge,mathlib,lean_bin,output):
    require(not output.exists(),'Output exists; choose a fresh directory')
    require(not output.is_relative_to(mathlib) and not output.is_relative_to(HERE),'Output must be outside Mathlib and this package')
    lean,checker=tool(lean_bin,'lean'),tool(lean_bin,'leanchecker')
    require(lean.is_file() and checker.is_file(),'Explicit Lean/checker binaries missing')
    env=os.environ.copy();env['LEAN_NUM_THREADS']='1'
    env['PATH']=str(lean_bin)+os.pathsep+env.get('PATH','')
    env.pop('LEAN_SYSROOT',None);env.pop('LEAN_SRC_PATH',None)
    head=subprocess.check_output(['git','-C',str(mathlib),'rev-parse','HEAD'],text=True,env=env).strip()
    require(head==refs['mathlib_commit'],'Wrong Mathlib commit')
    require((mathlib/'lean-toolchain').read_text().strip()==refs['lean_toolchain'],'Wrong toolchain file')
    version=subprocess.check_output([str(lean),'--version'],text=True,env=env).strip()
    require(re.search(r'\bversion\s+4\.33\.0(?:[,\s]|$)',version) is not None,'Actual Lean is not pinned 4.33.0')
    caches=[mathlib/'.lake/build/lib/lean',*sorted((mathlib/'.lake/packages').glob('*/.lake/build/lib/lean'))]
    require((caches[0]/'Mathlib.olean').is_file(),'Mathlib cache missing')
    output.mkdir(parents=True,exist_ok=False)
    src,build,logs=output/'src',output/'build',output/'logs'
    src.mkdir();build.mkdir();logs.mkdir()
    env['LEAN_PATH']=os.pathsep.join(map(str,[build,src,*caches]))
    runtime={p.name:sha(p.read_bytes()) for p in [lean,checker,*sorted(lean_bin.glob('*.dll'))]}
    package_files=['verify.py','upstream.json','verification.json','JSP410ClosedBridge.lean']
    if (HERE/'bridge-source-revision.json').exists(): package_files.append('bridge-source-revision.json')
    package={n:sha((HERE/n).read_bytes()) for n in package_files}
    result={'status':'running','started_utc':datetime.now(timezone.utc).isoformat(),'lean_version':version,'mathlib_commit':head,
            'lean_toolchain':refs['lean_toolchain'],'LEAN_NUM_THREADS':'1','runtime_file_sha256':runtime,'package_sha256':package,
            'fresh_custom_compilation':True,'private_object_reuse':False,'sources':[],'events':[],
            'historical_verification_bridge_sha256':evidence['bridge_sha256'],
            'scope':'Three custom compilations; both final theorem axiom reports; bridge-only kernel replay against imported read-only caches.'}
    save(output/'result.json',result)
    try:
        for row in refs['files']:
            data=download(row);rel=row['module'].replace('.','/')+'.lean';target=src/rel
            target.parent.mkdir(parents=True,exist_ok=True)
            with target.open('xb') as stream: stream.write(data)
            result['sources'].append({'module':row['module'],'relative_file':rel,'sha256':sha(data),'bytes':len(data),'download_url':row['url'],'git_blob_sha1':row['git_blob_sha1']})
            save(output/'result.json',result)
        with (src/'JSP410ClosedBridge.lean').open('xb') as stream: stream.write(bridge)
        result['sources'].append({'module':'JSP410ClosedBridge','relative_file':'JSP410ClosedBridge.lean','sha256':sha(bridge),'bytes':len(bridge)})
        for index,stage in enumerate(command_plan(refs,lean_bin,output)):
            cmd=stage['command']
            if '-o' in cmd: Path(cmd[cmd.index('-o')+1]).parent.mkdir(parents=True,exist_ok=True)
            log=logs/f'{index:02d}-{stage["module"]}.{stage["stage"]}.log'
            event={**stage,'exit_code':None,'log':log.relative_to(output).as_posix(),'start_utc':datetime.now(timezone.utc).isoformat()}
            result['events'].append(event);save(output/'result.json',result)
            print(stage['stage'],stage['module'],flush=True);started=time.monotonic()
            with log.open('xb') as stream:
                try: code=subprocess.run(cmd,cwd=src,env=env,stdout=stream,stderr=subprocess.STDOUT).returncode
                except OSError as error:
                    event['launch_error']=repr(error);stream.write(repr(error).encode('utf-8'));code=None
            event.update(exit_code=code,seconds=round(time.monotonic()-started,3),end_utc=datetime.now(timezone.utc).isoformat(),log_sha256=sha(log.read_bytes()))
            save(output/'result.json',result)
            require(code==0,stage['stage']+' failed: '+stage['module'])
            text=log.read_text(encoding='utf-8',errors='replace')
            if stage['stage']=='compile':
                obj=Path(cmd[cmd.index('-o')+1]);require(obj.is_file() and obj.stat().st_size>0,'Missing/empty compiled object')
                event['object_sha256']=sha(obj.read_bytes())
                if stage['module']=='JSP410ClosedBridge':
                    reports=parse_axioms(text,[t['name'] for t in evidence['theorems']])
                    result['target_axioms']={n:r['axioms'] for n,r in reports.items()}
                    result['target_axiom_reports_raw']={n:r['raw'] for n,r in reports.items()}
            else:
                selected=re.findall(r'(?m)^replaying ([A-Za-z_0-9.]+)\s*$',text)
                require(selected==['JSP410ClosedBridge'],'Checker selection is not exactly the bridge')
                result['checker_selected_modules']=selected
            save(output/'result.json',result)
        for row in result['sources']: require(sha((src/row['relative_file']).read_bytes())==row['sha256'],'Source changed')
        for event in result['events']:
            require(sha((output/event['log']).read_bytes())==event['log_sha256'],'Log changed')
            if 'object_sha256' in event: require(sha(Path(event['command'][event['command'].index('-o')+1]).read_bytes())==event['object_sha256'],'Compiled object changed')
        for name,digest in runtime.items(): require(sha((lean_bin/name).read_bytes())==digest,'Runtime changed')
        for name,digest in package.items(): require(sha((HERE/name).read_bytes())==digest,'Submission package changed')
        require(subprocess.check_output(['git','-C',str(mathlib),'rev-parse','HEAD'],text=True,env=env).strip()==head,'Mathlib HEAD changed')
        result['build_artifacts']=[{'path':p.relative_to(output).as_posix(),'sha256':sha(p.read_bytes()),'bytes':p.stat().st_size} for p in sorted(build.rglob('*')) if p.is_file()]
        result['status']='fresh_helper_run_complete'
    except Exception as error:
        result['status'],result['error']='failed',repr(error)
        raise
    finally:
        result['ended_utc']=datetime.now(timezone.utc).isoformat();save(output/'result.json',result)
    return result

def main():
    p=argparse.ArgumentParser(description=__doc__)
    mode=p.add_mutually_exclusive_group();mode.add_argument('--plan',action='store_true');mode.add_argument('--execute',action='store_true')
    p.add_argument('--mathlib',type=Path,required=True,help='Pinned cached checkout, used read-only')
    p.add_argument('--lean-bin',type=Path,required=True,help='Installed Lean 4.33.0 bin directory')
    p.add_argument('--output',type=Path,required=True,help='Fresh output outside Mathlib and this package')
    args=p.parse_args();refs,evidence,bridge=load()
    mathlib,lean_bin,output=(x.resolve() for x in (args.mathlib,args.lean_bin,args.output))
    if not args.execute:
        print(json.dumps({'status':'plan_only_not_executed','stages':command_plan(refs,lean_bin,output),'source_directory':str(output/'src'),
                          'LEAN_NUM_THREADS':'1','network_used':False,'lean_started':False},indent=2));return
    result=execute(refs,evidence,bridge,mathlib,lean_bin,output)
    print(json.dumps({'status':result['status'],'result_file':str(output/'result.json')},indent=2))

if __name__=='__main__':
    try: main()
    except (ValueError,OSError,subprocess.SubprocessError) as error:
        print(str(error),file=sys.stderr);raise SystemExit(1)
