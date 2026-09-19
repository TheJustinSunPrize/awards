"""逐个使用 Lean 内核重新检查证据模块，并保存源码摘要和结果。"""
import argparse
import concurrent.futures
import hashlib
import json
import os
from pathlib import Path
import shutil
import subprocess
import sys
import time

ROOT = Path(__file__).resolve().parents[1]


def main():
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument('manifest')
    parser.add_argument('--workers',type=int,default=4)
    parser.add_argument('--timeout',type=int,default=600)
    parser.add_argument('--trust',type=int,choices=(0,1),default=1)
    parser.add_argument('--only',action='append',default=[])
    args=parser.parse_args()
    manifest=ROOT/args.manifest
    modules=json.loads(manifest.read_text(encoding='utf-8'))
    if args.only:
        wanted=set(args.only)
        missing=wanted-{m['module'] for m in modules}
        if missing:
            parser.error('清单中不存在这些模块：'+', '.join(sorted(missing)))
        modules=[m for m in modules if m['module'] in wanted]
    bindir=ROOT/'.tools/lean-4.34.0-windows/bin'
    env=os.environ.copy()
    if (bindir/'lean.exe').exists():
        env['PATH']=str(bindir)+os.pathsep+env['PATH']
    lean=shutil.which('lean',path=env['PATH'])
    lake=shutil.which('lake',path=env['PATH'])
    if not lean or not lake:
        raise SystemExit('请先安装 lean-toolchain 指定的 Lean 版本。')
    env['MATHLIB_CACHE_DIR']=str(ROOT/'.work/cache')
    env['LEAN_PATH']=subprocess.check_output(
        [lake,'env',sys.executable,'-c','import os; print(os.environ["LEAN_PATH"])'],
        cwd=ROOT,env=env,text=True).strip()
    reports=ROOT/'.work/verification'/manifest.stem
    reports.mkdir(parents=True,exist_ok=True)
    def verify(item):
        source=ROOT/item['path']
        out=ROOT/'.lake/build/lib/lean'/Path(item['module'].replace('.','/')).with_suffix('.olean')
        out.parent.mkdir(parents=True,exist_ok=True)
        record=reports/(source.stem+'.json')
        digest=hashlib.sha256(source.read_bytes()).hexdigest()
        start=time.monotonic()
        proc=subprocess.run([lean,'-j','1',f'--trust={args.trust}',str(source),'-o',str(out)],
                            cwd=ROOT,env=env,capture_output=True,timeout=args.timeout)
        (reports/(source.stem+'.log')).write_bytes(proc.stdout+proc.stderr)
        result={'module':item['module'],'source_sha256':digest,'exit_code':proc.returncode,
                'seconds':time.monotonic()-start,'trust':args.trust}
        record.write_text(json.dumps(result,indent=2),encoding='utf-8')
        return result
    results=[]
    with concurrent.futures.ThreadPoolExecutor(max_workers=args.workers) as pool:
        futures={pool.submit(verify,m):m['module'] for m in modules}
        for future in concurrent.futures.as_completed(futures):
            try:
                result=future.result()
            except Exception as exc:
                result={'module':futures[future],'exit_code':-1,'error':str(exc)}
            results.append(result)
            print(f'{len(results)}/{len(modules)} {result["module"]} '+
                  ('通过' if result['exit_code']==0 else '失败'),flush=True)
    result_name='result-filtered.json' if args.only else 'result.json'
    (reports/result_name).write_text(json.dumps(results,indent=2),encoding='utf-8')
    if any(r['exit_code'] for r in results):
        raise SystemExit(1)


if __name__=='__main__':
    main()
