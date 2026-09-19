"""按依赖顺序检查全部证明，最后以 --trust=0 复核公开陈述。"""
import json
import os
from pathlib import Path
import re
import shutil
import subprocess
import sys

ROOT=Path(__file__).resolve().parents[1]


def main():
    env=os.environ.copy()
    local=ROOT/'.tools/lean-4.34.0-windows/bin'
    if (local/'lean.exe').exists():env['PATH']=str(local)+os.pathsep+env['PATH']
    env['MATHLIB_CACHE_DIR']=str(ROOT/'.work/cache')
    env['LEAN_NUM_THREADS']='2'
    lake=shutil.which('lake',path=env['PATH'])
    if not lake:raise SystemExit('未找到 lake，请先安装 lean-toolchain 中固定的工具链。')
    def run(args):
        subprocess.run(args,cwd=ROOT,env=env,check=True)
    version=subprocess.check_output([lake,'env','lean','--version'],cwd=ROOT,env=env,text=True)
    if not re.search(r'\bversion 4\.34\.0,',version):raise SystemExit('Lean 版本与锁定版本不一致。')
    print(version.strip(),flush=True)
    run([lake,'build','SendovDirectionModel','JSP404.ClassicalBounds','SunPrize.DirectionModel'])
    for stage,workers in [('base',1),('logic',2),('theory',2),('initial',2),
                          ('derived',1),('inputs-valid',2),('final',1)]:
        run([sys.executable,'-X','utf8','scripts/verify_modules.py',
             f'verification/modules/{stage}.json','--workers',str(workers)])
    reports=ROOT/'.work/verification'
    audit=subprocess.run([lake,'env','lean','-j','1','--trust=0','Audit.lean'],
                         cwd=ROOT,env=env,capture_output=True,text=True,encoding='utf-8')
    (reports/'audit.log').write_text(audit.stdout+audit.stderr,encoding='utf-8')
    if audit.returncode:raise SystemExit('总定理内核复核失败，见 .work/verification/audit.log。')
    allowed={'propext','Classical.choice','Quot.sound'}
    matches=re.findall(r"'([^']+)' depends on axioms: \[([^\]]*)\]",audit.stdout)
    expected={'SunPrize.Audit.angle_statement','SunPrize.Audit.value_statement'}
    found={}
    for name,values in matches:
        axioms={v.strip() for v in values.split(',') if v.strip()}
        if name in expected:
            if not axioms<=allowed:raise SystemExit('发现未允许的公理：'+', '.join(axioms-allowed))
            found[name]=sorted(axioms)
    if set(found)!=expected:raise SystemExit('公理审计未包含全部指定的公开定理。')
    (reports/'audit-result.json').write_text(json.dumps({'exit_code':0,'trust':0,'axioms':found},indent=2),encoding='utf-8')
    print('全部证明及公开陈述的内核复核通过。',flush=True)


if __name__=='__main__':main()
