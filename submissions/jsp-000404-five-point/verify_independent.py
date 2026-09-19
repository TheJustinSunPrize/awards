"""Export and externally check the final theorem, including rejection controls.
Supply binaries built from the pinned sources in INDEPENDENT.md.
Large exports and deliberately invalid controls stay in .independent-check/.
"""
from pathlib import Path
from datetime import datetime, timezone
import argparse, hashlib, json, re, shutil, subprocess

ROOT = Path(__file__).resolve().parent
TARGET = 'SendovFivePointPlane.finite_set_large_angle'
EXPORTER_REV = 'bae5a4a9c1cddec1fd97a82907cb5be9da884b2d'
CHECKER_REV = '4c544ed4099c8227f07d5de77ad1e69fb0740a27'
AXIOMS = ['propext', 'Classical.choice', 'Quot.sound']

def sha(path):
    with path.open('rb') as f:
        return hashlib.file_digest(f, 'sha256').hexdigest()

def write_json(path, value):
    path.write_text(json.dumps(value, indent=2) + '\n', encoding='utf-8', newline='\n')

def source_revision(path, expected):
    revision = subprocess.check_output(['git', 'rev-parse', 'HEAD'], cwd=path, text=True).strip()
    dirty = subprocess.check_output(['git', 'status', '--porcelain', '--untracked-files=no'],
                                    cwd=path, text=True).strip()
    if revision != expected or dirty:
        raise RuntimeError('Tool source revision/cleanliness mismatch: ' + str(path))

def main():
    parser = argparse.ArgumentParser(description=__doc__)
    for name in ['exporter', 'nanoda', 'exporter-source', 'nanoda-source']:
        parser.add_argument('--' + name, required=True, type=Path)
    args = parser.parse_args()
    source_revision(args.exporter_source, EXPORTER_REV)
    source_revision(args.nanoda_source, CHECKER_REV)
    lake = shutil.which('lake')
    if not lake:
        raise RuntimeError('Lean 4.19 / Lake must be on PATH')
    local = json.loads((ROOT / 'verification/result.json').read_text(encoding='utf-8'))
    proof_files = {n: h for n, h in local['files'].items() if n.endswith('.lean')}
    for name, digest in proof_files.items():
        if sha(ROOT / name) != digest:
            raise RuntimeError('Proof changed since local verification: ' + name)
    subprocess.run([lake, 'build'], cwd=ROOT, check=True)
    scratch = ROOT / '.independent-check'
    scratch.mkdir(exist_ok=True)
    out = ROOT / 'verification'
    export = scratch / 'final.ndjson'
    with export.open('wb') as f:
        subprocess.run([lake, 'env', str(args.exporter.resolve()), 'SendovFivePointPlane',
                        '--', TARGET], cwd=ROOT, stdout=f, check=True)
    with export.open(encoding='utf-8') as f:
        meta = json.loads(next(f))['meta']
    if meta['lean']['version'] != '4.19.0' or meta['format']['version'] != '3.1.0':
        raise RuntimeError('Unexpected export metadata')
    config = dict(export_file_path=str(export), use_stdin=False, permitted_axioms=AXIOMS,
                  unpermitted_axiom_hard_error=True, unsafe_permit_all_axioms=False,
                  num_threads=4, nat_extension=True, string_extension=True,
                  print_axioms=True, print_success_message=True, pp_to_stdout=True,
                  unknown_pp_declar_hard_error=True,
                  pp_declars=[TARGET, 'SendovFivePointPlane.Point',
                              'EuclideanGeometry.angle', 'InnerProductGeometry.angle'])
    config_path = scratch / 'config.json'
    def check(label, path, positive):
        write_json(config_path, dict(config, export_file_path=str(path)))
        result = subprocess.run([str(args.nanoda.resolve()), str(config_path)], cwd=ROOT,
                                stdout=subprocess.PIPE, stderr=subprocess.STDOUT,
                                encoding='utf-8', timeout=600)
        log = out / ('nanoda-' + label + '.log')
        log.write_text(result.stdout, encoding='utf-8', newline='\n')
        count = None
        if positive:
            match = re.search(r'Checked (\d+) declarations with no errors', result.stdout)
            if result.returncode or not match or TARGET not in result.stdout:
                raise RuntimeError('External proof check failed: ' + log.name)
            count = int(match.group(1))
        else:
            if result.returncode == 0:
                raise RuntimeError('Checker accepted negative control: ' + label)
            if label == 'wrong-proof' and 'self.def_eq(u, v)' not in result.stdout:
                raise RuntimeError('Wrong-proof control failed for an unexpected reason')
            if label == 'unpermitted-axiom' and 'unpermitted axiom' not in result.stdout.lower():
                raise RuntimeError('Axiom control failed for an unexpected reason')
        print(label + ': exit ' + str(result.returncode), flush=True)
        return dict(exit_code=result.returncode, declarations=count, log=log.name,
                    log_sha256=sha(log), input_sha256=sha(path))
    success = check('final', export, True)
    bad_proof, bad_axiom = scratch / 'wrong-proof.ndjson', scratch / 'unpermitted-axiom.ndjson'
    names, zero, changed = {0: ''}, None, 0
    with export.open(encoding='utf-8') as src, \
            bad_proof.open('w', encoding='utf-8', newline='\n') as dst_proof, \
            bad_axiom.open('w', encoding='utf-8', newline='\n') as dst_axiom:
        for line in src:
            obj = json.loads(line)
            if 'str' in obj and 'in' in obj:
                node = obj['str']; prefix = names[node['pre']]
                names[obj['in']] = (prefix + '.' if prefix else '') + node['str']
            elif 'num' in obj and 'in' in obj:
                node = obj['num']; prefix = names[node['pre']]
                names[obj['in']] = (prefix + '.' if prefix else '') + str(node['i'])
            if obj.get('natVal') == '0': zero = obj['ie']
            thm = obj.get('thm')
            if thm and names.get(thm['name']) == TARGET:
                if zero is None: raise RuntimeError('No zero literal for negative control')
                changed += 1
                dst_proof.write(json.dumps({'thm': dict(thm, value=zero)}) + '\n')
                new_axiom = {k: thm[k] for k in ['name', 'levelParams', 'type']}
                new_axiom['isUnsafe'] = False
                dst_axiom.write(json.dumps({'axiom': new_axiom}) + '\n')
            else:
                dst_proof.write(line); dst_axiom.write(line)
    if changed != 1: raise RuntimeError('Final theorem not uniquely found')
    negative_proof = check('wrong-proof', bad_proof, False)
    negative_axiom = check('unpermitted-axiom', bad_axiom, False)
    write_json(out / 'nanoda-config.json', dict(config, export_file_path='final.ndjson'))
    record = dict(checked_at_utc=datetime.now(timezone.utc).isoformat(), target=TARGET,
                  proof_files=proof_files, export_metadata=meta,
                  exporter_commit=EXPORTER_REV, nanoda_commit=CHECKER_REV,
                  exporter_binary_sha256=sha(args.exporter), nanoda_binary_sha256=sha(args.nanoda),
                  export_bytes=export.stat().st_size, permitted_axioms=AXIOMS,
                  unsafe_permit_all_axioms=False, unpermitted_axiom_hard_error=True,
                  independent_implementation=True, independent_operator=False,
                  official_verification=False, network_isolated=False,
                  positive=success, wrong_proof=negative_proof, unpermitted_axiom=negative_axiom,
                  script_sha256=sha(Path(__file__)), config_sha256=sha(out / 'nanoda-config.json'))
    write_json(out / 'independent-result.json', record)

if __name__ == '__main__': main()
