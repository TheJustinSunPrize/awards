"""Reconstruct Lean's concrete matrix, compare its source, and verify exact orthogonality.

The Python program is a separate check, never an axiom or input trusted by Lean.
"""
from pathlib import Path
import ast, csv, gzip, hashlib, json, re

root=Path(__file__).resolve().parent
source=(root/'src/Hadamard716/CertificateData.lean').read_text()
def read(name):
    match=re.search(r'^def '+name+r'\b.*?:=\s*(.*?)(?=^def |^end )',source,re.M|re.S)
    assert match
    return ast.literal_eval(match[1].strip().replace('true','True').replace('false','False'))
top,left,dirs,bases=[read(n) for n in ['top716','left716','dirs716','bases716']]
assert len(top)==len(left)==len(dirs)==len(bases)==4
assert all(len(x)==4 for x in left+dirs+bases)
assert all(len(x)==178 for row in bases for x in row)
rows=[list(x) for x in top]
for a in range(4):
    for i in range(178):
        row=list(left[a])
        for q in range(4):
            k=(-i if dirs[a][q] else i)%178
            row.extend(bases[a][q][k:]+bases[a][q][:k])
        rows.append(row)
assert len(rows)==716 and all(len(r)==716 and set(r)<=set([-1,1]) for r in rows)
csvbytes=gzip.decompress((root/'hadamard_716.csv.gz').read_bytes())
original=[[int(v) for v in r] for r in csv.reader(csvbytes.decode().splitlines())]
assert rows==original
def masks(rs): return [sum((x==1)<<i for i,x in enumerate(r)) for r in rs]
bits=masks(rows)
checked=0
for i in range(716):
    for j in range(i):
        assert (bits[i]^bits[j]).bit_count()==358,(i,j)
        checked+=1
# Direct integer dot products on representative rows independently check the sign/distance convention.
direct_pairs=[(i,j) for i in [0,1,3,4,5,181,182,359,360,537,538,715] for j in range(716)]
for i,j in direct_pairs:
    assert sum(x*y for x,y in zip(rows[i],rows[j])) == (716 if i==j else 0)
# A single-entry corruption must invalidate the checker, while changing an entire row's sign preserves it.
assert ((bits[0]^1)^bits[1]).bit_count()!=358
assert all((((1<<716)-1)^bits[0]^bits[j]).bit_count()==358 for j in range(1,716))
report=dict(order=716,entries=716**2,distinct_row_pairs=checked,
    source_csv_sha256=hashlib.sha256(csvbytes).hexdigest(),
    lean_certificate_sha256=hashlib.sha256(source.encode()).hexdigest(),
    reconstruction_matches_csv=True,all_signs=True,all_distinct_rows_orthogonal=True,
    direct_integer_dot_checks=len(direct_pairs),negative_control_rejected=True,
    row_sign_change_control_accepted=True,
    limitation='Independent exact computation; Lean status is recorded separately.')
(root/'independent-verification.json').write_text(json.dumps(report,indent=2)+'\n')
print(json.dumps(report,indent=2))
