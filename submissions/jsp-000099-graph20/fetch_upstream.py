"""Retrieve pinned external sources and reproduce the verified local adaptations.

The five upstream Lean modules are deliberately not redistributed in this PR.
Their licensing scope is awaiting clarification; this script grants no rights
to those sources. Downloads occur only when this script is explicitly invoked.
Use --source-dir for already obtained upstream files without network access.
"""
from __future__ import annotations
import argparse
import hashlib
import json
from pathlib import Path
import re
import urllib.request

ROOT = Path(__file__).resolve().parent
HEADER = """/- Local 20-vertex adaptation of PR #190, commit 4022d2df0f941a12f497d5045b75995e0cf8f883.
   Upstream formalization: jinkaizhang236-sketch / Justin Sun Prize contributors.
   Original mathematical construction: Paul W. Dyson and Brendan D. McKay.
   See THIRD_PARTY_NOTICES.md for exact reuse and changes. -/
"""


def assemble(name: str, data: bytes) -> bytes:
    if name == "RegularCertificate.lean":
        return data
    text = data.decode().replace("Erdos82Finite", "Graph20Proof").replace("Graph29", "Graph20")
    text = re.sub(r"\b29\b", "20", text)
    text = re.sub(r"\b7\b", "6", text)
    text = text.replace("536870911", "1048575")
    if name == "MaskCertificate.lean":
        from verify_witness import decode_masks
        adj = decode_masks((ROOT / "witness20.g6").read_bytes())
        block = "def adjBits (v : Fin 20) : Nat :=\n  match v.val with\n"
        block += "".join(f"  | {v} => {bits}\n" for v, bits in enumerate(adj))
        block += "  | _ => 0\n\n"
        text, count = re.subn(r"def adjBits .*?(?=def decode)", lambda _: block, text, count=1, flags=re.S)
        if count != 1:
            raise RuntimeError("Could not locate the pinned adjacency declaration")
    return (HEADER + text).encode()


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--source-dir", type=Path)
    args = parser.parse_args()
    manifest = json.loads((ROOT / "upstream-sources.json").read_text())
    outputs = []
    for item in manifest["files"]:
        name = item["name"]
        if Path(name).name != name:
            raise RuntimeError("Unexpected source filename")
        if args.source_dir:
            data = (args.source_dir / name).read_bytes()
        else:
            with urllib.request.urlopen(item["url"], timeout=60) as response:
                data = response.read()
        if hashlib.sha256(data).hexdigest() != item["source_sha256"]:
            raise RuntimeError("Upstream hash mismatch: " + name)
        outputs.append((ROOT / ".upstream" / name, data))
        if "assembled_sha256" in item:
            adapted = assemble(name, data)
            if hashlib.sha256(adapted).hexdigest() != item["assembled_sha256"]:
                raise RuntimeError("Adaptation hash mismatch: " + name)
            outputs.append((ROOT / name, adapted))
    for path, data in outputs:
        if path.exists() and path.read_bytes() != data:
            raise RuntimeError("Refusing to overwrite a different existing file: " + str(path))
    for path, data in outputs:
        path.parent.mkdir(parents=True, exist_ok=True)
        path.write_bytes(data)
    print("Verified all eight upstream source/notice hashes and five assembled Lean-module hashes.")


if __name__ == "__main__":
    main()
