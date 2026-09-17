#!/usr/bin/env python3
"""Run reproducible finite experiments, NOT a universal proof verification."""
from __future__ import annotations

import argparse
import csv
import json
import platform
import sys
from datetime import datetime, timezone
from pathlib import Path
from time import perf_counter

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT / "src"))
from construction import admissible_primes, check_construction, construct


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--min-k", type=int, default=9)
    parser.add_argument("--max-k", type=int, default=300)
    parser.add_argument("--prime-mode", choices=("largest", "all"), default="all")
    parser.add_argument("--output", type=Path, default=ROOT / "runs" / "latest")
    args = parser.parse_args()
    if args.min_k < 9 or args.max_k < args.min_k:
        parser.error("requires 9 <= min-k <= max-k")
    start = perf_counter()
    rows, skipped = [], []
    for k in range(args.min_k, args.max_k + 1):
        ps = admissible_primes(k)
        if not ps:
            skipped.append(k)
            continue
        if args.prime_mode == "largest":
            ps = ps[-1:]
        rows.extend(check_construction(construct(k, p)) for p in ps)
    failed = [row for row in rows if not row["passed"]]
    summary = {
        "utc_time": datetime.now(timezone.utc).isoformat(),
        "python": platform.python_version(),
        "min_k": args.min_k, "max_k": args.max_k, "prime_mode": args.prime_mode,
        "parameter_pairs_checked": len(rows),
        "distinct_k_checked": len({row["k"] for row in rows}),
        "parameters_skipped_no_admissible_prime": skipped,
        "failed_pairs": [[row["k"], row["p"]] for row in failed],
        "left_cases": sum(row["direction"] == "left" for row in rows),
        "right_cases": sum(row["direction"] == "right" for row in rows),
        "elapsed_seconds": round(perf_counter() - start, 6),
        "finite_experiments_passed": not failed,
        "lean_checked": False,
        "universal_proof_certified": False,
        "priority_cleared": False,
        "note": "Skipped k are not passes. Finite tests are not a universal proof or Lean verification."
    }
    args.output.mkdir(parents=True, exist_ok=True)
    (args.output / "summary.json").write_text(json.dumps(summary, indent=2) + "\n", encoding="utf-8")
    with (args.output / "cases.jsonl").open("w", encoding="utf-8") as out:
        for row in rows:
            out.write(json.dumps(row) + "\n")
    with (args.output / "cases.csv").open("w", encoding="utf-8", newline="") as out:
        fields = ["k", "p", "L", "m", "residue", "cutoff", "n", "direction", "exception_offset", "passed"]
        writer = csv.DictWriter(out, fieldnames=fields, extrasaction="ignore")
        writer.writeheader()
        writer.writerows(rows)
    print(json.dumps(summary, indent=2))
    return 1 if failed else 0


if __name__ == "__main__":
    raise SystemExit(main())
