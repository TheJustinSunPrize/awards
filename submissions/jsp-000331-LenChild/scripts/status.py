#!/usr/bin/env python3
"""Show the latest local verification state without starting a build."""

import json
from pathlib import Path

from verify import package_hashes

PACKAGE = Path(__file__).resolve().parents[1]
output = PACKAGE / "verification-output"
report = output / "result.json"
if not report.exists():
    print("No verification run has started in this package.")
else:
    result = json.loads(report.read_text(encoding="utf-8"))
    status = result["status"]
    if result.get("package_hashes") is not None and package_hashes() != result["package_hashes"]:
        status = "stale: package sources changed; rerun verification"
    print("Status:", status)
    print("Phase:", result.get("phase", "unknown"))
    print("Started (UTC):", result["started_utc"])
    sources = json.loads((PACKAGE / "source-lock.json").read_text(encoding="utf-8"))["sources"]
    artifacts = []
    for source in sources:
        relative = source.removeprefix("FormalPantheon/BoundedGaps/").removeprefix("proof/")
        artifacts.append(PACKAGE / ".lake/build/lib/lean" / Path(relative).with_suffix(".olean"))
    print("External proof module artifacts:", sum(p.exists() for p in artifacts), "/", len(artifacts))
    if "finished_utc" in result:
        print("Finished (UTC):", result["finished_utc"])
    if "current_command" in result:
        print("Current command:", " ".join(result["current_command"]))
    if "error" in result:
        print("Error:", result["error"])
    if "axioms" in result:
        for name, axioms in result["axioms"].items():
            print(name + ": " + ", ".join(axioms))
    log = output / result.get("current_log", "build.log")
    if log.exists():
        print("\nLatest log lines (" + log.name + "):")
        with log.open("rb") as stream:
            stream.seek(max(0, log.stat().st_size - 8000))
            print("\n".join(stream.read().decode("utf-8", errors="replace").splitlines()[-10:]))
    print("\nReport:", report)
    if result["status"] == "running":
        print("A running record is not a pass; after interruption, rerun the verifier.")
