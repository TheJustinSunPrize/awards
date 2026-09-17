"""Read-only check of the actual compiler and dependency checkout revisions."""
from pathlib import Path
import json
import subprocess

ROOT = Path(__file__).resolve().parents[1]


def output(args):
    return subprocess.check_output(args, cwd=ROOT, text=True).strip()


def main():
    version = output(["lake", "env", "lean", "--version"])
    if "version 4.34.0" not in version:
        raise RuntimeError(f"Wrong compiler: {version}")
    manifest = json.loads((ROOT / "lake-manifest.json").read_text())
    deps = []
    for pkg in manifest["packages"]:
        path = ROOT / manifest["packagesDir"] / pkg["name"]
        actual = output(["git", "-C", str(path), "rev-parse", "HEAD"])
        if actual != pkg["rev"]:
            raise RuntimeError(f"Wrong revision for {pkg['name']}")
        if output(["git", "-C", str(path), "status", "--porcelain", "--untracked-files=no"]):
            raise RuntimeError(f"Modified tracked dependency: {pkg['name']}")
        deps.append({"name": pkg["name"], "rev": actual, "tracked_sources_clean": True})
    print(json.dumps({"lean": version, "dependencies": deps}, indent=2))


if __name__ == "__main__":
    main()
