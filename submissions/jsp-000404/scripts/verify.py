#!/usr/bin/env python3
"""Build the pinned project, check theorem axioms, and record source hashes.

Uses only Python's standard library. The checker does not supply mathematical
assumptions to Lean. A new directory or --clean gives a build from source.
"""

import argparse
import datetime
import hashlib
import json
from pathlib import Path
import re
import shutil
import subprocess
import sys
import time

ROOT = Path(__file__).resolve().parents[1]
EXPECTED_VERSION = "4.34.0"
EXPECTED_COMMIT = "293d5d0c0c3f3dded4688b3ccd6a33939ac5102b"
ALLOWED_AXIOMS = {"propext", "Quot.sound", "Classical.choice"}
EXPECTED_THEOREMS = {
    'JSP404.alpha_eq_of_bounds',
    'JSP404.alpha_eq_sInf',
    'JSP404.alpha_five_le_three_pi_div_four',
    'JSP404.alpha_five_lt_four_pi_div_five',
    'JSP404.alpha_five_ne_four_pi_div_five',
    'JSP404.alpha_le_maxAngle',
    'JSP404.alpha_le_of_cluster_angles',
    'JSP404.alpha_le_of_configuration',
    'JSP404.alpha_le_pi',
    'JSP404.alpha_le_self_index_upper',
    'JSP404.alpha_le_szekeres_upper',
    'JSP404.alpha_lt_pi',
    'JSP404.alpha_mono',
    'JSP404.alpha_nonneg',
    'JSP404.alpha_sum_two_pow_le_of_cluster_directions',
    'JSP404.alpha_two_pow_le_of_signed_directions',
    'JSP404.angle_circleDirection',
    'JSP404.angle_circleDirection_le',
    'JSP404.angle_grid_directions',
    'JSP404.angle_le_maxAngle',
    'JSP404.angle_le_three_pi_div_four_of_inner',
    'JSP404.angle_lower_bound_of_two_cone_edges',
    'JSP404.binaryProjection_sub',
    'JSP404.binaryProjection_sub_factor',
    'JSP404.binaryResidual_zero',
    'JSP404.bipartite_cover_weighted_bound',
    'JSP404.card_le_two_pow_of_binary_separation',
    'JSP404.card_le_two_pow_of_bipartite_cover',
    'JSP404.card_le_two_pow_of_cone_cover',
    'JSP404.centerExponent_bound',
    'JSP404.circleDirection_pi',
    'JSP404.classical_bounds_between_powers',
    'JSP404.clusterWord_card',
    'JSP404.coneGraph_colorable',
    'JSP404.cone_cover_weighted_bound',
    'JSP404.configurationMaxima_bddBelow',
    'JSP404.configurationMaxima_nonempty',
    'JSP404.equally_spaced_direction_cover',
    'JSP404.eventually_binaryProjection_angle_lt',
    'JSP404.eventually_injective_binaryProjection',
    'JSP404.eventually_injective_center_cluster',
    'JSP404.eventually_injective_perturb',
    'JSP404.exists_configuration_maxAngle_lt',
    'JSP404.exists_configuration_of_cluster_angles',
    'JSP404.exists_first_difference',
    'JSP404.exists_near_grid',
    'JSP404.exists_polar_of_second_nonneg',
    'JSP404.finset_card_le_two_pow_of_direction_cover',
    'JSP404.five_in_lower_interval',
    'JSP404.floor_pair_exponent_bound',
    'JSP404.grid_direction_angle_bounds',
    'JSP404.guaranteed_alpha',
    'JSP404.guaranteed_bddAbove',
    'JSP404.guaranteed_iff_le_alpha',
    'JSP404.guaranteed_le_pi',
    'JSP404.guaranteed_mono',
    'JSP404.guaranteed_of_direction_cover',
    'JSP404.guaranteed_pi_div_three',
    'JSP404.guaranteed_zero',
    'JSP404.hasLargeAngle_iff_le_maxAngle',
    'JSP404.hasLargeAngle_maxAngle',
    'JSP404.hasLargeAngle_mono',
    'JSP404.hasLargeAngle_of_direction_cover',
    'JSP404.hasLargeAngle_pi_div_three',
    'JSP404.hasLargeAngle_zero',
    'JSP404.housePoint_angle_le',
    'JSP404.housePoint_injective',
    'JSP404.house_angle_le',
    'JSP404.house_card',
    'JSP404.le_alpha',
    'JSP404.maxAngle_le',
    'JSP404.maxAngle_le_pi',
    'JSP404.maxAngle_mono',
    'JSP404.maxAngle_nonneg',
    'JSP404.mem_angleValues',
    'JSP404.mul_le_sub_one_of_normalized_cap',
    'JSP404.norm_circleDirection',
    'JSP404.not_guaranteed_five_four_pi_div_five',
    'JSP404.not_transcribed_lower_formula',
    'JSP404.not_two_cone_edges',
    'JSP404.perturb_angle_same_cluster',
    'JSP404.perturb_sub',
    'JSP404.perturb_sub_of_same_center',
    'JSP404.pi_div_three_le_alpha',
    'JSP404.realDigit_injective',
    'JSP404.realDigit_sub_eq_sign',
    'JSP404.realDigit_sub_ne_zero',
    'JSP404.realDigit_sub_same_base',
    'JSP404.signed_grid_direction_angle_le',
    'JSP404.signed_grid_direction_angle_le_real',
    'JSP404.source_branch_at_three',
    'JSP404.source_branch_lt_transcribed',
    'JSP404.sum_free_binary_coordinates_le',
    'JSP404.szekeres_lower_bound',
    'JSP404.szekeres_lower_bound_alpha',
    'JSP404.szekeres_upper_bound',
    'JSP404.tendsto_angle_affine',
    'JSP404.tendsto_binaryProjection_angle',
    'JSP404.tendsto_binaryProjection_direction_angle',
    'JSP404.tendsto_binaryResidual',
    'JSP404.tendsto_perturb_angle',
    'JSP404.tendsto_perturb_sub',
    'JSP404.three_center_bound',
    'JSP404.three_center_bound_small_delta',
    'JSP404.three_centers_not_all_high',
    'JSP404.three_centers_not_two_high',
    'JSP404.three_le_two_pow',
    'JSP404.three_pi_div_four_lt_four_pi_div_five',
    'JSP404.three_powers_le_five_of_not_all_high',
    'JSP404.three_powers_le_two_pow_of_at_most_one_high',
    'JSP404.transcribed_branch_at_three',
}
EXPECTED_MATHLIB = "5ed2965256430c3649e86755f9576b54eca72435"



def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--lake", help="Path to Lake; defaults to PATH, then local bundled runtime")
    parser.add_argument("--clean", action="store_true", help="Remove this package's build cache first")
    args = parser.parse_args()
    local_lake = ROOT / ".tools/lean-4.34.0-darwin_aarch64/bin/lake"
    lake = args.lake or shutil.which("lake") or (str(local_lake) if local_lake.exists() else None)
    if not lake:
        parser.error("Lake not found. Install the pinned Lean toolchain or pass --lake.")
    out = ROOT / "verification"
    out.mkdir(exist_ok=True)
    log_path = out / "build-and-axioms.log"
    started = time.monotonic()
    with log_path.open("w", encoding="utf-8") as log:
        def run(arguments):
            display = ["lake", *arguments[1:]] if arguments[0] == lake else arguments
            print("Running:", " ".join(display), flush=True)
            log.write("$ " + " ".join(display) + "\n")
            log.flush()
            result = subprocess.run(arguments, cwd=ROOT, text=True, stdout=subprocess.PIPE,
                                    stderr=subprocess.STDOUT, check=False)
            print(result.stdout, end="", flush=True)
            log.write(result.stdout)
            log.flush()
            if result.returncode:
                raise RuntimeError("Command failed with exit code " + str(result.returncode))
            return result.stdout

        version = run([lake, "env", "lean", "--version"])
        if "version " + EXPECTED_VERSION + "," not in version or EXPECTED_COMMIT not in version:
            raise RuntimeError("Unexpected Lean version or commit; use lean-toolchain.")
        if args.clean:
            shutil.rmtree(ROOT / ".lake/build", ignore_errors=True)
        manifest = json.loads((ROOT / "lake-manifest.json").read_text())
        mathlib = next(p for p in manifest["packages"] if p["name"] == "mathlib")
        if mathlib["rev"] != EXPECTED_MATHLIB:
            raise RuntimeError("Unexpected Mathlib revision in manifest")
        rev = run(["git", "-C", ".lake/packages/mathlib", "rev-parse", "HEAD"]).strip()
        if rev != EXPECTED_MATHLIB:
            raise RuntimeError("Unexpected checked-out Mathlib revision")
        source_names = set()
        for path in sorted((ROOT / "JSP404").glob("*.lean")):
            source_names.update("JSP404." + name for name in re.findall(
                r"^(?:@\[[^\]]*\]\s*)?(?:theorem|lemma)\s+([A-Za-z_][A-Za-z_0-9]*)",
                path.read_text(), re.M))
        if source_names != EXPECTED_THEOREMS:
            raise RuntimeError("Update the explicit axiom audit for changed theorem declarations")
        run([lake, "build"])
        audit = run([lake, "env", "lean", "Audit.lean"])
        axioms = {}
        for name, raw in re.findall(r"'([^']+)' depends on axioms: \[([^\]]*)\]", audit):
            axioms[name] = [item.strip() for item in raw.split(",") if item.strip()]
        for name in re.findall(r"'([^']+)' does not depend on any axioms", audit):
            axioms[name] = []
        if set(axioms) != EXPECTED_THEOREMS:
            raise RuntimeError("Missing or unexpected axiom audit entries: " + repr(set(axioms)))
        for name, dependencies in axioms.items():
            bad = set(dependencies) - ALLOWED_AXIOMS
            if bad:
                raise RuntimeError("Unapproved axiom dependency in " + name + ": " + repr(bad))
        paths = sorted((ROOT / "JSP404").glob("*.lean"))
        paths += [ROOT / name for name in
                  ("JSP404.lean", "Audit.lean", "lean-toolchain", "lakefile.toml",
                   "lake-manifest.json", "scripts/verify.py")]
        hashes = {str(path.relative_to(ROOT)): hashlib.sha256(path.read_bytes()).hexdigest()
                  for path in paths}
        report = {
            "status": "passed",
            "verified_at_utc": datetime.datetime.now(datetime.timezone.utc).isoformat(),
            "lean_version": EXPECTED_VERSION,
            "lean_commit": EXPECTED_COMMIT,
            "mathlib_commit": EXPECTED_MATHLIB,
            "audited_theorem_count": len(EXPECTED_THEOREMS),
            "clean_requested": args.clean,
            "elapsed_seconds": round(time.monotonic() - started, 3),
            "axioms": axioms,
            "source_sha256": hashes,
        }
        (out / "result.json").write_text(json.dumps(report, indent=2) + "\n", encoding="utf-8")
        print("PASS: build and all 111 theorem axiom audits succeeded.", flush=True)
        log.write("PASS: build and all 111 theorem axiom audits succeeded.\n")


if __name__ == "__main__":
    try:
        main()
    except (OSError, RuntimeError) as error:
        print("FAILED:", error, file=sys.stderr)
        sys.exit(1)
