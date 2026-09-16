"""Check completeness and allowed dependencies in actual Lean axiom reports."""
from pathlib import Path
import re

root = Path(__file__).resolve().parent / "replay"
expected = {"JSP692." + n for n in (
    "transversal_contains_edge", "square_matrix_bound", "exists_maximal_only_edge",
    "edge_disjoint_of_independent", "edge_meets_only_set_at_point",
    "rank_le_twice_intersection_bound_add_one", "large_intersection_nat",
    "large_intersection_one_third", "jsp000692_question_two")}
allowed = {"propext", "Classical.choice", "Quot.sound"}
for name in ("axioms.log", "standalone.log"):
    log = (root / name).read_text()
    found = {k: {v.strip() for v in vals.split(",") if v.strip()}
             for k, vals in re.findall(
                 r"'([^']+)' depends on axioms:\s*\[([^\]]*)\]", log)}
    if set(found) != expected:
        raise SystemExit(f"FAIL {name}: missing or unexpected axiom reports")
    if any(values - allowed for values in found.values()):
        raise SystemExit(f"FAIL {name}: unexpected axiom dependency")
    if re.search(r"\berror:|sorryAx|declaration uses .sorry.", log):
        raise SystemExit(f"FAIL {name}: compiler error or admitted proof")
print("PASS: all nine declarations have only permitted standard dependencies in both reports.")
