"""Regenerate and check the polynomial sign certificates in Bounds.lean.

Run from any directory with Python 3 and SymPy installed:
    python tools/generate_bounds.py

The input and output are resolved relative to this project. This script reads
the Lean source and writes tools/bounds-certificates.json; it does not modify
Lean source. The generated Lean RHS expressions can be used when rebuilding
the identities. SymPy is an auxiliary generator, not a trusted proof oracle:
`lake build Erdos700.Bounds` independently checks every identity using `ring`
and every asserted inequality using `positivity`. The boundary certificate
R_at_least_one is nonnegative; the other 32 certificates are strictly positive.
"""

from hashlib import sha256
import json
from pathlib import Path
import re

import sympy as s


def main() -> None:
    project = Path(__file__).resolve().parent.parent
    source_relative = Path("Erdos700") / "Bounds.lean"
    output_relative = Path("tools") / "bounds-certificates.json"
    source_bytes = (project / source_relative).read_bytes()
    source = source_bytes.decode("utf-8")

    a, b, c = s.symbols("a b c")
    x, y, z = s.symbols("x y z", nonnegative=True)
    sa = x + 1
    sb = 3 * sa + y
    sc = 3 * sb - sa + 1 + z
    input_symbols = {"a": a, "b": b, "c": c}
    certificate_symbols = {"x": x, "y": y, "z": z}
    certificates = []

    blocks = re.findall(
        r"theorem\s+\w+[\s\S]*?(?=\ntheorem\s|\nend Erdos700|\Z)", source
    )
    for block in blocks:
        name = re.search(r"theorem\s+(\w+)", block).group(1)
        identity = re.search(r"  have hid : (.*?) = (.*?) := by", block)
        if identity is None:
            # large_base_thresholds has a separate monotonicity proof.
            assert name == "large_base_thresholds", name
            continue
        assert "(hc : 3*b-a+1 ≤ c)" in block, name
        lhs_lean, rhs_lean = identity.groups()
        lhs = s.sympify(lhs_lean.replace("^", "**"), locals=input_symbols)
        rhs = s.sympify(rhs_lean.replace("^", "**"), locals=certificate_symbols)
        statement = re.search(r"\n    0 (<|≤) (.*?) := by", block)
        assert statement is not None, (name, "missing sign statement")
        relation, conclusion_lean = statement.groups()
        conclusion = s.sympify(conclusion_lean.replace("^", "**"), locals=input_symbols)
        assert s.expand(conclusion - lhs) == 0, (name, "statement/identity mismatch")
        assert (relation == "≤") == (name == "R_at_least_one"), name
        generated = s.expand(lhs.subs({a: sa, b: sb, c: sc}, simultaneous=True))
        polynomial = s.Poly(generated, x, y, z)
        assert s.expand(rhs - generated) == 0, (name, "identity mismatch")
        assert all(coef >= 0 for coef in polynomial.coeffs()), (
            name, "negative coefficient"
        )
        constant = polynomial.coeff_monomial(1)
        if relation == "<":
            assert constant > 0, (name, "nonpositive constant")
        else:
            assert constant >= 0, (name, "negative boundary constant")
        generated_lean_rhs = str(generated).replace("**", " ^ ").replace("*", " * ")
        certificates.append({
            "name": name,
            "source_expression": lhs_lean,
            "conclusion_relation": "0 " + relation + " expression",
            "strictly_positive": relation == "<",
            "constant_term": int(constant),
            "number_of_monomials": len(polynomial.terms()),
            "all_coefficients_nonnegative": True,
            "matches_current_lean_identity": True,
            "generated_lean_rhs": generated_lean_rhs,
        })

    assert len(certificates) == 33, len(certificates)
    report = {
        "source": source_relative.as_posix(),
        "source_sha256": sha256(source_bytes).hexdigest(),
        "hypotheses": "a>=1, b>=3a, c>=3b-a+1",
        "substitution": "a=x+1, b=3a+y, c=3b-a+1+z; x,y,z>=0",
        "certificate_count": len(certificates),
        "strict_certificate_count": sum(item["strictly_positive"] for item in certificates),
        "nonnegative_certificate_count": sum(not item["strictly_positive"] for item in certificates),
        "all_checks_passed": True,
        "certificates": certificates,
        "trust_note": "Auxiliary generation only. Lean ring and positivity check the proofs.",
    }
    (project / output_relative).write_text(
        json.dumps(report, indent=2) + "\n", encoding="utf-8", newline="\n"
    )
    print(f"Verified {len(certificates)} polynomial sign certificates: "
          f"{report['strict_certificate_count']} strict and "
          f"{report['nonnegative_certificate_count']} nonnegative.")
    print(f"Wrote {output_relative.as_posix()} without changing Lean source.")


if __name__ == "__main__":
    main()
