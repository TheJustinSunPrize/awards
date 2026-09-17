# Independent-implementation check

The checked target is `JSP404.verified_cases_exact`, containing the five-point equality, the exact values for six through eight points, and the equality `alpha(2^n)=(1-1/n)*pi` for every integer `n >= 2`. Exporting this theorem includes the dependencies of both our lower proofs and the separately attributed upstream upper constructions.

Tools are built from clean pinned source trees:

- [lean4export](https://github.com/leanprover/lean4export/tree/076e8e57707e813375e8f9da8bf989799ace9680), tag v4.34.0, commit `076e8e57707e813375e8f9da8bf989799ace9680`, built with Lean 4.34.0 using `lake build`.
- [Nanoda](https://github.com/ammkrn/nanoda_lib/tree/4c544ed4099c8227f07d5de77ad1e69fb0740a27), version 0.4.17, commit `4c544ed4099c8227f07d5de77ad1e69fb0740a27`, built using `cargo build --release --locked`.

After `python verify.py`, run:

```sh
python verify_independent.py --exporter /path/to/lean4export --nanoda /path/to/nanoda_bin --exporter-source /path/to/lean4export-source --nanoda-source /path/to/nanoda-source
```

The script verifies source revisions and proof hashes; exports the selected theorem's dependency closure; checks it with Nanoda; prints the theorem and the actual point/angle/extremal definitions; and rejects every axiom except `propext`, `Classical.choice`, and `Quot.sound`.

Two negative controls exercise rejection: replace the final theorem's proof with the natural-number literal zero, and replace the theorem with an unpermitted axiom of the same name and type. The script requires semantic type-check and axiom-policy failures, respectively, not merely a parser failure.

The hash-linked record is `verification/independent-result.json`. Large exports and deliberately invalid controls stay in the ignored `.independent-check/` directory. The exported format is 3.1.0.

This is an independent checker implementation run by the submitter, not independent-person review or official verification. No network-isolated build, official acceptance, or prize entitlement is claimed.
