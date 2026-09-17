# Independent implementation check

## English

The verification route exports only the final theorem and its transitive
dependencies with lean4export, then checks the complete export with Nanoda.
Both tools must be built from clean sources at these exact revisions:

- [lean4export](https://github.com/leanprover/lean4export/tree/076e8e57707e813375e8f9da8bf989799ace9680)
  `076e8e57707e813375e8f9da8bf989799ace9680`.
- [Nanoda](https://github.com/ammkrn/nanoda_lib/tree/4c544ed4099c8227f07d5de77ad1e69fb0740a27)
  `4c544ed4099c8227f07d5de77ad1e69fb0740a27`.

Run the local verifier first, then:

```sh
python verify_independent.py --exporter /path/to/lean4export \
  --nanoda /path/to/nanoda_bin --exporter-source /path/to/lean4export-source \
  --nanoda-source /path/to/nanoda-source --num-threads 1
```

The script checks tool-source revisions and tracked-source cleanliness,
source hashes, export versions, the complete positive proof, and both controls:

1. Replace the final theorem proof by a literal natural zero: typechecking must fail.
2. Replace the final theorem by an unpermitted axiom: the axiom whitelist must reject it.

Only `propext`, `Classical.choice`, and `Quot.sound` are permitted, with hard
errors for other axioms. Exports and invalid controls stay outside tracked
files. The result records hashes, versions, positive declaration count,
negative-control outcomes, and the expanded final statement/definitions.

An independent implementation is used, but the operator is the submitter.
These checks were not network-isolated and do not substitute for designated
official review or external mathematical assessment.
