# JSP-001007: square-block formalization

This is a separate, AI-assisted formalization contribution for JSP-001007 (Erdős #1202 / Green Problem 44). It is submitted for review, not as an announced award or a claim of first mathematical discovery or first formalization.

The canonical sources are the unchanged Lean files from `JSP001007_repair_v2.zip`, SHA-256 `43a71fde1ef97fcb51881df603fda7ac4838e387c9c423710844cae8d3cbca07`. The authoritative archive digest and source hashes are in [provenance.json](verification/provenance.json); that machine-readable record takes precedence over historical package status messages.

## Result

For every natural number `k` and every lower bound `N0`, `JSP001007.counterexamples` produces `N ≥ N0`, `k` strictly increasing odd primes with `p_i^10 < N^9`, and sets of exactly `floor(p_i/2)` forbidden residues, while more than `N/10` integers of `[1,N]` survive all the sieves. This includes `k = 0`. It proves arbitrarily large counterexamples, not a counterexample for every sufficiently large prescribed `N`.

The prime clusters come from the unbounded number of primes in intervals `[q²,(q+1)²)`, deduced from the divergence of the prime reciprocal series. See [PROOF.md](PROOF.md) and [STATEMENT.md](STATEMENT.md).

## Native reproduction

The submitter ran the complete native gate on 2026-09-16, with exit code 0:

- Lean `4.33.1`.
- Mathlib `0df444a360eaa60ab8c11dca51a86af692955474`.
- Arithmetic, PrimeBlocks, the main module, and the independently compiled whole-source standalone file all passed.
- All 14 selected transitive axiom reports contain only `propext`, `Classical.choice`, and `Quot.sound`; none contains `sorryAx`.

With elan installed, from this directory:

```sh
lake update
lake exe cache get
bash run_checks.sh
python3 -S -m unittest -v test_audits test_gate
```

The generated standalone file imports only Mathlib and includes the exact declaration bodies of all three modules. It is checked separately to avoid relying on previously compiled local proof modules. Mathlib's prebuilt dependency cache was used; this is not a from-source rebuild of every dependency.

See [VERIFICATION.md](VERIFICATION.md) for limitations, native logs, and the distinction between submitter reproduction and independent prize verification.

## Attribution and related submissions

The prize catalog and [Erdős problem page](https://www.erdosproblems.com/1202) already attribute the negative mathematical answer to Liam Price and GPT-5.4 Pro. That attribution is preserved. This submission does not establish a new negative answer, priority, or award eligibility, and it does not claim to have compared every step with the original Overleaf proof.

The earlier [PR #107](https://github.com/TheJustinSunPrize/awards/pull/107) and [recipient recommendation #104](https://github.com/TheJustinSunPrize/awards/issues/104) concern a different submitter. They are explicitly disclosed for duplicate and attribution review. The present contribution was provided as a separate local source package; it is not an update to that submitter's PR. No code from that PR has been copied into this package.

The proposed formalization recipient remains `RECIPIENT-JSP001007-SQUAREBLOCKS-A`, pending written confirmation and curator review. The submitter ran the automated verification with AI assistance; this is not an independent human review signature. Independent checker review, statement review, and the committee's eligibility decision remain pending.

The submission's code is contributed under the repository's [MIT license](../../LICENSE). No third-party dependency binaries or source trees are redistributed here. Mathlib, Lean and other dependency licenses remain with their respective projects.
