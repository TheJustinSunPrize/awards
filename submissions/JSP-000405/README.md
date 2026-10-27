# JSP-000405: Lean Formalization Reference

This submission references a complete Lean 4 formalization hosted in an external repository.

## Proof Source

| Field | Value |
|-------|-------|
| Repository | https://github.com/plby/lean-proofs |
| Branch | main |
| Commit | 8822f7ddef30fadbd92e1c6ab4ed897af356af5e |
| File | `src/latest/ErdosProblems/Erdos405.lean` |
| Problem Mapping | JSP-000405 = Erdős Problem #405 |

## Original PR

This is a resubmission of administratively closed PR #4400.
The closure was for format non-compliance (containing `.lean` source files), not for any mathematical or attribution issue.

## Toolchain

- Lean: `leanprover/lean4:v4.33.0`
- Mathlib: `v4.33.0`

## Build

```bash
git clone https://github.com/plby/lean-proofs.git
cd lean-proofs
git checkout 8822f7ddef30fadbd92e1c6ab4ed897af356af5e
lake exe cache get
lake build
```
