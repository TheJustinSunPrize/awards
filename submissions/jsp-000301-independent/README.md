# JSP-000301: formalization with independent Nanoda evidence

This is a request for verification of the known counterexample 12167, 12168 to [JSP-000301](https://github.com/TheJustinSunPrize/awards/blob/f4e7173d89dfe91022a185427d63452c8ffbf6ae/problems/catalog-0301-0400.md#JSP-000301). It is not an award announcement or a first-discovery claim.

## Result and statement fidelity

`12167 = 23³` and `12168 = 2³ × 3² × 13²` are positive consecutive powerful numbers. Both are strictly between `110² = 12100` and `111² = 12321`, so neither is a square.

`JSP000301.Powerful n` requires `0 < n` and quantifies over every natural prime divisor p: `p ∣ n` implies `p² ∣ n`. Primality, divisibility, and `IsSquare` are standard mathlib predicates. There is no restriction of the prime quantifier to the four witness primes. Natural-number squares suffice for positive integers, since the square of an integer is the square of its natural absolute value.

`JSP000301.counterexample` supplies an explicit existential counterexample. `JSP000301.claim_false` negates the universal assertion directly. The separate asymptotic counting question in Erdős problem 365 is outside this submission.

## Source provenance and attribution

This proof is byte-identical to the source [publicly posted by jinkaizhang236-sketch](https://github.com/TheJustinSunPrize/awards/issues/25#issuecomment-5699218957) on September 16, 2026. SHA-256 of `JSP301.lean`: `a8dc2c9c9e2220bc2da10ae9acbaf4dee0933c59ef3e41ba6f778e9a36c9ccc7`.

The account submits AI-assisted formalization and local verification work produced with OpenAI Codex. The mathematical counterexample predates this work. The submitter has an interest in the assessment and is not a designated independent prize verifier. A submitting account is not a confirmed prize-recipient identity.

Earlier intake records include [PR 13](https://github.com/TheJustinSunPrize/awards/pull/13), [PR 17](https://github.com/TheJustinSunPrize/awards/pull/17), [Issue 25](https://github.com/TheJustinSunPrize/awards/issues/25), [PR 33](https://github.com/TheJustinSunPrize/awards/pull/33), [PR 55](https://github.com/TheJustinSunPrize/awards/pull/55), [Issue 62](https://github.com/TheJustinSunPrize/awards/issues/62), [Issues 63](https://github.com/TheJustinSunPrize/awards/issues/63) and [64](https://github.com/TheJustinSunPrize/awards/issues/64), and [Issue 82](https://github.com/TheJustinSunPrize/awards/issues/82). We have not recompiled those projects or determined their first-publication priority. This evidence applies to this source only.

## Reproduce the source

Use Lean 4.34.0 and the dependencies pinned in `lake-manifest.json`. The mathlib commit is `5ed2965256430c3649e86755f9576b54eca72435`.

```sh
bash verify.sh
bash verify_nanoda.sh
```

The first command builds the source, audits six theorems, and replays all imported and local declarations through the official kernel. The second builds pinned exporter/checker tools when they are not provided, regenerates a theorem dependency export, and checks it independently. It requires a working pinned project, Git, and Rust/Cargo when building Nanoda. Tool download/setup may require network access. Neither convenience command should be described as the organizer's full source-only sandbox procedure.

The compact `verify_nanoda.sh` wrapper is syntax-checked; its complete end-to-end run has not yet been confirmed. The recorded Nanoda results below were obtained with the underlying tools and separately reproduced, and do not constitute a claim that this convenience wrapper has passed.

## Actual verification results

- Local Lean build: exit 0, zero errors/warnings.
- Six theorem axiom audits: only `propext`, `Classical.choice`, `Quot.sound`.
- Official `leanchecker --fresh --verbose JSP301`: exit 0, including imported declarations. This uses the official Lean kernel.
- Nanoda 0.4.17: exit 0; **3,446 declarations checked without errors**, including all transitive dependencies of the two final theorems. The count includes constructors and recursors, not 3,446 user-written theorems.
- Negative control: the same export is rejected when all axioms are forbidden.

A separate macOS sandbox reproduction freshly compiled the exact proof (exit 0) and repeated all six axiom audits (exit 0), with tested network/filesystem restrictions. Its complete official-kernel replay did **not** finish: it was stopped at the 600-second wall limit after an earlier 180-second timeout. Neither timeout is claimed as a successful sandbox replay. This run reused pinned imported artifacts and used sampled RSS enforcement rather than a kernel-enforced hard memory cap. The successful baseline official-kernel replay and the independent Nanoda result above are separate runs.

The source has no placeholders, user axioms, `native_decide`, or environment modifications. It is not described as axiom-free.

### Independent implementation and fixed versions

[Nanoda](https://github.com/ammkrn/nanoda_lib/tree/4c544ed4099c8227f07d5de77ad1e69fb0740a27) is a separately implemented Rust checker; [Lean Kernel Arena](https://arena.lean-lang.org/checker/nanoda/) describes its independence. The checker source was unmodified. Its fixed commit was upstream master HEAD when retrieved; whether this satisfies the prize's current-release policy remains for the designated verifier to decide.

[lean4export v4.34.0](https://github.com/leanprover/lean4export/tree/076e8e57707e813375e8f9da8bf989799ace9680) was also unmodified. Its export loads the pinned compiled Lean environment; Nanoda then checks the exported closure rather than treating imported theorems as axioms. This does not establish a source-only rebuild of the compiler and every dependency.

The export contains 12,005,922 bytes, SHA-256 `154697e0f6327b099f7b2665f7d8a3f72ff0fa692cbe39a4882b4f40aa79d84c`. It contains exactly the three standard axiom declarations, no `sorryAx` and no `Lean.trustCompiler`. The complete compressed export and expanded local evidence have been retained by the submitting account; a permanent public archive acceptable to the operator remains to be established. The export can be regenerated with the included script.

During the recorded independent check the checker process had network access denied and CPU/wall-time limits. It did not have a memory cap. The operator's designated review has not happened. An independently implemented program is not an independent human attestation.

### Recorded checker output

```text
def JSP000301.Powerful (a._@._internal._hyg.0 : Nat) : Sort 0 :=
  And (LT.lt (OfNat.ofNat 0) a._@._internal._hyg.0)
    (forall (p : Nat),
    Nat.Prime p → Dvd.dvd p a._@._internal._hyg.0 → Dvd.dvd (HPow.hPow p (OfNat.ofNat 2))
      a._@._internal._hyg.0)

theorem JSP000301.counterexample :
  Exists
    (fun (n : Nat) =>
    And (JSP000301.Powerful n)
      (And (JSP000301.Powerful (HAdd.hAdd n (OfNat.ofNat 1)))
        (And (Not (IsSquare n)) (Not (IsSquare (HAdd.hAdd n (OfNat.ofNat 1))))))) :=
  _

theorem JSP000301.claim_false :
  Not
    (forall (n : Nat),
    JSP000301.Powerful n → JSP000301.Powerful (HAdd.hAdd n (OfNat.ofNat 1)) → Or (IsSquare n)
      (IsSquare (HAdd.hAdd n (OfNat.ofNat 1)))) :=
  _

axiom propext {a b : Sort 0} : Iff a b → Eq a b

axiom Classical.choice.{u} {α : Sort u} : Nonempty α → α

axiom Quot.sound.{u} {α : Sort u} {r : α → α → Sort 0} {a b : α} :
  r a b → Eq (Quot.mk r a) (Quot.mk r b)

Checked 3446 declarations with no errors
```

### Recorded strict checker policy

```json
{
  "export_file_path": "JSP301.ndjson",
  "use_stdin": false,
  "permitted_axioms": ["propext", "Classical.choice", "Quot.sound"],
  "unpermitted_axiom_hard_error": true,
  "unsafe_permit_all_axioms": false,
  "nat_extension": true,
  "string_extension": true,
  "num_threads": 4,
  "pp_declars": ["JSP000301.Powerful", "JSP000301.counterexample", "JSP000301.claim_false"],
  "unknown_pp_declar_hard_error": true,
  "pp_to_stdout": true,
  "pp_options": {"proofs": false, "width": 100},
  "print_success_message": true,
  "print_axioms": true
}
```

### Recorded axiom audit

```text
'JSP000301.powerful_12167' depends on axioms: [propext, Classical.choice, Quot.sound]
'JSP000301.powerful_12168' depends on axioms: [propext, Classical.choice, Quot.sound]
'JSP000301.not_isSquare_12167' depends on axioms: [propext, Classical.choice, Quot.sound]
'JSP000301.not_isSquare_12168' depends on axioms: [propext, Classical.choice, Quot.sound]
'JSP000301.counterexample' depends on axioms: [propext, Classical.choice, Quot.sound]
'JSP000301.claim_false' depends on axioms: [propext, Classical.choice, Quot.sound]
```

## Requested disposition and remaining work

Please review statement fidelity, the independent-checker evidence, and the source under the applicable submission rules. Please preserve the submitting account's distinct contribution. We do not assert that this account is the first formalizer. If multiple independent valid contributions fall within the applicable evaluation window, please consider whether joint recognition applies; we do not assume the definition or applicability of that window.

The applicable website [Selection Rules](https://www.hejustinsun.com/prize/rules) and [FAQ Q8](https://www.hejustinsun.com/prize/faq) distinguish first public visibility from processing/merge time. Stronger verification evidence does not override a valid earlier priority date.

Designated isolated reproduction, acceptance of tool versions, formal curator/verifier signatures, permanent evidence archiving, entry confirmation, and award/priority decisions remain outstanding. No completed candidate record, invented reviewer, recipient profile, award level, or payment claim is introduced. Repository CI checks record structure; it is not proof verification or an award decision.

The included original source and scripts are MIT licensed. Lean, mathlib, Nanoda, lean4export, and their dependencies retain their respective upstream licenses. Tool binaries, library sources, and the derived declaration export are not redistributed in this PR.
