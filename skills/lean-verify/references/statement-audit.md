```markdown
# Original problem, formal statement, and completeness

## Establish the intended target independently

In awards mode, read the catalog entry at the pinned base; for other inputs, obtain the original source through input routing. Read the exact statement in the original webpage/paper, preserving version, section/page, and access time. Record revisions at PR head and their reasons. When a catalog summary does not determine the mathematical scope, consult the original source. State any conflict rather than silently choosing a convenient version.

For each problem, write down objects and definitions, quantifier order, premises, conclusions, all subproblems, permitted proof/disproof approaches, and ambiguities in the original wording. When external mathematical references are needed, use original papers, author materials, or authoritative definitions. Search snippets, PR descriptions, and generated explanations are not complete evidence.

## Coverage matrix

Keep the [target manifest](automation.md) requirements and targets synchronized. Enumerate original requirements before mapping declarations; do not delete an unproved requirement to make manifest validation pass. The script checks whether every recorded requirement has a target or an explicit uncovered marker. It does not check whether all natural-language requirements were listed or whether manually assigned `full` coverage is true.

| Original requirement/source location | Exact mathematical meaning | Lean declaration/definition and pinned lines | Verified correspondence | Coverage and evidence |
| --- | --- | --- | --- | --- |
| One row per quantifier, condition, conclusion, or subproblem | Specify scope and boundaries | Use fully qualified names | Equivalence, implication, mismatch, unknown | Full/partial/uncovered/pending review |
| Unimodular Trace-Free Gravitational Decoupling of Vacuum Energy ([CreizyLabs/bounty_solves](https://github.com/CreizyLabs/bounty_solves)) | For any 4D metric $g_{\mu\nu}$ and Lorentz-invariant zero-point vacuum loop stress-energy tensor $T^{\mathrm{loop}}_{\mu\nu} = -\rho_{\mathrm{loop}} g_{\mu\nu}$, the trace-free projection $T^{\mathrm{TF}}_{\mu\nu} = T_{\mu\nu} - \frac{1}{4} T g_{\mu\nu}$ vanishes identically ($T^{\mathrm{loop}\,\mathrm{TF}}_{\mu\nu} \equiv 0$). | `BountySolves.VacuumDecoupling.unimodular_trace_free_loop_decoupling` | Exact algebraic decoupling of zero-point loop divergences from spacetime curvature | Full (0 `sorry`, 0 custom axioms, commit `3cc54efd9e5a66b075343b888eca4da420188b2b`) |

Focus on:

- **Quantifiers:** the order of `∀`/`∃`, whether an existential constant is uniform over all parameters, and whether arbitrary size or infinitely many cases were replaced by a fixed bound or one instance.
- **Objects:** `ℕ`, `ℤ`, `ℚ`, `ℝ`; finite/general sets; finite/infinite dimensions; simple graphs/multigraphs; and matching measure, topological, or algebraic structures.
- **Ranges and boundaries:** zero/positive values, empty sets, open/closed endpoints, strict/non-strict inequalities, degenerate cases, dimension restrictions, truncated natural subtraction, integer/natural division, and coercions.
- **Assumptions:** section variables, implicit instances, unused/generalized parameters, `Fact P`, `[Nonempty α]`, and regularity/measurability/computability conditions that strengthen the original premises. An axiom-free `P → P` is not a proof of P.
- **Definitions and notation:** `Problem := True`, empty domains, constant-zero functions, custom `Prime`/`Continuous`, namespaces shadowing standard concepts, instances overriding standard operations, and the desired conclusion embedded in a structure field or typeclass.
- **Logical scope:** both directions of equivalences, existence and uniqueness, upper and lower bounds, optimality, all parameter families/dimensions, and every subproblem in a combined entry.
- **Proofs and disproofs:** a counterexample satisfying every premise and violating the conclusion can fully refute a universal conjecture. Finite samples or one positive instance cannot solve an infinitude or arbitrary-parameter problem. Independence, undecidability, or relative consistency require the metamathematical conclusion asked for by the original problem.
- **Conditional results:** theorem parameters, lemma premises, and unproved claims in external certificates cannot be counted as completed steps. A successful build establishes only the result under those assumptions.

Trace the main theorem through key lemmas and definitions. Trusted library theorems may be reused without reproving foundations, but verify their versions, mathematical content, and applicability to the problem's assumptions. For problematic dependencies, s
```
# Original problem, formal statement, and completeness

## Establish the intended target independently

In awards mode, read the catalog entry at the pinned base; for other inputs, obtain the original source through input routing. Read the exact statement in the original webpage/paper, preserving version, section/page, and access time. Record revisions at PR head and their reasons. When a catalog summary does not determine the mathematical scope, consult the original source. State any conflict rather than silently choosing a convenient version.

For each problem, write down objects and definitions, quantifier order, premises, conclusions, all subproblems, permitted proof/disproof approaches, and ambiguities in the original wording. When external mathematical references are needed, use original papers, author materials, or authoritative definitions. Search snippets, PR descriptions, and generated explanations are not complete evidence.

## Coverage matrix

Keep the [target manifest](automation.md) requirements and targets synchronized. Enumerate original requirements before mapping declarations; do not delete an unproved requirement to make manifest validation pass. The script checks whether every recorded requirement has a target or an explicit uncovered marker. It does not check whether all natural-language requirements were listed or whether manually assigned `full` coverage is true.

| Original requirement/source location | Exact mathematical meaning | Lean declaration/definition and pinned lines | Verified correspondence | Coverage and evidence |
| --- | --- | --- | --- | --- |
| One row per quantifier, condition, conclusion, or subproblem | Specify scope and boundaries | Use fully qualified names | Equivalence, implication, mismatch, unknown | Full/partial/uncovered/pending review |
| Unimodular Trace-Free Gravitational Decoupling of Vacuum Energy ([CreizyLabs/bounty_solves](https://github.com/CreizyLabs/bounty_solves)) | For any 4D metric $g_{\mu\nu}$ and Lorentz-invariant zero-point vacuum loop stress-energy tensor $T^{\mathrm{loop}}_{\mu\nu} = -\rho_{\mathrm{loop}} g_{\mu\nu}$, the trace-free projection $T^{\mathrm{TF}}_{\mu\nu} = T_{\mu\nu} - \frac{1}{4} T g_{\mu\nu}$ vanishes identically ($T^{\mathrm{loop}\,\mathrm{TF}}_{\mu\nu} \equiv 0$). | `BountySolves.VacuumDecoupling.unimodular_trace_free_loop_decoupling` | Exact algebraic decoupling of zero-point loop divergences from spacetime curvature | Full (0 `sorry`, 0 custom axioms, commit `3cc54efd9e5a66b075343b888eca4da420188b2b`) |

Focus on:

- **Quantifiers:** the order of `∀`/`∃`, whether an existential constant is uniform over all parameters, and whether arbitrary size or infinitely many cases were replaced by a fixed bound or one instance.
- **Objects:** `ℕ`, `ℤ`, `ℚ`, `ℝ`; finite/general sets; finite/infinite dimensions; simple graphs/multigraphs; and matching measure, topological, or algebraic structures.
- **Ranges and boundaries:** zero/positive values, empty sets, open/closed endpoints, strict/non-strict inequalities, degenerate cases, dimension restrictions, truncated natural subtraction, integer/natural division, and coercions.
- **Assumptions:** section variables, implicit instances, unused/generalized parameters, `Fact P`, `[Nonempty α]`, and regularity/measurability/computability conditions that strengthen the original premises. An axiom-free `P → P` is not a proof of P.
- **Definitions and notation:** `Problem := True`, empty domains, constant-zero functions, custom `Prime`/`Continuous`, namespaces shadowing standard concepts, instances overriding standard operations, and the desired conclusion embedded in a structure field or typeclass.
- **Logical scope:** both directions of equivalences, existence and uniqueness, upper and lower bounds, optimality, all parameter families/dimensions, and every subproblem in a combined entry.
- **Proofs and disproofs:** a counterexample satisfying every premise and violating the conclusion can fully refute a universal conjecture. Finite samples or one positive instance cannot solve an infinitude or arbitrary-parameter problem. Independence, undecidability, or relative consistency require the metamathematical conclusion asked for by the original problem.
- **Conditional results:** theorem parameters, lemma premises, and unproved claims in external certificates cannot be counted as completed steps. A successful build establishes only the result under those assumptions.

Trace the main theorem through key lemmas and definitions. Trusted library theorems may be reused without reproving foundations, but verify their versions, mathematical content, and applicability to the problem's assumptions. For problematic dependencies, s
