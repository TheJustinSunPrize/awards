# Candidate review narrative

## English

This candidate concerns JSP-000513 / Erdős Problem #632, the question of whether simultaneous scaling of the available-list size and the required number of colors preserves list multicolorability.

Dvořák, Hu, and Sereni gave a negative answer by constructing a finite graph that is 4-choosable but not (8:2)-choosable:

Z. Dvořák, X. Hu, J.-S. Sereni, *A 4-choosable graph that is not (8:2)-choosable*, Advances in Combinatorics (2019), 2019:5, https://doi.org/10.19086/aic.10811.

A public Lean 4 formalization of this construction is available at:

https://github.com/TonyMaYiXuan/jsp-000513-lean

The principal theorem is `JSP513.main`; the repository also contains the explicitly finite existential form `JSP513.exists_finite_counterexample`. The project is pinned to Lean 4.33.1 and mathlib v4.33.1, with mathlib commit `0df444a360eaa60ab8c11dca51a86af692955474`.

The proof repository was locally checked successfully and its axiom audit reports only `propext`, `Classical.choice`, and `Quot.sound`. This candidate record does not assert independent verification, recipient confirmation, or an award decision. The formal verification record is intentionally left null pending repository review.
