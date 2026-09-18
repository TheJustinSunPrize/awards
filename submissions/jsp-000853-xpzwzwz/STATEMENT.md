# Statement correspondence

Erdős Problem #1025 starts with a map from unordered pairs of an `n`-element
set back to the set, with the image different from both endpoints.  A subset is
free when no pair of its elements maps into the subset.

`PairMapping α` represents the unordered-pair map as a symmetric binary
function.  Its endpoint conditions are required only for distinct inputs, so
the diagonal values are irrelevant.  `PairMapping.IsFree` likewise quantifies
only over distinct members.

The source conclusion `g(n) = Θ(√n)` is represented without real square roots:

- `LowerBoundTarget` asks for a universal `C > 0` such that every mapping on
  `Fin n` has a free `S` satisfying `n ≤ C * |S|²`.
- `UpperBoundTarget` asks for a universal `C > 0` and, for every `n ≥ 3`, a
  mapping on `Fin n` such that every free `S` satisfies `|S|² ≤ C * n`.

The restriction `n ≥ 3` on the construction side is exact: an admissible map
cannot exist on a set with two elements, since the unique pair has no possible
third image.

The proved theorem is:

```lean
theorem JSP000853.erdos1025 : Erdos1025Target
```

Its two components use the explicit constants `512` and `16`, respectively.
