# Provenance of Erdos882Original.lean

`Erdos882Original.lean` was newly written for this submission from the original
mathematical definition of Erdős Problem 882. It contains no ELRSS construction,
no binary-weight or binary-defect lemmas, and no imported or copied third-party
proof module.

The mathematical definitions are: the set of nonempty subset sums; primitiveness
of that set under divisibility; admissibility of a finite subset of `{1,...,n}`;
and the largest attainable cardinality. The implementation forms the finite set
of attainable cardinalities and takes its `Finset.max'`. Existence and the
extremal inequality follow directly from Mathlib's generic maximum lemmas.

The names `nonemptySubsetSums`, `IsPrimitive`, `Admissible`, `maximumSize`, and
`maximumSize_attained` retain the endpoint API used during development. This
is not a claim that these mathematical concepts or their natural names are new.
Earlier development examined an existing public formalization; no claim of a
clean-room process is made. The new submitted module is independently written
and does not redistribute that formalization.

Mathematical problem source: https://www.erdosproblems.com/882
The upper bound formalized by the other submitted modules is due to Samuel
Korsky. The ELRSS lower-bound result is cited as mathematical background only.
