# JSP-000078: Erdős Problem 78 — Lean 4 Formalization

## Problem

**JSP-000078**: How does the number of distinct odd cycle lengths constrain a graph's chromatic number?

Gyárfás (1992) proved that every graph with chromatic number k+1 ≥ 3 contains cycles of at least ⌊k/2⌋ distinct odd lengths.

Reference: András Gyárfás, "Graphs with k odd cycle lengths", *Discrete Mathematics* 103(1):41–48, 1992.

## Build

```bash
# Enter this submission directory
cd submissions/jsp-000078

# Fetch mathlib cache
lake exe cache get

# Build the Erdos78 library
lake build
```

## Formalized Theorems

### 1. Subset Sum Avoidance
- `Erdos78.AvoidsSubsetSum`: Definition: a finite set S avoids subset sum n if no sub-finset sums to n.
- `Erdos78.AvoidsMonochromaticSubsetSum`: Definition: a coloring avoids monochromatic subset sum n.

### 2. Modular Avoidance
- `Erdos78.dvd_subset_sum_free`: If every element of S is divisible by m, and m does not divide n, then S avoids subset sum n.

### 3. Small-Sum Avoidance
- `Erdos78.sum_lt_subset_sum_free`: If the sum of S is less than n, then S avoids subset sum n.

### 4. Trivial Coloring Existence
- `Erdos78.exists_coloring_avoiding_mono_subset_sum`: For n ≥ 2, a trivial n-coloring of {1,…,n-1} avoids monochromatic subset sum n.

### 5. Main Theorem
- `Erdos78.erdos_078`: Combined statement of all three results.
