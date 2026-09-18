import JSP000853.Definitions
import JSP000853.Finite
import JSP000853.Deletion
import JSP000853.ExtensionCounting
import JSP000853.Sampling
import JSP000853.LowerBound
import JSP000853.UpperBound
import JSP000853.GridGraph
import JSP000853.ArbitraryUpper

/-!
# JSP-000853

Formalization of Erdős Problem #1025.  The mathematical target is that the largest
free set forced by an admissible mapping on pairs has order `Θ(√n)`.

The proof is split into two independently auditable parts:

* a universal lower bound, obtained from an independent-set argument for a sparse
  three-uniform hypergraph;
* an explicit two-dimensional grid mapping giving the matching upper bound.
-/
