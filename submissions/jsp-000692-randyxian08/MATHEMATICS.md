# Candidate solution of both parts of JSP-000692 / Erdős 836

**Scope:** finite uniform intersecting hypergraphs of chromatic number exactly three. The vertex count always means the union of the edges. Both questions have complete mathematical arguments below and corresponding Lean proof bodies in this project. **The corrected Lean source has passed local compilation and axiom auditing; see verification/status.json.** This manuscript is supplied for mathematical and statement review; it is not an award announcement or a claim of priority.

## 1. Statements

Let \(H\) be a finite family of \(r\)-element sets, \(r\ge2\). Suppose any two members intersect, and there is no proper two-colouring of the vertices. In this setting a proper three-colouring exists, as proved below.

Write \(V(H)=\bigcup_{e\in H}e\). We address precisely the following questions.

**Question 1.** Are there constants \(C>0\) and \(R\) such that every such hypergraph of rank \(r\ge R\) satisfies \(|V(H)|\le Cr^2\)?

**Answer: no.** In fact, for every real \(C\) and natural-number threshold \(R\), there is such a hypergraph, with no isolated ambient vertices, of rank \(r\ge\max(2,R)\) and with \(|V(H)|>Cr^2\).

**Question 2.** Is there a positive constant \(c\), independent of both \(r\) and \(H\), such that two distinct edges always have intersection size at least \(cr\)?

**Affirmative proof:** two distinct edges satisfy
\[
 r\le 2|e\cap f|+1.
\]
In particular the constant \(c=1/3\) works for every \(r\ge2\).

The final Lean theorem combines the negative answer to Question 1 and the affirmative answer to Question 2 on the same definitions. The stronger expanded theorem also states the actual counterexamples and the explicit constant.

## 2. Three colours suffice

Take an edge \(e\), a point \(x\in e\), and colour \(x\) with colour 0, the other points of \(e\) with colour 1, and all remaining vertices with colour 2. The edge \(e\) is not monochromatic because \(r\ge2\). Every other edge meets \(e\), and it also has a point outside \(e\): otherwise uniformity would make it equal to \(e\). It consequently sees colour 2 and at least one of colours 0 and 1. The empty family is trivially colourable.

Thus an intersecting uniform hypergraph of rank at least two has chromatic number exactly three precisely when it is not two-colourable. The Lean predicate nevertheless explicitly records both directions.

## 3. Question 1: Alon's construction, for every rank

The construction in this section is attributed to Noga Alon in the Erdős Problems record. We do not claim to have discovered it.

Let \(h\ge1\), let \(|X|=2h\), and fix \(p\in X\). For each \(h\)-element subset \(A\subseteq X\) that contains \(p\), introduce a new vertex \(y_A\). This labels unordered balanced partitions without a quotient: exactly one side of each partition contains \(p\).

On the disjoint union of the core \(X\) and these new vertices, take the following edges:

* every \((h+1)\)-element subset of \(X\);
* \(A\cup\{y_A\}\) and \((X\setminus A)\cup\{y_A\}\), for every label \(A\).

The rank is \(r=h+1\).

### 3.1 Uniformity and intersection

All edges have size \(h+1\). Two core edges intersect since their sizes sum to \(2h+2>|X|\). A core edge and an extended half intersect in the core since \((h+1)+h>2h\).

For two extended halves, a common core point suffices. If their core halves are disjoint, the two halves are complementary, because each has size \(h\). They therefore label the same balanced partition and share the new vertex assigned to it.

The Lean proof makes this last case completely explicit with the chosen orientation. Two left halves share \(p\). Two right halves lie in \(X\setminus\{p\}\), which has size \(2h-1\), so they intersect. If a left half \(A\) is disjoint from the right half \(X\setminus B\), then \(A\subseteq B\), and equal cardinalities force \(A=B\); the two edges share \(y_A=y_B\).

### 3.2 No proper two-colouring

Consider any two-colouring of the whole vertex set. If either colour appears on at least \(h+1\) core vertices, a monochromatic core edge exists. Otherwise each colour occupies exactly \(h\) core vertices. These two colour classes form one of the balanced partitions. Whichever colour its new vertex receives, the extended edge on that colour's half is monochromatic.

The graph is therefore not two-colourable. Section 2 gives a proper three-colouring, so its chromatic number is exactly three.

### 3.3 Every vertex is active

Every new vertex belongs to its two extended edges. Every core point extends to an \((h+1)\)-subset of \(X\), since \(h+1\le2h\); that subset is a core edge. Hence the union of the edges is the entire ambient vertex set. There is no isolated-vertex padding.

### 3.4 An explicit exponential injection

For the actual Lean family, put \(r=m+2\) and \(h=m+1\), and use
\[
 X=(\{\bot\}\sqcup\{0,\ldots,m-1\})\times\{0,1\},\qquad p=(\bot,0).
\]
For each Boolean vector \(b\in\{0,1\}^m\), the set
\[
 A_b=\{(\bot,0)\}\cup\{(i,b_i):0\le i<m\}
\]
has size \(m+1\), contains \(p\), and is a valid label. Different vectors have different selected halves, hence different labels. All these labels are active vertices. It follows that
\[
 |V(H_m)|\ge 2^m=2^{r-2}.
\]
No estimate for a binomial coefficient is required. The graph is transported by an equivalence to \(\operatorname{Fin} n\); this preserves rank, intersection, both colouring properties and full vertex coverage.

### 3.5 Exceeding every quadratic coefficient after every threshold

Here is the exact elementary growth estimate used in the Lean proof:
\[
 (k+14)^3\le 2^{k+12}\qquad(k\in\mathbb N).
\]
For \(k=0\), this is \(2744\le4096\). The induction step follows from
\[
 2(k+14)^3-(k+15)^3=k^3+39k^2+501k+2113\ge0.
\]

Now fix **any** real \(C\) and **any** natural-number threshold \(R\). Choose a natural number \(k>C\), and set
\[
 m=k+R+12,\qquad r=m+2=k+R+14.
\]
Then \(r\ge R\), \(r\ge2\), and \(r>C\). Applying the growth estimate at \(k+R\) gives
\[
 Cr^2<r^3\le 2^m\le |V(H_m)|.
\]
This proves the negation of the eventual uniform \(O(r^2)\) statement, rather than merely the inequality \(|V|>r^2\) for one example.

## 4. Question 2: the maximal unique-edge set

We prove that if a natural number \(s\) bounds all distinct-edge intersection sizes, then \(r\le2s+1\).

### 4.1 Choose the extremal set

Fix an edge \(E\). Among vertex sets \(R\) that contain \(E\) and contain no other edge of \(H\), choose one of maximum cardinality. This class is nonempty: \(R=E\) is admissible by uniformity. Finiteness gives a maximum. Let \(Q=V\setminus R\).

For every \(y\in Q\), maximality supplies an edge \(F_y\ne E\) with
\[
 F_y\subseteq R\cup\{y\}.
\]
If no such edge existed, adding \(y\) to \(R\) would preserve its defining property and increase its size.

### 4.2 Edges opposite an independent colour class

For each \(x\in E\), the set \(R\setminus\{x\}\) contains no edge. Indeed, its only possible edge inside \(R\) would be \(E\), and \(x\) has been removed. Colour this independent set red and its complement blue. Non-two-colourability forces a blue edge \(G_x\). Thus
\[
 G_x\subseteq Q\cup\{x\}.
\]
Intersectingness with \(E\subseteq R\) forces \(x\in G_x\), so
\[
 G_x\cap R=\{x\}.
\]
The edges \(G_x\) are pairwise distinct as \(x\) varies over \(E\).

In Lean, the opposite edge is obtained from an elementary general lemma: every transversal of a non-two-colourable hypergraph contains an edge. Otherwise colouring the transversal red and its complement blue would be proper. An independent set therefore cannot be a transversal.

### 4.3 The witness matrix

Fix \(x_0\in E\), and set
\[
 A=E\setminus\{x_0\},\qquad B=G_{x_0}\setminus\{x_0\}.
\]
Both sets have \(n=r-1>0\) elements, and \(B\subseteq Q\). Define the \(A\)-by-\(B\) zero-one matrix
\[
 M_{x,y}=1\quad\Longleftrightarrow\quad y\in G_x.
\]

For each row \(x\in A\), its ones lie in \(G_x\cap G_{x_0}\). These are distinct edges, since their intersections with \(R\) are \(\{x\}\) and \(\{x_0\}\). The row has at most \(s\) ones.

For each column \(y\in B\), consider its edge \(F_y\ne E\). If \(M_{x,y}=0\), then \(y\notin G_x\). But
\[
 F_y\subseteq R\cup\{y\},\qquad G_x\cap R=\{x\}.
\]
The nonempty intersection \(F_y\cap G_x\) can therefore contain only \(x\), so \(x\in F_y\). Every zero in this column is indexed by a point of \(E\cap F_y\). The column has at most \(s\) zeros.

Counting all entries, by rows for the ones and columns for the zeros, gives
\[
 n^2\le ns+ns=2ns.
\]
Since \(n>0\), we get \(n\le2s\), i.e. \(r\le2s+1\).

### 4.4 Extract an actual pair and an absolute constant

Suppose no distinct pair had \(r\le2|e\cap f|+1\). Then every distinct-pair intersection would be at most \(\lfloor(r-2)/2\rfloor\). Applying the preceding bound would imply
\[
 r\le 2\lfloor(r-2)/2\rfloor+1\le r-1,
\]
a contradiction. Thus such a pair exists.

Writing \(t=|e\cap f|\), intersectingness gives \(t\ge1\). Hence
\[
 r\le2t+1\le3t,
\]
which gives \(t\ge r/3\). The constant is outside the quantifiers over rank, ambient size and hypergraph, and the pair is explicitly distinct. The stronger bound is \((r-1)/2\), **not** \(r/2\) for every rank.

## 5. Relation to the Lean files

`AlonCore` proves all-parameter uniformity and the two-colouring obstruction; `AlonGeometry` proves intersection, exact three-chromaticity and full activity; `AlonGrowth` supplies the injection, the growth induction and every-coefficient/every-threshold counterexamples. `Relabel` justifies the conversion to `Fin n` without padding.

`LinearIntersection` proves the matrix lemma, the two witness families, the integer bound, and the constant \(1/3\). `Complete` states the two questions on the shared predicates and proves both their conjunction and its fully expanded version. No core combinatorial result is added as an axiom or as an extra hypothesis.

## 6. Attribution and verification boundaries

The Alon construction is pre-existing mathematics. A forum claim of a solution to the second question by Liam Price / GPT-5.5 Pro was recorded on 27 April 2026. Its linked original manuscript was not successfully retrieved here, so no comparison, novelty or priority conclusion is asserted. The maximum-unique-edge-set argument above and its translation are presented for review in full.

The finite checks in `verification/finite-results.json` are regression tests, not proofs of universally quantified statements. The source scanner is not a Lean elaborator. The successful local compilation and axiom-audit outcome is in `verification/status.json`. The submitter has reviewed the statement mapping and mathematical argument with AI assistance. Independent review, priority assessment and the organizers' decisions about eligibility and recipients remain outstanding.

References and recovered links (not treated as substitutes for proof):

- Problem: https://www.erdosproblems.com/836
- Prize entry: https://github.com/TheJustinSunPrize/awards/blob/main/problems/catalog-0601-0700.md#JSP-000692
- Earlier claim location: https://www.erdosproblems.com/forum/thread/836#post-5941
- Earlier manuscript link, unread here: https://www.overleaf.com/read/bhnhxhswnjht#52529b
- Forum snapshot: https://github.com/erichou1/erdos-open-problems/blob/4b4ec96f1c81492af02f814c65825a5106e0af60/forum_threads/836.html
- Official verification policy: https://github.com/TheJustinSunPrize/awards/blob/main/docs/verification.md
- Official contribution policy: https://github.com/TheJustinSunPrize/awards/blob/main/docs/attribution.md
