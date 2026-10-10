# Statement correspondence and attribution

## Full mathematical target

Write p(0)=2, p(1)=3, ... for the increasing enumeration of primes. Define L(0)=1 and L(k+1)=p(k). For every natural n, let S(n) mean:

- n is positive;
- some index k satisfies L(k)<=n<p(k);
- for every natural r, if r is prime and r divides n!+1, then r=p(k) or r=p(k+1).

The target is **S(n) if and only if 1<=n<=5**, for every n. Thus the set of positive solutions is finite. The allowed prime factors need only be contained in the two-element set: it is not required that both allowed primes divide n!+1. This distinction matters for all five solutions. The n=0 boundary is excluded explicitly. If one indexes primes starting at 1 and allows only intervals with a preceding prime, the first interval convention is omitted and the corresponding positive solution list starts at 2; the original finiteness answer is unchanged. This packet states its n=1 convention explicitly.

[Statement.lean](proof/Statement.lean) defines the full predicate and finiteness target using only Mathlib; [Main.lean](proof/Main.lean) proves them via a checked definitional bridge to the pinned source. Its `finitely_many_solutions` states actual set finiteness, not bounded experimental absence. `escaping_prime` quantifies over **every** n>=6 and every applicable prime interval and produces a prime divisor outside the two permitted primes. There is no computational cutoff in these final statements.

## Imported proof and new work

The mathematical classification is Florian Luca's 2001 theorem, not a new result. The substantive Lean proof is existing public work in `plby/lean-proofs` at `8822f7ddef30fadbd92e1c6ab4ed897af356af5e`. Its main source credits Codex and GPT-5.6 Sol. This packet adds an AI-assisted Lean 4.34.0 compatibility patch, explicit statement consequences, source locks, and actual compilation/axiom evidence. The final verification receipt records successful exact-scope replay and rejection of the negative control. It does not claim authorship of Luca's argument, authorship of the imported formalization, first formalization, or independent review.

The new patch changes proof scripts only: a product-monotonicity API adjustment, restricted normalization, and an explicit proved equality between factorization and the two-adic valuation. Original source hashes, patched hashes and exact edits are all exposed. Upstream sources remain externally referenced, with their published attribution and licensing; they are not republished or relicensed as new work here.

## Why the proof is not merely a finite computation

The imported proof has these interfaces, all of which must be discharged before the final theorem is accepted:

1. `Core` defines the prime sequence and exact predicate and verifies the small solutions. Supporting lemmas eliminate n=6,...,11, then 12,...,193 and 194,...,433.
2. For any hypothetical solution n>433, it obtains positive exponents a,b and the factorization n!+1=p^a q^b, where p,q are the first two primes after n.
3. A specialized Bugeaud–Laurent estimate is proved through interpolation determinants and yields q<36,000,000. The proposition `LargePrimeBound` is a named intermediate goal, not an admitted axiom.
4. Kernel-checked periodic/cubic-character certificates establish `LargeCubicCertificate` over the resulting bounded prime parameters. The sieve forces a cube-minus-one relation for n!, contradicting a separate factorial bound.
5. The main source supplies **both** proved inputs to `erdos1058_classification_of_large_certificates`. Merely compiling that conditional assembly without compiling the analytic input would not establish the full theorem. The dependency closure and final axiom audit are therefore essential.

This is a map for reading the pinned formal proof, not a claim to have independently recreated every argument in Luca's paper. The publisher PDF request returned HTML rather than a usable PDF in this session. The original question and historical attribution were checked against [the Erdős problem page](https://www.erdosproblems.com/1058); the full formal source was read and processed directly.

## Search and eligibility limits

All-state awards issue/PR searches by JSP-000878 and Erdős 1058 found [issue76](https://github.com/TheJustinSunPrize/awards/issues/76), a chronology correction, at the time checked. Cross-repository GitHub code search also found:

- The substantive pinned `plby/lean-proofs` source used here.
- [ryantuck/erdos-ai](https://github.com/ryantuck/erdos-ai/blob/f32b2886f8f005d481533036d0af4fe36e8e48f7/deepmind/reviews/1058.md), whose reviewed statement contains `sorry`; this is not a complete proof.
- [rjwalters/lean-genius](https://github.com/rjwalters/lean-genius/blob/dc62f771ed5010abfdb04247dff6143e0e69d3e7/proofs/Proofs/Erdos1058Problem.lean), which declares `luca_theorem` and the conjecture as axioms; this is not accepted as a complete kernel proof here.

Search coverage is limited by indexing and did not establish the globally earliest public timestamp. Under official FAQ Q8, earlier valid public source cannot be displaced by a later rebuild, cleaner code or PR merge. Any same-window joint consideration or Tier V Contribution treatment requires organizer determination. A successful local run alone is neither designated verification nor official prize eligibility. No solver share, formalizer share, tier, amount or payment is asserted. Recipient identity and independent review remain unconfirmed.

The final pre-publication duplicate check on 2026-09-17 searched all-state GitHub issues and PRs for both `JSP-000878` and `1058`; both queries returned only issue76. This checks the awards repository, not every public platform or unindexed private submission.
