# Novelty and source audit: proposed 3/4 exponent for Erdős 700

Audit date: 2026-09-17. This is a limited literature review, not a guarantee of priority.

## Target and distinction

Erdős problem 700 is JSP-000570 in the local Justin Sun Prize catalog. The function is f(n)=min_{2<=k<=n/2} gcd(n,binom(n,k)). The newly drafted result gives infinitely many squarefree n with four prime factors for which f(n)=n^(3/4)(1+o(1)). It does not resolve the full classification f(n)=n/P(n), nor the proposed general logarithmic upper bounds.

## Sources inspected in full

The scratch filenames cited below are internal working artifacts, not included
in this packet. The included proof is [proof.md](proof.md); the reproducible
Lean build and final theorem audit are recorded in [verification](../verification/).

1. Erdős and Szekeres, Some number theoretic problems on binomial coefficients (1978), 3 pages. Primary scan: https://www.renyi.hu/~p_erdos/1978-46.pdf . The paper poses the classification, square-root strictness, and general upper-bound questions. No four-prime or 3/4-exponent theorem appears.
2. Current problem page and comments: https://www.erdosproblems.com/700 and proof-claims tab https://www.erdosproblems.com/forum/thread/700/proof-claims . The current accepted partial result is attributed to Liam Price using GPT 5.6 Sol Pro and gives infinitely many n with exponent 2/3, through three primes. Sporadic products of more primes are discussed, but no sufficient condition covering the present general four-prime lemma was found in the inspected comments. Local text: 700-comments.txt.
3. Full public manuscript Large Binomial GCDs, credited to GPT 5.6 Sol Pro: https://www.overleaf.com/read/pmnwkfnhhxhn#82956e . Public read-only source downloaded; saved as prior700-main.tex. Its local proposition: if p<q<r are primes, r-q>q-p, and p>2(r-p)^2, then f(pqr)=pq. It then applies Maynard to an admissible set of powers of two. There is no theorem for four or arbitrarily many prime factors.
4. Patrick White + Claude, July 24 report: https://erdosproblemaday.com/day/700-gcd-binomial . Saved as 700-prior-daily-report.txt. This independently discusses close-prime-triple classification, a threshold p>10D^2, and the resulting exponent 2/3. It adds no four-prime criterion. It explicitly describes literature originality as uncertain at that time.

## Searches

Queries including `Erdos 700 3/4`, `Erdős 700 four prime`, `binomial gcd 3/4 Maynard`, `f(n) binomial four primes`, and the title Large Binomial GCDs were checked. No matching published four-prime or 3/4-exponent result was found. This negative search result cannot exclude an unindexed manuscript or an equivalent theorem under other notation.

## Mathematical verification artifacts

The following are internal working artifacts, not included in the packet:

- erdos700-general-four-prime-proof.md: full proposed proof, including all six pair exclusions and the Maynard infinite-family step.
- verify_700_general_algebra.py and 700-general-algebra-certificate.json: exact polynomial identity and universal positive-coefficient checks. Not Lean verification.
- erdos700-four-prime-proof.md: independent fallback fixed pattern (0,2,6,30), P>=100000; proves only the implication for primes of that pattern and does not claim infinitely many such patterns.
- verify_700_four_prime_certificate.py and 700-four-prime-certificate.json: exact finite parameter audit for the universal fixed-pattern proof.

The version-1 packet was subsequently submitted as [official PR #657](https://github.com/TheJustinSunPrize/awards/pull/657).
The version-2 refinement weakens its c-separation hypothesis; this is an extension
of that same submission, not a separate full resolution or a higher-exponent claim.
Additional exact-phrase web searches for the four-prime criterion and the new gap
formula returned no matching result. This limited negative search does not establish priority.

Version 3 further replaces the quadratic separation hypothesis by c>=3b+1.
This is a continuation of the same local four-prime criterion, not a claim of
a larger exponent or a full solution. The previous limited literature review
does not establish worldwide novelty or optimality of this new threshold.

Version 4 further weakens the final separation condition to c>=3b-a+1,
with all other assumptions retained. This extension does not change the 3/4
exponent. No optimality or worldwide-priority claim follows from it.

Version 5 retains the version-4 gap condition but reduces the base-size
requirement from P>=100c^5 to P>=12c^3. The separate exact Lucas-digit
counterexample explains why simply removing the gap condition's final +1
fails. Neither observation establishes global novelty or an optimal joint
parameter condition, and the 3/4 exponent remains unchanged.
