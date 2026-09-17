# Bounded prior-art screening

Checked 2026-09-17 UTC before preparing this submission:

- Prize issues and pull requests, open and closed, were screened by Erdős
  number, JSP-000143, “consecutive primes,” and CPAP terminology. The combined
  local corpus contained 617 entries through #618; a fresh latest-100 response
  reached #637 immediately before publication. No matching prize submission was found in these snapshots.
- The pinned Formal Conjectures statement at
  `40e7c98697de6f66b8cbdbf641749ab39ed9c152` leaves the finite-length target
  unproved. This alone is not evidence of a worldwide formalization gap.
- The public `plby/lean-proofs` snapshot at
  `8822f7ddef30fadbd92e1c6ab4ed897af356af5e` was searched by problem filename.
  No Erdős 141 proof file was found.
- Web searches for the exact Lean theorem name, Erdős 141 formalizations, and
  consecutive-prime progressions found the published numerical construction and
  a later public computational report. The report's Python/ECPP certificate work
  is acknowledged as prior verification; it is not represented as this work.
  No code or certificate data was taken from that report. Its public page is
  https://www.erdosproblemaday.com/report/141 .

The numerical progression comes from the original paper. The implementation
here uses a complete Lucas-certificate dependency graph, small divisors, and
43 failed Fermat congruences, all checked in Lean, together with a bridge to the
exact reference definitions. Factorization hints came from FactorDB and local
integer computations; they are validated by the submitted proofs.

This search is bounded and may miss public work. The submission makes no
worldwide first-formalization or mathematical-discovery claim. Any earlier
matching contribution should retain its proper attribution and priority.
