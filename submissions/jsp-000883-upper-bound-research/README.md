# A proposed lcm-scale upper bound for Erdos Problem 1063

**Research note v0.1, 17 September 2026. Published by the GitHub account
`randyxian08`, with OpenAI ChatGPT/Codex assistance.**

This is an unrefereed mathematical manuscript offered for scrutiny and
formalization. A complete written argument is supplied; the Lean files contain
target definitions only. This publication is not a verified Lean submission,
an assertion of established first-discovery priority, or an award announcement.

## Proposed result

Let `L_k = lcm(1,...,k-1)` and let `n_k` be the least `n >= 2k` for which exactly
one of `n,n-1,...,n-k+1` fails to divide `choose(n,k)`. The manuscript proposes

$$
n_k \le 3L_k \qquad\text{for all sufficiently large }k.
$$

It constructs a witness using a prime `k/2 < p <= (2k-2)/3`, then applies the
classical prime number theorem. The claimed consequence is `n_k = O(L_k)` and
`L_k = o(k L_k)`, improving the known `k L_k` upper bound by an unbounded factor.
This does not determine the sharp growth rate or claim to settle the entire
open-ended original estimation problem. No explicit numerical threshold is claimed.

## Read and reproduce

- [Full manuscript](MANUSCRIPT.md), including the finite construction, all prime
  valuations, uniqueness of the exception, and the asymptotic step.
- [Sources, prior work and contribution disclosure](REFERENCES.md).
- [Verification evidence and limits](VERIFICATION.md).
- [Remaining formalization obligations](docs/FORMALIZATION_PLAN.md).
- [Versioned release, PDF and complete research bundle](https://github.com/randyxian08/awards/releases/tag/jsp000883-research-v0.1).

From this directory, using Python 3.10 or later and no third-party libraries:

```sh
python3 -m unittest discover -s tests -v
python3 scripts/run_checks.py --min-k 9 --max-k 300 --prime-mode all
```

The run writes new results to `runs/latest/`. Published checks cover all 1,454
eligible `(k,p)` pairs with `9 <= k <= 300`, with zero failures. These finite
calculations support exploration; they do not prove the universal theorem.

The optional PDF builder needs ReportLab (tested with 4.4.9) and the four
DejaVu Serif font files (regular, bold, italic, and bold italic):

```sh
python3 scripts/build_note_pdf.py --font-dir /path/to/dejavu-fonts --output note.pdf
```

The release includes a PDF and ZIP. Their exact sizes and SHA-256 hashes are
recorded in [artifacts.json](https://github.com/randyxian08/awards/blob/jsp000883-research-v0.1/submissions/jsp-000883-upper-bound-research/artifacts.json). The ZIP contains its own
`SHA256SUMS` for every packaged file; `artifacts.json` is excluded from the ZIP
to avoid a circular archive checksum.

## Review request

We invite specific corrections to the valuation argument, the prime-interval
step, and the correspondence with Formal Conjectures' `better_upper` target.
We also welcome references to earlier equivalent bounds or constructions and
collaboration on the missing Lean proofs. Please use the linked upstream research
PR for discussion once it is opened; this release remains a fixed v0.1 snapshot.

The related prize PRs [#56](https://github.com/TheJustinSunPrize/awards/pull/56),
[#154](https://github.com/TheJustinSunPrize/awards/pull/154), and
[#406](https://github.com/TheJustinSunPrize/awards/pull/406) concern the known
factorial or `k L_k` bounds. This is a proposed mathematical improvement, not
a request to reassign their formalization credits.

## Citation and status

Suggested citation: **randyxian08. A proposed lcm-scale upper bound for Erdos
Problem 1063. Research note v0.1, 17 September 2026.** Cite the release URL above
and, when citing source, its pinned Git commit. See `CITATION.cff`.

A GitHub release records public availability; it is not a DOI deposit, peer
review, or a guarantee of prize priority. A passed Lean verification remains a
separate requirement for prize evaluation under the
[published rules](https://www.hejustinsun.com/prize/rules). This research
publication requests feedback, not immediate payment or a change to official
problem/award status. See [NOTICE](NOTICE) and [LICENSE](LICENSE).
