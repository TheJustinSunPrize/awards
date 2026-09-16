# Formula discrepancy for Erdős Problem 504 / JSP-000404

Checked on 16 September 2026. This submission supplies a formally checked counterexample to the displayed lower-interval formula and partial formalization infrastructure. The full determination of the extremal angle remains work in progress.

## The discrepancy

The [Erdős Problems page for Problem 504](https://www.erdosproblems.com/504) displays

\[
\alpha_N=\left(1-\frac{1}{2n-1}\right)\pi
\qquad
\text{when }2^{n-1}<N\le 2^{n-1}+2^{n-3}.
\]

For this interval, Sendov's **final theorem** instead gives

\[
\alpha_N=\left(1-\frac{2}{2n-1}\right)\pi.
\]

Here we use integers \(n\ge3\), so all the displayed exponents are nonnegative. In Sendov's own indexing, with \(m=n-1\ge2\), the formula is

\[
\alpha_N=\left(1-\frac{2}{2m+1}\right)\pi,
\qquad 2^m<N\le 2^m+2^{m-2}.
\]

The complementary interval has
\(\alpha_N=(1-1/(m+1))\pi\) for
\(2^m+2^{m-2}<N\le2^{m+1}\).

Two primary sources confirm the numerator **2**:

1. **Bl. Sendov**, *Minimax of the angles in a plane configuration of points*, Acta Mathematica Hungarica **69** (1995), 27–46, **Theorem 4.1, printed p. 42**. The [Hungarian Academy of Sciences' public scan](https://real-j.mtak.hu/7467/1/ActaMathHung_69.pdf#page=44) contains this theorem on PDF page 44. DOI: [10.1007/BF01874605](https://doi.org/10.1007/BF01874605).
2. **Bl. Sendov**, *Compulsory configurations of points in the plane*, Fundamentalnaya i Prikladnaya Matematika **1** (1995), 491–516 (Russian), **Theorem 4.1, equation (4.14), printed p. 501**, and **Theorem 4.4, printed p. 514**. [Official Math-Net record and full text](https://www.mathnet.ru/eng/fpm81); these are PDF pages 11 and 24.

The English paper's **introductory equation (1.1), p. 27, also prints numerator 1**, whereas its final theorem on p. 42 prints numerator 2. Thus this note identifies a discrepancy between the displayed expressions; it does not attribute the error's origin to the website. The awards repository's JSP-000404 catalog entry asks the extremal-angle question but **does not itself print the erroneous formula**.

## The five-point check and the Lean result

Taking \(n=3,N=5\), the displayed numerator-1 formula predicts \(\alpha_5=4\pi/5\). The corrected expression gives \(3\pi/5\), also explicitly listed in Sendov's English paper on p. 27 and Russian paper on p. 500.

Our Lean result proves the sufficient, weaker bound

\[
\alpha_5\le\frac{3\pi}{4}<\frac{4\pi}{5}.
\]

It uses the five distinct rational-coordinate points
\((-1,-1),(1,-1),(1,1),(0,2),(-1,1)\), and checks that every angle they determine is at most \(3\pi/4\). This is a geometric counterexample, independent of assuming Sendov's formula.

The relevant declarations are `JSP404.alpha_five_le_three_pi_div_four`, `JSP404.alpha_five_lt_four_pi_div_five`, and `JSP404.not_transcribed_lower_formula`. The arithmetic theorem `JSP404.source_branch_at_three` evaluates the corrected expression; **it is not a proof that \(\alpha_5=3\pi/5\)**. Neither that exact value nor Sendov's complete classification is claimed as formalized by this submission.

The original mathematical classification is due to **Blagovest Sendov**. Completing the general geometric counting argument and connecting it with the available construction lemmas remain part of the formalization work.
