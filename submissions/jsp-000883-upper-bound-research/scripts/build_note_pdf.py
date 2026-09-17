#!/usr/bin/env python3
"""Render the research note with ReportLab and the DejaVu Serif font family.

Usage: python build_note_pdf.py --font-dir /path/to/dejavu --output note.pdf
The manuscript is an unrefereed proof claim, not a verified Lean theorem.
"""
import argparse
from pathlib import Path
from reportlab.lib import colors
from reportlab.lib.enums import TA_CENTER, TA_JUSTIFY
from reportlab.lib.pagesizes import A4
from reportlab.lib.styles import ParagraphStyle
from reportlab.pdfbase import pdfmetrics
from reportlab.pdfbase.ttfonts import TTFont
from reportlab.platypus import SimpleDocTemplate, Paragraph, Spacer, PageBreak

parser = argparse.ArgumentParser()
parser.add_argument('--font-dir', type=Path, required=True)
parser.add_argument('--output', type=Path, required=True)
args = parser.parse_args()
for name, filename in [('Serif', 'DejaVuSerif.ttf'), ('SerifB', 'DejaVuSerif-Bold.ttf'),
                       ('SerifI', 'DejaVuSerif-Italic.ttf'), ('SerifBI', 'DejaVuSerif-BoldItalic.ttf')]:
    pdfmetrics.registerFont(TTFont(name, str(args.font_dir / filename)))
pdfmetrics.registerFontFamily('Serif', normal='Serif', bold='SerifB', italic='SerifI', boldItalic='SerifBI')
ink = colors.HexColor('#16242d')
body = ParagraphStyle('body', fontName='Serif', fontSize=10.5, leading=15.2,
                      textColor=ink, spaceAfter=8, alignment=TA_JUSTIFY)
heading = ParagraphStyle('heading', parent=body, fontName='SerifB', fontSize=12,
                         leading=16, spaceBefore=11, spaceAfter=7, keepWithNext=True)
equation = ParagraphStyle('equation', parent=body, alignment=TA_CENTER,
                          fontSize=11, leading=17, spaceBefore=4, spaceAfter=10)
small = ParagraphStyle('small', parent=body, fontSize=8.6, leading=12.3, alignment=0)
title = ParagraphStyle('title', parent=body, fontName='SerifB', fontSize=20,
                       leading=25, alignment=0, spaceAfter=13)
story = []
def p(text, style=body): story.append(Paragraph(text, style))
def h(text): p(text, heading)
def eq(text): p(text, equation)
def page(): story.append(PageBreak())

p('UNREFEREED RESEARCH NOTE  |  v0.1  |  17 SEPTEMBER 2026', small)
story.append(Spacer(1, 13))
p('A proposed lcm-scale upper bound<br/>for Erdős Problem 1063', title)
p('Published by <b>randyxian08</b> (GitHub account)<br/>Prepared with OpenAI ChatGPT/Codex assistance', small)
h('Abstract')
p('Let <i>n</i><sub>k</sub> be the least integer <i>n</i> ≥ 2<i>k</i> for which exactly one of '
  '<i>n</i>, <i>n</i> − 1, …, <i>n</i> − <i>k</i> + 1 fails to divide the binomial coefficient '
  'C(<i>n</i>, <i>k</i>). We give a proposed proof that, for all sufficiently large <i>k</i>,')
eq('<i>n</i><sub>k</sub> ≤ 3<i>L</i><sub>k</sub>, &nbsp; <i>L</i><sub>k</sub> = lcm(1, …, <i>k</i> − 1).')
p('The construction removes one large prime factor from <i>kL</i><sub>k</sub> and chooses one '
  'of two adjacent blocks. Prime valuations verify every divisibility and the unique '
  'exception. The classical prime number theorem supplies the required prime eventually. '
  'This yields <i>n</i><sub>k</sub> = O(<i>L</i><sub>k</sub>), improving the recorded '
  '<i>kL</i><sub>k</sub> comparator by an unbounded factor.')
p('<b>Status.</b> This is a written proof claim offered for review. Finite experiments '
  'have been reproduced; a complete Lean proof has not been supplied. Independent peer '
  'acceptance and global priority are not claimed. The sharp growth rate and the full '
  'open-ended estimation problem remain outside the claim.', small)
h('1. Statement of the finite construction')
p('For <i>k</i> ≥ 2 let <i>L</i> = <i>L</i><sub>k</sub>. An admissible starting point is an '
  'integer <i>n</i> ≥ 2<i>k</i> whose descending block has exactly one nondivisor of '
  'C(<i>n</i>, <i>k</i>). We produce actual admissible values before using the minimum.')
p('<b>Proposition.</b> Suppose <i>k</i> ≥ 9, <i>p</i> is prime, '
  '<i>k</i> &lt; 2<i>p</i>, and 3<i>p</i> + 2 ≤ 2<i>k</i>. Put')
eq('<i>m</i> = <i>kL</i>/<i>p</i>, &nbsp; <i>r</i> = <i>m</i> mod <i>p</i>, &nbsp; <i>s</i> = <i>k</i> − <i>p</i> − 1.')
p('Choose <i>n</i> = <i>m</i> if <i>r</i> ≤ <i>s</i>, and '
  '<i>n</i> = <i>m</i> + <i>k</i> − 1 otherwise. Then <i>n</i> is admissible, '
  '<i>n</i> ≤ 3<i>L</i>, and the unique exceptional integer in its block is <i>m</i>.')

page()
h('2. Block geometry and divisibility')
p('Write <i>v</i><sub>q</sub>(<i>x</i>) for the exponent of a prime <i>q</i> in a positive '
  'integer <i>x</i>. The hypotheses give <i>p</i> &lt; <i>k</i> &lt; 2<i>p</i> and '
  '<i>p</i><super>2</super> &gt; <i>k</i>. Thus <i>p</i> does not divide <i>k</i>, '
  '<i>v</i><sub>p</sub>(<i>L</i>) = 1, and <i>m</i> is an integer not divisible by <i>p</i>. '
  'In particular 1 ≤ <i>r</i> ≤ <i>p</i> − 1. Since 2 and the odd prime <i>p</i> both divide '
  '<i>L</i>, we have 2<i>p</i> | <i>L</i> and <i>m</i> ≥ 2<i>k</i>.')
p('The inequality 3<i>p</i> + 2 ≤ 2<i>k</i> gives 2<i>s</i> ≥ <i>p</i>. If '
  '<i>r</i> ≤ <i>s</i>, the block <i>B</i> = {<i>m</i> − <i>k</i> + 1, …, <i>m</i>} '
  'contains the two distinct multiples <i>m</i> − <i>r</i> and <i>m</i> − <i>r</i> − <i>p</i>, '
  'because <i>r</i> + <i>p</i> ≤ <i>k</i> − 1.')
p('Otherwise <i>r</i> &gt; <i>s</i>, so <i>p</i> − <i>r</i> ≤ <i>s</i>. The block '
  '<i>B</i> = {<i>m</i>, …, <i>m</i> + <i>k</i> − 1} contains '
  '<i>m</i> + (<i>p</i> − <i>r</i>) and <i>m</i> + (2<i>p</i> − <i>r</i>), since '
  '2<i>p</i> − <i>r</i> ≤ <i>p</i> + <i>s</i> = <i>k</i> − 1.')
p('All block members are positive. With <i>n</i> = max <i>B</i> and <i>C</i> = C(<i>n</i>, <i>k</i>),')
eq('<i>C</i> · <i>k</i>! = ∏<sub><i>d</i> ∈ <i>B</i></sub> <i>d</i>.')
h('Primes different from p')
p('Fix any prime <i>q</i> ≠ <i>p</i>, including primes larger than <i>k</i>, and set')
eq('<i>a</i> = max<sub>1 ≤ <i>j</i> &lt; <i>k</i></sub> <i>v</i><sub>q</sub>(<i>j</i>), &nbsp; '
   '<i>b</i> = <i>v</i><sub>q</sub>(<i>k</i>), &nbsp; '
   '<i>A</i> = ∑<sub>1 ≤ <i>j</i> &lt; <i>k</i></sub> <i>v</i><sub>q</sub>(<i>j</i>).')
p('Then <i>v</i><sub>q</sub>(<i>m</i>) = <i>a</i> + <i>b</i> and '
  '<i>v</i><sub>q</sub>(<i>k</i>!) = <i>A</i> + <i>b</i>. Write the other block members as '
  '<i>d</i><sub>j</sub> = <i>m</i> + ε<i>j</i>, where ε is −1 or +1 and 1 ≤ <i>j</i> &lt; <i>k</i>. '
  'The valuation inequality gives <i>v</i><sub>q</sub>(<i>d</i><sub>j</sub>) ≥ '
  '<i>v</i><sub>q</sub>(<i>j</i>). For each noncentral <i>d</i><sub>i</sub>, therefore,')
eq('<i>v</i><sub>q</sub>(∏<sub><i>d</i> ∈ <i>B</i>, <i>d</i> ≠ <i>d</i><sub>i</sub></sub> <i>d</i>) '
   '≥ <i>a</i> + <i>b</i> + <i>A</i> − <i>v</i><sub>q</sub>(<i>i</i>) ≥ <i>A</i> + <i>b</i>.')
p('The product identity implies <i>v</i><sub>q</sub>(<i>C</i>) ≥ '
  '<i>v</i><sub>q</sub>(<i>d</i><sub>i</sub>).')

page()
h('3. The exception and the eventual bound')
p('<b>The prime p.</b> We have <i>v</i><sub>p</sub>(<i>k</i>!) = 1. Removing any one '
  'member of <i>B</i> leaves at least one <i>p</i>-multiple, because the block has two '
  'distinct such multiples. Hence <i>v</i><sub>p</sub>(<i>C</i>) ≥ '
  '<i>v</i><sub>p</sub>(<i>d</i>) for every <i>d</i> ∈ <i>B</i>. Together with the previous '
  'section, this proves <i>d</i> | <i>C</i> for every block member other than <i>m</i>.')
p('<b>The exception is genuine.</b> Choose a prime divisor <i>q</i> of <i>k</i>. It is '
  'different from <i>p</i>. Now <i>b</i> &gt; 0, so')
eq('<i>v</i><sub>q</sub>(<i>m</i>) = <i>a</i> + <i>b</i> &gt; <i>a</i> ≥ <i>v</i><sub>q</sub>(<i>j</i>) '
   '&nbsp; (1 ≤ <i>j</i> &lt; <i>k</i>).')
p('Unequal valuations give <i>v</i><sub>q</sub>(<i>m</i> + ε<i>j</i>) = '
  '<i>v</i><sub>q</sub>(<i>j</i>). Consequently,')
eq('<i>v</i><sub>q</sub>(<i>C</i>) = (<i>a</i> + <i>b</i>) + <i>A</i> − (<i>A</i> + <i>b</i>) '
   '= <i>a</i> &lt; <i>v</i><sub>q</sub>(<i>m</i>).')
p('Thus <i>m</i> does not divide <i>C</i>. It is the unique exception, at descending '
  'offset 0 for the left block and <i>k</i> − 1 for the right block. Finally,')
eq('<i>n</i> ≤ <i>kL</i>/<i>p</i> + <i>k</i> − 1 &lt; 2<i>L</i> + <i>k</i> − 1 ≤ 3<i>L</i>,')
p('using <i>p</i> &gt; <i>k</i>/2 and <i>L</i> ≥ <i>k</i> − 1. This completes the finite construction.')
h('Prime number theorem and asymptotics')
p('The classical prime number theorem π(<i>x</i>) ~ <i>x</i>/log <i>x</i> implies')
eq('π((2<i>k</i> − 2)/3) − π(<i>k</i>/2) = (1/6 + o(1)) · <i>k</i>/log <i>k</i> &gt; 0')
p('for every sufficiently large <i>k</i>. There is consequently a prime '
  '<i>k</i>/2 &lt; <i>p</i> ≤ (2<i>k</i> − 2)/3. Applying the construction gives an actual '
  'admissible starting point. The minimum therefore exists and satisfies '
  '<i>n</i><sub>k</sub> ≤ 3<i>L</i><sub>k</sub> eventually.')
p('For <i>U</i>(<i>k</i>) = <i>L</i><sub>k</sub>, the bound yields '
  '<i>n</i><sub>k</sub> = O(<i>U</i>(<i>k</i>)). Since <i>L</i><sub>k</sub> &gt; 0,')
eq('<i>U</i>(<i>k</i>)/(<i>kL</i><sub>k</sub>) = 1/<i>k</i> → 0.')
p('This gives both quantitative conditions in the inspected Formal Conjectures '
  '<i>better_upper</i> target. No explicit threshold, exact formula, or sharp growth '
  'rate is asserted.')

page()
h('4. Reproducibility, status and sources')
p('Exact integer checks cover every eligible pair (<i>k</i>, <i>p</i>) with '
  '9 ≤ <i>k</i> ≤ 300: 1,454 pairs over 285 values of <i>k</i>, with zero failures. '
  'There are 1,055 left blocks and 399 right blocks. Values 10, 11, 14, 15, 16, 17, '
  'and 26 have no eligible prime and are skipped, not counted as successes. '
  'All 18 Python tests passed. Each case uses the actual arbitrary-precision '
  'binomial coefficient and checks all block divisibilities.')
p('The Lean target definitions were checked using Lean 4.33.0 and Mathlib '
  'db584cd6d46c92f209a44c0f1c829460d327499d in an existing pinned environment. '
  'The four central declarations are definitions of propositions, not proofs. '
  'No completed universal Lean theorem, final-theorem axiom audit, or fresh kernel '
  'replay is supplied. Numerical evidence does not replace the all-parameter argument.')
h('Attribution and review request')
p('The argument and original experiment bundle were prepared with ChatGPT assistance; '
  'Codex assisted in checking, reproduction, exposition and publication. The publishing '
  'account is randyxian08. This is a contributor draft, not an independent referee '
  'report. Earlier bounds retain their authors’ credit. Global priority is unconfirmed.')
p('Please review the finite valuation argument, the prime-interval step, and the '
  'match to the asymptotic target; references to earlier equivalent bounds and '
  'collaboration on formalization are welcome. The proposed factor-<i>k</i> improvement '
  'does not settle the sharp asymptotic scale. Publication is not a prize decision.')
h('References and public version')
p('[1] T. F. Bloom, Erdős Problem 1063 and discussion, accessed 17 September 2026. '
  '<link href="https://www.erdosproblems.com/1063" color="#17607a">erdosproblems.com/1063</link>. '
  'The discussion records Stijn Cambie’s <i>kL</i><sub>k</sub> bound (1 October 2025).', small)
p('[2] P. Erdős and J. L. Selfridge, Problem 6447, American Mathematical Monthly '
  '(1983), 710. J.-M. Monier, Solutions of Advanced Problems: 6447, American '
  'Mathematical Monthly 92 (1985), 435-436. R. K. Guy, Unsolved Problems in Number '
  'Theory (2004), B31. Bibliographic details follow the cited problem sources; '
  'the original publications were not independently retrieved here.', small)
p('[3] The Formal Conjectures Authors, ErdosProblems/1063.lean (2026), inspected '
  'Git blob bda13fc03989bb240293a164c7d70c75dfcc86f9. Target definitions retain '
  'Apache-2.0 attribution. The classical prime number theorem is a standard input.', small)
p('[4] Related prize PRs #56, #154 and #406 concern Monier’s factorial bound, '
  'Cambie’s lcm bound, or factorial multiples. Their public descriptions do not '
  'claim this note’s O(<i>L</i><sub>k</sub>) improvement. This bounded check does not '
  'establish global novelty. See REFERENCES.md in the source bundle.', small)
p('<b>Versioned source, code and logs:</b><br/>'
  '<link href="https://github.com/randyxian08/awards/releases/tag/jsp000883-research-v0.1" color="#17607a">'
  'github.com/randyxian08/awards/releases/tag/jsp000883-research-v0.1</link><br/>'
  'Suggested citation: randyxian08 (2026), <i>A proposed lcm-scale upper bound for '
  'Erdős Problem 1063</i>, research note v0.1. This release is not a DOI deposit. '
  'License: Apache-2.0.', small)

def decorate(canvas, doc):
    canvas.saveState()
    canvas.setStrokeColor(colors.HexColor('#bec7cc'))
    canvas.line(54, 45, A4[0]-54, 45)
    canvas.setFont('Serif', 7.5)
    canvas.setFillColor(colors.HexColor('#596770'))
    canvas.drawString(54, 31, 'Erdős 1063  |  research note v0.1  |  Lean proof incomplete')
    canvas.drawRightString(A4[0]-54, 31, str(doc.page))
    canvas.restoreState()

args.output.parent.mkdir(parents=True, exist_ok=True)
doc = SimpleDocTemplate(str(args.output), pagesize=A4, leftMargin=54, rightMargin=54,
                        topMargin=47, bottomMargin=58,
                        title='A proposed lcm-scale upper bound for Erdos Problem 1063',
                        author='randyxian08; prepared with OpenAI ChatGPT/Codex assistance',
                        subject='Unrefereed research note v0.1; Lean proof incomplete')
doc.build(story, onFirstPage=decorate, onLaterPages=decorate)
print(args.output)
