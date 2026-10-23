# Proof and publication status — 2026-10-23

| Family | Proved scope | Formal verification | Publication |
| --- | --- | --- | --- |
| A242239: one extra position | Generating function, column recurrence, stable rows, Mathar identity for A242235 | Written proof and exact Python checks | Existing public manuscript and OEIS manuscript/source links |
| A242322: two extra positions | Transfer construction and quartic rows; general minimal recurrence order binomial(k+2,2), even eventually; merged in PR #7 | Written proof and exact symbolic checks | Public manuscript with minimality; merged [PR #7](https://github.com/pandolfonicolo/oeis-proofs/pull/7); OEIS revisions 24–25 proposed |
| A354766/A278085: four integers and three squares | Primitive product, normalized multiplicativity and prime powers, equality characterization, natural density zero; overlapping conclusions previously established by Su | All 43 modules compiled; 14 final dependency reports use only propext, Classical.choice, Quot.sound | Public reproducible project; A354766 revisions 54–55 and A278085 revisions 48–49 proposed for review |

The ten fixed-column sequences attached to the first two general families
are specializations, not ten additional independent research projects.
Minimality belongs to A242322; it is not a fourth family.

## Boundaries

No proof step is left open within the scope above. Independent external human
mathematical review has not yet occurred. The work and internal reviews used
AI assistance, as disclosed in the manuscripts. Public availability, Lean
verification, external review, and OEIS editorial acceptance are distinct.

The stronger closed formulas for the A242322 Krylov determinant and Smith
normal form remain conjectural. They are not premises of the minimality
proof. Investigating them is an optional further research project.

A354766 denotes the total standard-quad count divided by four. A278085 denotes
the primitive count divided by four, including its primary sum-3n, norm-3n^2
definition. The complement bijection and even-n normalization are proved.
The equality set for A354766(n)=n has natural density zero; the OEIS
positive-density conjecture is disproved.

Lien-Hung Su's earlier preprint,
[*Integral Quadruples, Three-Square Representations, and Fixed-Point Density*,
version 1, October 10, 2026](https://doi.org/10.5281/zenodo.23272293),
already proves the overlapping arithmetic formulas and fixed-point
classification (Theorems 3.1 and 3.4), and the stronger asymptotic
`S(x) ~ C*x/sqrt(log x)` for the number of fixed points up to `x`
(Theorem 3.6, with an explicit positive constant). We acknowledge that prior
contribution. The complementary contribution here is an explicit
prime-neighbor derivation, a finite-CRT density-zero argument, and complete
Lean formalization of the stated conclusions. No priority claim is made
for the shared results; the stronger asymptotic is outside this formalized
scope.

## OEIS synchronization

The public A242239 and A242322 pages contain links to their existing papers.
The public A354766/A278085 pages still list the arithmetic assertions as
conjectures as checked on 2026-10-23. The proposed updates link the complete
public source and manuscript. The authenticated A354766 draft already
credits Su's October 12 contribution. Our additional comment and links
were saved as revision 54, followed by proposed revision 55, on October 22
EDT / October 23 local time; neither is represented as editorial acceptance.
The earlier contributor credits are preserved. A278085 revisions 48–49 are
also proposed for review. A242322 revisions 24–25 update the existing signed
comment to the proved minimal order and pin its links to the minimality revision; the draft is
proposed for review. A242239 has no pending changes and its existing paper
links remain published.

The current [OEIS AI policy](https://oeis.org/wiki/Use_of_AI_for_OEIS_Submissions)
prohibits AI-generated full comments and editorial replies. The submitted
comments use human-provided English text with notation and
reference corrections; existing contributor credits are preserved. No
editorial reply was posted. The submissions remain proposals pending OEIS
editorial acceptance.
