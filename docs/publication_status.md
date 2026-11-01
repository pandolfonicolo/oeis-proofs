# Proof and publication status — 2026-11-01

| Family | Proved scope | Formal verification | Publication |
| --- | --- | --- | --- |
| A242239: one extra position | Generating function, column recurrence, stable rows, Mathar identity for A242235 | Written proof and exact Python checks | Existing public manuscript and OEIS manuscript/source links |
| A242322: two extra positions | Transfer construction and quartic rows; general minimal recurrence order binomial(k+2,2), even eventually; merged in PR #7 | Written proof and exact symbolic checks | Public manuscript with minimality; merged [PR #7](https://github.com/pandolfonicolo/oeis-proofs/pull/7); OEIS revision 26 approved on October 29 EDT / October 30 UTC |
| A354766/A278085: four integers and three squares | Primitive product, normalized multiplicativity and prime powers, equality characterization, natural density zero; overlapping conclusions previously established by Su | All 43 modules compiled; 14 final dependency reports use only propext, Classical.choice, Quot.sound | Public reproducible project; A278085 revision 57 approved on October 31 EDT / November 1 UTC; A354766 revision 58 approved with Su's contribution, without our reverted additions |

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

Checked against the live OEIS entries and revision histories on 2026-11-01.
Search-engine snapshots can lag behind these pages.

- **A242239:** the public entry retains our manuscript and source links. Its
  formula section still uses empirical labels. The related A242235 entry
  still labels Mathar's identity conjectural and does not link our paper.
- **A242322:** [revision 26](https://oeis.org/history/view?seq=A242322&v=26)
  was approved by Sean A. Irvine on October 29, 2026 at 20:32 EDT
  (October 30 at 00:32 UTC). The public entry credits our comment establishing
  minimal order `(k+1)*(k+2)/2` and stable quartic rows; its manuscript and
  source links are pinned to `fc896fcceae66a180149e05fcd0a8a8e7b0dca4b`.
- **A278085:** our additions from revisions 48–49 were
  [approved as revision 57](https://oeis.org/history/view?seq=A278085&v=57)
  by Michael De Vlieger on October 31, 2026 at 20:19:42 EDT
  (November 1 at 00:19:42 UTC), after Jeff Sponaugle marked revision 56
  reviewed earlier that day. The [approved public entry](https://oeis.org/A278085)
  now contains our proof comment, multiplicative formulas, manuscript and
  complete-Lean/source links pinned to
  `080ebfababba28df63e0696019807741e5c0ea92`, together with Su's citation.
  The historical conjecture comment remains alongside the new proof comment.
- **A354766:** our comment and links from revisions 54–55 were reverted by
  Andrew Howroyd in revisions 56–57 on October 22 EDT because another
  contributor's edit was pending. That existing draft was subsequently
  [approved as revision 58](https://oeis.org/history/view?seq=A354766&v=58)
  by Sean A. Irvine on October 28, 2026 at 23:57 EDT
  (October 29 at 03:57 UTC). The public entry now includes Su's divisor-sum
  and multiplicative formulas, fixed-point classification, density zero and
  stronger asymptotic. It does not include our reverted comment or links.
  The earlier instruction to wait until that draft was complete is therefore
  no longer an outstanding timing condition; any separate contribution
  remains subject to OEIS editorial review. No new OEIS edit or discussion
  reply was made as part of this status check.

The current [OEIS AI policy](https://oeis.org/wiki/Use_of_AI_for_OEIS_Submissions)
prohibits AI-generated full comments and editorial replies. The submitted
comments use human-provided English text with notation and
reference corrections; existing contributor credits are preserved. No
editorial reply was posted. A278085's update and A242322's minimality update
are approved. Any future A354766 contribution should distinguish our
alternate derivation and formalization
from the shared results already credited to Su.
