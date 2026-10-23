# Proof and publication status — 2026-10-23

| Family | Proved scope | Formal verification | Publication |
| --- | --- | --- | --- |
| A242239: one extra position | Generating function, column recurrence, stable rows, Mathar identity for A242235 | Written proof and exact Python checks | Existing public manuscript and OEIS manuscript/source links |
| A242322: two extra positions | Transfer construction and quartic rows; general minimal recurrence order binomial(k+2,2), even eventually, in PR #7 | Written proof and exact symbolic checks | Existing public manuscript; minimality revision [PR #7](https://github.com/pandolfonicolo/oeis-proofs/pull/7) |
| A354766/A278085: four integers and three squares | Primitive product, normalized multiplicativity and prime powers, equality characterization, natural density zero | All 43 modules compiled; 14 final dependency reports use only propext, Classical.choice, Quot.sound | New reproducible project in this revision; OEIS update awaits human-authored submission |

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

## OEIS synchronization

The public A242239 and A242322 pages contain links to their existing papers.
The public A354766/A278085 pages still list the arithmetic assertions as
conjectures as checked on 2026-10-23. Their update must cite the complete
public source and manuscript. The historical draft A242322 revision 23 is
not being represented here as an accepted edit; its current editorial state
was not accessible in the unauthenticated check.

The current [OEIS AI policy](https://oeis.org/wiki/Use_of_AI_for_OEIS_Submissions)
prohibits AI-generated full comments and editorial replies. Accordingly,
mathematical notes and proposed formula fields are provided for personal
human verification. They are not submission prose. No automatic OEIS update
or editorial acceptance is claimed by this repository revision.
