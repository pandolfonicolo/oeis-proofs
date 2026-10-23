# Publication review record

Package prepared from `A354766_A278085_complete_2026-10-23`. The 43 local
Lean proof sources, generated joint source, pinned manifest, original Lean
tools, and recorded checking evidence are copied without changing proof
bodies. `paper/` becomes `manuscript/`. The recovery manifest and unrelated
A242322 minimality audit are excluded. No cache, scratch proof, credential,
generated Lean binary, or incomplete Formal Conjectures template is part of
the publication package.

Project publication version `0.1.0` identifies the first public package. It
does not indicate an unfinished proof: all 43 modules and all 14 final
dependency reports are present. Independent external human review is
pending.

The literature acknowledgment was updated after checking Lien-Hung Su's
earlier Zenodo preprint, version 1, October 10, 2026,
[doi:10.5281/zenodo.23272293](https://doi.org/10.5281/zenodo.23272293),
licensed CC BY 4.0. Theorems 3.1 and 3.4 contain the overlapping primitive
and total formulas and fixed-point classification; Theorem 3.6 proves the
stronger asymptotic `S(x) ~ C*x/sqrt(log x)` with an explicit positive
constant. The manuscript and README now acknowledge that prior contribution.
Our distinct scope is the explicit prime-neighbor derivation, finite-CRT
density-zero proof, and Lean formalization. No first-proof or priority
claim is made for the shared conclusions. The stronger asymptotic is not
part of this formal development. Checking that overlap is not external
peer review of either paper.

The source manifest and recorded standalone compilation results identify the
same current 43-module graph. The recorded final dependency reports for all
14 conclusions contain only `propext`, `Classical.choice`, and `Quot.sound`.
The portable package audit checks those actual records and their source
bindings; it does not claim to rerun the Lean kernel. `make formal` provides
the separate fresh-compilation route in an ignored directory and protects
the historical logs from replacement. Compiler linter warnings in the
recorded logs are preserved and are not proof admissions. The two narrative
release reports are translated into English and labeled as translations;
their compiler data, source files, CSV data and recorded hashes remain
unchanged.

The publication PDF was rebuilt with `make pdf`, using a fixed source-date
epoch. The final LaTeX log has no unresolved-reference or layout warnings.
All 11 revised rendered pages were visually inspected. The only manuscript
source changes are the prior-work paragraph and its bibliographic entry;
all theorem statements and proof bodies are unchanged. All Lean sources,
data, tools and compiler logs are unchanged.

The conventional proof covers the corrected parity bridge, the lattice
representation product including the prime three, normalization and content
decomposition, the two multiplicative functions, their local formulas, the
exact equality cases, and the finite density-zero sieve. The explicit
complement bijection connects A278085's primary definition to the standard
quadruple model. No open mathematical proof step remains within these
stated results. The stronger determinant/Smith conjectures from the other
OEIS family are outside this project's scope.

Recorded independent enumeration covers `n=1..300`, direct primitive
three-square checks at the 38 odd levels up to 75, a second ordered-pair
implementation through 20, and symmetric primary-model bounds through 12.
The static audit independently recomputes the finite arithmetic formulas
for every recorded CSV row. `make verify` adds a fresh bounded enumeration
through 40, with direct three-square checks up to 25. None of these finite
checks is used as a proof of the general theorem.

The OEIS AI policy and both relevant entries were checked on 2026-10-23.
The publicly approved entries retain conjectural wording. The authenticated
A354766 draft already credits Su's October 12 contribution. Our additional
comment and links were saved as revision 54, followed by proposed revision
55, on October 22 EDT / October 23 local time. Earlier contributor credits
were preserved. A278085 revisions 48–49 are also proposed for review.
No editorial acceptance or endorsement of this manuscript, or external human mathematical review is
claimed. Human submission responsibility and prohibited AI comment/Pink Box practices are stated in the project README and the
repository's CONTRIBUTING.md. The manuscript discloses AI assistance.

Code and build tools use MIT; original content and documentation use CC BY
4.0 under the repository's existing license files. External mathematical
references are citations, not redistributed third-party texts. Original
recorded logs can contain absolute source paths from the checking machine;
these are provenance records and are not required runtime paths.
