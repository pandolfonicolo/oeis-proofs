# Integer quadruples and primitive three-square representations

This project proves the arithmetic formulas for [OEIS A354766](https://oeis.org/A354766)
and [A278085](https://oeis.org/A278085), with a conventional manuscript and a
complete Lean development. The release contains 43 local proof modules and
recorded successful checks of 14 final dependency reports. Those reports use
only `propext`, `Classical.choice`, and `Quot.sound`; no admitted result, added
axiom, or native compiler oracle is a dependency of the final conclusions.
Independent external human mathematical review remains pending.

The overlapping arithmetic formulas and fixed-point classification were
already proved in Lien-Hung Su's earlier preprint,
[*Integral Quadruples, Three-Square Representations, and Fixed-Point Density*,
version 1, October 10, 2026](https://doi.org/10.5281/zenodo.23272293),
Theorems 3.1 and 3.4. His Theorem 3.6 gives the stronger asymptotic
`S(x) ~ C*x/sqrt(log x)` for the number of fixed points up to `x`, with an
explicit positive constant. We acknowledge this prior contribution. This
project supplies a separate explicit prime-neighbor derivation, a finite-CRT
density-zero argument, and complete Lean proofs of the stated conclusions.
It makes no priority claim for the shared results and does not formalize
the stronger asymptotic.

## Results and normalization

For positive `n`, a standard quadruple is an ordered integer quadruple with
sum `n` and sum of squares `n²`. All signs and coordinate orders are counted.
Write `tq(n)` for the total count and `pq(n)` for the primitive count, where
primitive means coordinate gcd one. The arithmetic functions are
`T(n) = tq(n)/4` and `P(n) = pq(n)/4`; divisibility by four is proved.

- `T` is A354766. A278085's primary definition instead uses primitive
  quadruples with sum `3n` and square sum `3n²`; an explicit, content-preserving
  complement involution proves that its normalized count equals `P`.
- The primitive three-square product is derived from concrete prime-neighbor
  lattices and a primitive-vector double count. No representation-count
  formula or recurrence is assumed as a hypothesis of the final result.
- The Hadamard bridge handles odd `n`, `n = 2 mod 4`, and `4 | n` separately;
  the middle case uses the halved three-square level.
- `P` and `T` are multiplicative, and all stated prime-power formulas are
  proved.
- `T(n) = n` precisely for `n = 2^e m`, where `e` is zero or one, `m` is odd,
  and every prime divisor of `m` is `1 mod 6`. This set has natural density
  zero, refuting the positive-density conjecture in A354766. The finite sieve
  does not assume a reciprocal-prime divergence theorem.

The [manuscript](manuscript/main.pdf) gives the complete conventional
argument. [The Lean guide](lean/README.md) explains the module architecture.

## What verification means

`make verify` is a fast, portable package audit using Python's standard
library. It verifies the pinned source hashes and complete 43-module import
graph, the recorded standalone compilation exit codes and source hashes,
the actual 14 recorded final axiom reports, the recorded joined-check hash,
and the 300 recorded exact numerical rows against independently recomputed
integer formulas. It then performs a **fresh finite enumeration** through
`n=40`, with direct primitive three-square checks at odd levels up to 25 and
two workers. These finite computations are consistency checks, not proofs.

This fast target does **not** recompile Lean. Successful recorded compilation
is release evidence, while a new compilation on the reader's machine is a
separate operation:

```sh
make verify   # Static release-evidence audit and fresh bounded enumeration
make check    # SHA-256 checks for the publication package
make formal   # Fresh pinned Lean compilation and final axiom audit
make pdf      # Rebuild the manuscript with latexmk
```

`make formal` needs the pinned Lean 4.27.0 toolchain, `lake`, Git, network
access for the exact dependencies/cache, and Python 3.9 or later. Mathlib is
pinned to `a3a10db0e9d66acbebf76c5e6a135066525ac900`; the manifest also fixes
its dependencies. `A354766_LEAN` may select the exact compiler binary.
The target stages an unchanged source copy under
`verification/current/formal/`, runs `lake exe cache get`, compiles the local
modules in dependency order, and reruns the final axiom audit. New logs and
artifacts remain there. The original `lean/verification/` evidence is never
overwritten by these Makefile targets.

The compiler records, source files and numerical data are preserved byte
for byte. Two narrative release reports are translated into English and
identify that translation explicitly. Their absolute
build paths identify the original checking environment and are not required
paths on a new machine. Some old audit prose describes an earlier formal
checkpoint; current completion evidence is the source manifest, standalone
results, and final axiom reports, not an earlier prose status sentence.
An unused recovered theorem retains `native_decide`; the 14 final reports
show that it is absent from the dependencies of all public conclusions.

## Package layout

```text
lean/                     Exact pinned proof sources and build tools
lean/verification/        Recorded release compilation and axiom evidence
manuscript/               TeX sources, PDF, and historical internal audit
verification/cloud/       Independent exact-count program and recorded CSVs
verification/current/     Ignored fresh checks, formal builds, and logs
verification/verify_package.py
docs/publication_review.md
metadata.yaml
checksums.sha256
```

The unrelated A242322 minimality audit and the recovery-only manifest are
excluded. No dependency cache or generated Lean binary is shipped.

## OEIS publication and review

Status checked against the live OEIS pages and histories on 2026-11-01.
Our A354766 comment and links were submitted in revisions 54–55, then
reverted by Andrew Howroyd in revisions 56–57 because another contributor's
edit was pending. That existing draft was
[approved as revision 58](https://oeis.org/history/view?seq=A354766&v=58)
on October 28, 2026 at 23:57 EDT (October 29 at 03:57 UTC). The public
entry now includes Su's arithmetic formulas, fixed-point classification,
density-zero result and stronger asymptotic, but not our reverted comment
or links. The instruction to wait for the existing draft to finish is no
longer an outstanding timing condition; a separate contribution would still
require editorial review.

Our A278085 proof comment, formulas, manuscript and complete-Lean/source
links are now in the [approved public entry](https://oeis.org/A278085).
Michael De Vlieger approved
[revision 57](https://oeis.org/history/view?seq=A278085&v=57)
on October 31, 2026 at 20:19:42 EDT (November 1 at 00:19:42 UTC),
after Jeff Sponaugle reviewed revision 56. The public entry links our package
at `080ebfababba28df63e0696019807741e5c0ea92` and preserves Su's citation.
Its historical conjecture comment remains alongside the new proof comment.
No OEIS edit or discussion reply was made
during this status check. Mathematical completion and kernel checks remain
distinct from editorial acceptance and independent human review. See the
[repository publication status](../../docs/publication_status.md) for the
other sequence families and the boundary of our complementary contribution.

Before submitting any OEIS update, the human contributor must understand and
personally verify its content and write the final submission prose. Follow
the current [OEIS AI policy](https://oeis.org/wiki/Use_of_AI_for_OEIS_Submissions):
do not paste AI-generated Pink Box replies or fully AI-generated comments,
and do not submit a program whose operation or limits the submitter does
not understand. This project includes no ready-to-paste OEIS comments.

AI assistance in exploration, checking, and drafting is disclosed in the
manuscript. Internal agent audits are not represented as external human
peer review. New source code and build automation use MIT; the manuscript,
original research notes, and documentation use CC BY 4.0, under the
repository's license files. Referenced third-party works retain their own
rights; their full texts and Mathlib's source/cache are not bundled here.
