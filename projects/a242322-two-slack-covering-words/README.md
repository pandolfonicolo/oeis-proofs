# A242322 two-slack window-covering words

This directory contains a public manuscript and reproducibility package for
OEIS A242322. The October 23, 2026 revision adds a general proof of minimal
scalar recurrence order. Internal audits are recorded separately from the
independent external mathematical review, which is still pending.

For `q = k+1`, A242322 counts canonical restricted-growth words of length
`n+q+1` in which every consecutive block of length `q+2` contains all `q`
symbols.  Thus it is the two-slack counterpart of A242239.

## Main results

- an exact last-occurrence-age automaton with `binomial(k+2,2)` states;
- an explicit transfer-matrix generating function for every column;
- a recurrence whose minimal scalar order is exactly `binomial(k+2,2)` for
  every `k >= 1`, even when a competing recurrence is required only eventually;
- a proved quartic formula for every row when `k >= max(1,n-4)`.

The research and publication gate is recorded in
[`docs/acceptance_criteria.md`](docs/acceptance_criteria.md).  Passing the
computational checks supports but does not replace the written proof or
independent review.

## Contents

- `manuscript/` - LaTeX source and compiled review draft;
- `verification/verify_a242322_feasibility.py` - independent discovery and
  definition-only checks;
- `verification/verify_a242322_theorems.py` - proof-oriented exact checks;
- `verification/check_minimality_identities.py` - exact checks of the new
  proof's reflection identities and boundary elimination;
- `verification/explore_minimality.py` - exploratory exact checks of the
  stronger determinant formula, which remains conjectural;
- `docs/` - acceptance criteria, research log, and adversarial review;
- `docs/general_minimality_proof.md` - complete algebraic minimality proof;
- `docs/minimality_audit.md` - separate internal audit of the general proof;
- `docs/minimality_research.md` - research history and the remaining stronger
  determinant and Smith normal form conjectures;
- `oeis/` - internal mathematical notes, not submission prose.

## Reproduce

```bash
make all
make check
```

The verifiers use only the Python standard library.  The manuscript build also
requires `latexmk` and a standard LaTeX installation.

The separate exploratory minimality check can be reproduced with

```bash
python3 verification/explore_minimality.py --max-k 15
```

Passing that finite check is evidence for the determinant formula recorded in
`docs/minimality_research.md`, not a proof of it.
