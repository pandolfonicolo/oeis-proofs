# A242322 two-slack window-covering words

This directory contains a proof draft and reproducibility package for OEIS
A242322.  The manuscript is ready for independent mathematical review, but it
has not been externally reviewed and is not yet an OEIS submission package.

For `q = k+1`, A242322 counts canonical restricted-growth words of length
`n+q+1` in which every consecutive block of length `q+2` contains all `q`
symbols.  Thus it is the two-slack counterpart of A242239.

## Main results

- an exact last-occurrence-age automaton with `binomial(k+2,2)` states;
- an explicit transfer-matrix generating function for every column;
- a characteristic recurrence of triangular order;
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
- `docs/` - acceptance criteria, research log, and adversarial review;
- `oeis/` - internal mathematical notes, not submission prose.

## Reproduce

```bash
make all
make check
```

The verifiers use only the Python standard library.  The manuscript build also
requires `latexmk` and a standard LaTeX installation.
