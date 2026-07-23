# Research log

## 2026-07-23 — feasibility study opened

The live A242322 entry describes empirical column recurrence orders
`3, 6, 10, 15, 21, 28` for `k=1,...,6`, suggesting
`binomial(k+2, 2)`.  It also displays empirical quartic formulas for fixed
rows.  Neither pattern is treated as proved here.

Initial objective: independently reconstruct the table and test both patterns
with discovery and hold-out ranges kept separate.

Source checked 2026-07-23:
https://oeis.org/A242322

## 2026-07-23 — initial computation

All initial feasibility checks pass:

- an explicit classification of equality patterns agrees with its independent
  binomial count through `q=30`;
- literal restricted-growth enumeration agrees with the quotient transfer
  computation for `k=1,...,3`, `n=1,...,6`;
- the raw labeled suffix DFA agrees with the quotient for `k=1,...,4`,
  `n=1,...,15`;
- the quotient reproduces the first `10 x 10` displayed OEIS values;
- rational Berlekamp--Massey fits on `n=1,...,60` predict the disjoint range
  `n=61,...,100`, with orders `3, 6, 10, 15, 21, 28`;
- the candidate stable range has vanishing fifth finite differences on four
  held-out values for rows `n=1,...,12`.

Interpretation: this is a positive feasibility result.  The recurrence orders
and quartic rows remain conjectural until derived symbolically from a proved
quotient structure.

## 2026-07-23 — proof-grade reduction

The last-occurrence ages of the `k+1` symbols are distinct, include zero, and
lie in `0,...,k+2`.  A valid prefix is therefore represented by the two missing
positive ages.  This gives exactly `binomial(k+2,2)` states.

The transition rule, initial weights, transfer generating function,
unimodularity, characteristic recurrence, boundary-walk lemma, and stable
quartic formula were derived and written as explicit proofs.  Two exact
verifiers now provide fourteen complementary feasibility and theorem-oriented
checks.

Current status: draft for independent mathematical review.  No OEIS update has
been prepared or proposed from this project.
