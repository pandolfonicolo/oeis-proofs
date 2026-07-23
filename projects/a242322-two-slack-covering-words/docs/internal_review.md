# Internal adversarial review

Date: 2026-07-23

Status: no blocking mathematical, computational, or rendering defect found.

This is an internal adversarial audit, not independent peer review.

## Proof dependency audit

1. The first valid window contains every alphabet symbol.  Relabeling is
   therefore free, and each orbit has one restricted-growth representative.
2. Last-occurrence ages are distinct, include zero, and are at most `k+2`.
   With `k+1` symbols, exactly two positive ages are missing.
3. If the maximum age is present, its symbol is the unique legal next symbol.
   If it is missing, every symbol is legal.  Updating ages gives exactly the
   stated shift and star transitions.
4. For missing ages `(i,j)`, the first-window orbit count is `i*(j-1)`.
   The two non-last positions have respectively `i` and `j-1` possible later
   last occurrences.
5. Initial weights followed by `n-1` state transitions give
   `T(n,k)=w^T A^(n-1) 1`; summing gives the resolvent generating function.
6. After the row and column ordering in the proof, the transition matrix has a
   permutation block and an identity block on its diagonal.  Its determinant
   is therefore `+1` or `-1`.
7. Cayley-Hamilton gives the characteristic recurrence from `n=N+1`, where
   `N=binomial(k+2,2)`.  No general minimality claim is made.
8. The distance-coordinate recurrence for boundary walks is a direct rewrite
   of the state transitions.  Its closed form follows by strong induction and
   geometric sums, including the limiting case `r=s-1`.
9. Substitution of the boundary lemma into the exact weighted state sum gives
   the quartic row formula for `k>=max(1,n-4)`.
10. The boundary is uniformly sharp because `(n,k)=(6,1)` gives `149`, while
    the stable polynomial gives `151`.

## Computational independence audit

Four structurally different enumeration routes agree:

- literal restricted-growth depth-first enumeration;
- raw labeled last-block DFA divided by the free factorial action;
- equality-pattern suffix quotient;
- last-occurrence-age transfer matrix.

Additional exact checks cover:

- the first `10 x 10` values displayed on OEIS A242322;
- characteristic polynomials, determinant endpoints, and recurrences;
- rational Berlekamp--Massey discovery versus disjoint held-out terms;
- the boundary-walk closed form, including its limiting case;
- the stable formula via both matrix walks and direct closed-lemma summation.

All checks use integer or rational arithmetic and the Python standard library.

## Adversarial failure modes checked

- off-by-one errors among alphabet size, word length, and window length;
- confusion between last-occurrence ages and missing ages;
- a non-free relabeling action;
- transition multiplicities greater than one after quotienting;
- an incorrectly claimed minimal recurrence;
- cancellation reducing the determinant degree;
- applying the stable boundary lemma outside `r>=s-1`;
- interpolation masquerading as proof;
- manual transcription of OEIS rows;
- unresolved LaTeX references, clipped formulas, or unreadable rendering.

## Remaining limitations

- Independent mathematical review is still pending.
- The literature search is qualified and cannot establish absolute priority.
- Minimal scalar recurrence order is computationally verified only for
  `k=1,...,10`; the theorem claims the characteristic order, not general
  minimality.
- No OEIS prose should be copied from the internal notes.  The human
  contributor must understand and write any eventual update personally.
