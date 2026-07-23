# Independent review request

The manuscript proves two claims about OEIS A242322:

1. an exact transfer system on `binomial(k+2,2)` last-occurrence-age states,
   giving a rational generating function and triangular-order characteristic
   recurrence for every column;
2. a closed quartic formula for fixed rows in the exact stable range
   `k>=max(1,n-4)`.

A useful independent review should focus on:

- the initial weight `w(i,j)=i*(j-1)`;
- completeness and multiplicity of the shift/star transitions;
- the unimodularity block argument;
- the induction and limiting case in the boundary-walk lemma;
- the algebra from the boundary lemma to the quartic coefficients;
- whether the scope wording distinguishes characteristic order from minimal
  scalar order.

The complete package is reproducible with:

```bash
make all
make check
```

Please report the smallest concrete counterexample or the exact proof line
that needs revision.  General stylistic feedback is welcome after the
mathematical dependencies have been checked.
