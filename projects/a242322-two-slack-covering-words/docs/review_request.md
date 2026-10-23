# Independent review request

The manuscript proves three claims about OEIS A242322:

1. an exact transfer system on `binomial(k+2,2)` last-occurrence-age states,
   giving a rational generating function and triangular-order characteristic
   recurrence for every column;
2. minimal homogeneous constant-coefficient scalar recurrence order exactly
   `binomial(k+2,2)` for every `k>=1`, including eventual recurrences;
3. a closed quartic formula for fixed rows in the exact stable range
   `k>=max(1,n-4)`.

A useful independent review should focus on:

- the initial weight `w(i,j)=i*(j-1)`;
- completeness and multiplicity of the shift/star transitions;
- the unimodularity block argument;
- the boundary Schur complement and reflected-polynomial identity;
- the exclusion of nonzero left eigenvectors annihilating the boundary vector;
- the reversal form and invertibility of every shifted Hankel matrix;
- the induction and limiting case in the boundary-walk lemma;
- the algebra from the boundary lemma to the quartic coefficients;
- whether the minimality proof avoids assuming the still-conjectural closed
  determinant and Smith normal form formulas.

The complete package is reproducible with:

```bash
make all
make check
```

Please report the smallest concrete counterexample or the exact proof line
that needs revision.  General stylistic feedback is welcome after the
mathematical dependencies have been checked.
