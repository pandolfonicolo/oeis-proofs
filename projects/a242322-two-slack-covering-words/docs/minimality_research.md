# Minimal scalar order: research note

Date: 2026-07-23

Status: partial structural result and a strongly supported determinant
conjecture.  This note is not a proof of general minimality and must not be
cited as one.

## Question

Let

```text
N = binomial(k+2, 2)
```

and let `A_k`, `w_k`, and `1` be the transfer matrix, initial vector, and
terminal vector from the manuscript.  Cayley--Hamilton proves a scalar
recurrence of order `N` for

```text
T(n,k) = w_k^T A_k^(n-1) 1.
```

The recurrence is minimal precisely when no factor cancels from the scalar
generating function.  A sufficient and necessary state-space formulation is
that

```text
C_k = [1, A_k 1, ..., A_k^(N-1) 1]
```

is nonsingular and that the corresponding observability matrix is
nonsingular.

## A proved reduction: time-reversal form

Put `r = k+2`, and index rows and columns by pairs
`(i,j)` with `1 <= i < j <= r`.  Define

```text
J_k[(i,j),(u,v)]
  = [i+u >= r+1 and j+v >= r+1]
  + [i+v >= r+1 and j+u >= r+1].
```

Direct substitution in the transition rules gives

```text
A_k^T J_k = J_k A_k,
J_k 1 = w_k.
```

The form is symmetric.  It is also unimodular.  To see this, reverse a column
pair by

```text
(u,v) -> (r+1-v, r+1-u) = (p,q).
```

The resulting entry is

```text
[i >= q] + [i >= p and j >= q].
```

Both summands vanish unless `(i,j)` is componentwise at least `(p,q)`, and
the diagonal entry is one.  In any linear extension of componentwise order,
the column-reversed matrix is unit lower triangular.

Consequently, if

```text
O_k = [w_k^T; w_k^T A_k; ...; w_k^T A_k^(N-1)],
```

then

```text
O_k^T = J_k C_k
```

and `abs(det(O_k)) = abs(det(C_k))`.  General scalar minimality therefore
reduces to the single claim `det(C_k) != 0`.

## Determinant conjecture

Exact fraction-free computation through `k=15` gives the following formula.
For `k >= 2`, set

```text
N = binomial(k+2, 2),
M = binomial(k+1, 2) - 1.
```

The conjecture is

```text
abs(det(C_k)) = 2^e(k) * k^(N-1) * (k-1)^M,
```

where

```text
e(2m)   = m*(m-1)*(2m+3)/2,
e(2m+1) = m^2*(m+2).
```

For `k=1`, `abs(det(C_1))=1`.

The factors `k^(N-1)` have an elementary first explanation:

```text
A_k 1 - 1 = k*b,
```

where `b` is the indicator of the boundary states.  Successive column
differences therefore extract `k` from every column of `C_k` except the
first.  A complete proof must still account for the `(k-1)` and `2` factors
and show that no further factor remains.

## Additional exact evidence

The Smith normal forms computed for `k <= 8` follow a sharper pattern:

```text
1                                      (multiplicity 1),
k                                      (multiplicity k+1),
k*(k-1)                                (multiplicity 2),
2^j*k*(k-1)                            (multiplicity k+3)
```

for the full blocks `j = 1,...,floor((k-2)/2)`.  If `k` is odd, there is one
final block

```text
2^((k-1)/2)*k*(k-1)                    (multiplicity (k+3)/2).
```

This Smith pattern implies the determinant conjecture, but it is itself only
computational evidence at present.

## What a complete proof would yield

A proof of the determinant formula, or merely of its nonvanishing, combined
with the time-reversal form above would prove that the scalar recurrence for
every column of A242322 has minimal order exactly
`binomial(k+2,2)`.  Until that last step is supplied, the manuscript's current
distinction remains necessary:

- characteristic recurrence of triangular order: proved for every `k`;
- minimal scalar order: checked for a finite range, not proved in general.

