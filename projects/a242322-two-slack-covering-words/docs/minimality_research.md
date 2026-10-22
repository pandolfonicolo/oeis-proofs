# Minimal scalar order: research note

Exploration begun: 2026-07-23. Updated: 2026-10-23.

Status: **general minimal scalar order is now proved** by the boundary
reflection argument in [general_minimality_proof.md](general_minimality_proof.md)
and the revised manuscript. It gives homogeneous constant-coefficient
recurrence order exactly `binomial(k+2,2)` for every `k>=1`, even when the
recurrence is required to hold only eventually. The proof has been audited
internally; external mathematical review remains pending.

The determinant evaluation and Smith normal form patterns below remain
conjectures. They are preserved as exploratory context and are not needed
for the completed minimality proof. Finite computations do not prove those
stronger formulas.

## The completed argument

The new proof establishes cyclicity without evaluating the controllability
determinant. For a boundary left nullvector `v M_m(z)=0`, put
`V(t)=sum v_d t^d`. Reflection under `t -> z/t` proves that `V(z)` cannot
vanish for a nonzero nullvector. A differentiated polynomial identity gives

```text
(2z-1-z^(m+2)) V(1) = (m-2)(z-1) V(z).
```

For `m=k+1>=3`, a nullvector annihilating the all-one input would therefore
force `z=1`. An elementary prefix-sum induction excludes a nullvector at
that point. Unimodularity excludes eigenvalue zero, and `k=1` is checked by
an explicit three-by-three determinant equal to one. The reversal form
below transfers cyclicity to observability. Every shifted Hankel matrix is
then invertible, excluding even shorter eventual recurrences.

The complete proof spells out each reduction and every exceptional case;
the argument is not an extrapolation from the determinant data below.

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

and `abs(det(O_k)) = abs(det(C_k))`. General scalar minimality therefore
reduces to the single claim `det(C_k) != 0`, now established by the boundary
reflection proof.

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

## Boundary-renewal reduction

There is a second exact reduction which makes the remaining determinant much
more structured.  Put

```text
m = k+1,  r = m+1.
```

Write a state `(i,j)` by its gap and its distance from the boundary:

```text
d = j-i,  s = r-j,
1 <= d <= m,  0 <= s <= m-d.
```

Let `b` be the indicator of the boundary states `(i,r)`, and set

```text
F_d(z) = sum(t >= 0) (A_k^t b)[(r-d,r)] z^t.
```

The deterministic interior transitions imply that the corresponding series
from the state `(d,s)` is simply `z^s F_d(z)`.

On returning from one boundary state to the next, the possible excursion
lengths give

```text
F = 1 + K_m(z) F,
```

where, for `1 <= d,e <= m`,

```text
K_m(z)[d,e]
  = [e <= m+1-d] z^d + [e < d] z^(d-e).
```

Consequently, with

```text
M_m(z) = I - K_m(z),
D_m(z) = det(M_m(z)),
q(z)   = adj(M_m(z)) 1,
```

one has `F_d(z)=q_d(z)/D_m(z)`.  Eliminating the deterministic
interior chains from `I-zA_k` gives, without any extra determinant factor,

```text
D_m(z) = det(I-zA_k).
```

This also produces an explicit polynomial version of the controllability
test.  Since

```text
A_k 1 - 1 = k b,
```

the generating function for the row of the walk matrix belonging to `(d,s)`
is

```text
H_(d,s)(z)
  = (D_m(z) + k z^(s+1) q_d(z)) / ((1-z)D_m(z)).
```

Thus define

```text
p_(d,s)(z)
  = (D_m(z) + k z^(s+1) q_d(z)) / (1-z).
```

The numerator is divisible by `1-z`, and `deg(p_(d,s)) < N`.  Multiplication
of all row series by the common denominator `D_m(z)`, whose constant term is
one, is a unit lower-triangular convolution on the first `N` coefficients.
It follows that

```text
det(C_k)
```

is, up to the harmless row-ordering sign, the determinant of the `N` by `N`
coefficient matrix of the explicit polynomial family

```text
{p_(d,s): 1 <= d <= m, 0 <= s <= m-d}.
```

This is an equivalent finite polynomial-basis problem.

## Sparse form of the boundary system

The boundary matrix has a particularly sparse equivalent form.  Let

```text
Z = diag(z,z^2,...,z^m),
U[d,e] = [d=e] - [e<d],
R[d,e] = [d+e <= m+1].
```

Then

```text
M_m(z) = Z (U - R Z) Z^(-1).
```

Apply the determinant-one row operation which keeps the first row and replaces
every later row by that row minus its predecessor.  The resulting matrix has
first row

```text
(1-z, -z^2, -z^3, ..., -z^m),
```

while row `d`, for `2 <= d <= m`, has only

```text
-2                  in column d-1,
 1                  in column d,
 z^(m+2-d)          in column m+2-d,
```

with entries added when columns coincide.  This explains why powers of two
appear systematically in the experimental determinant.

The same row subtraction applied to

```text
M_m(z) q(z) = D_m(z) 1
```

gives the exact identities

```text
q_1 - z sum(e=1..m) q_e = D_m,

q_d - 2z q_(d-1) + z^d q_(m+2-d) = (1-z)D_m
                                      (2 <= d <= m).
```

These identities provide a concrete route to an induction or a
fraction-free polynomial elimination.

This was the final open step in the original exploration: prove that the
coefficient matrix of the `p_(d,s)` family is nonsingular for every `m`, or
evaluate its determinant from the sparse reflected system above. The new
boundary reflection proof establishes nonsingularity by a different route.
The calculations through `k=15` give the conjectured determinant value in the
preceding section, but neither those calculations nor the sparse reduction
alone prove its exact evaluation.

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

## Resolved minimality and the remaining stronger conjectures

The boundary reflection argument proves nonvanishing of the controllability
determinant for every `k>=1`. Combined with the time-reversal form, this
proves that every column of A242322 has minimal homogeneous
constant-coefficient recurrence order exactly `binomial(k+2,2)`, even if a
recurrence is required to hold only eventually.

- Characteristic recurrence of triangular order: proved for every `k`.
- Minimal scalar order of triangular size, even eventually: proved for every
  `k` by the new general argument.
- The displayed exact determinant evaluation: still conjectural.
- The displayed Smith normal form pattern: still conjectural.

The latter two arithmetic conjectures are independent follow-up questions;
the completed minimality theorem does not assume them.
