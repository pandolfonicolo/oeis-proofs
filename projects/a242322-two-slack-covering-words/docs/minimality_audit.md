# Independent audit of the general A242322 minimality argument

Date: 2026-10-23.

Target: `general_minimality_proof.md`, independently compared
with the transfer matrix in `verify_a242322_theorems.py` and the previous
research note. This audit does not take the numerical determinant checks as
evidence sufficient for the theorem.

## Verdict

The argument proves the stated general minimality theorem over the complex
numbers, and hence over the rationals or reals: for every integer `k >= 1`,
the scalar sequence `T(n,k)` has least constant-coefficient recurrence order
`binomial(k+2,2)`, including eventual recurrences. I found no mathematical
gap in the argument after independently deriving its algebra and checking
the exceptional cases below.

This verdict is conditional only on the already-established exact
enumeration/transfer formula for `T(n,k)` from the existing manuscript.
It does not assume the experimental closed determinant or Smith formulas.
It is an audit of a written mathematical proof, not a Lean certification.

## 1. Transfer matrix and invertibility

The basis action stated in the proposed proof agrees exactly with the row
transition convention in the enumeration script. For a target pair `(a,b)`:

- If `a=1`, there is exactly one predecessor, the boundary state `(b-1,r)`.
- If `a>=2`, there is one interior predecessor `(a-1,b-1)` and the two
  distinct boundary predecessors `(a-1,r)` and `(b-1,r)`.

After putting the `a=1` columns first and all boundary rows first, the two
diagonal blocks are permutation identities. The interior block is square
because both its source and target index sets have `binomial(r-1,2)`
elements. Therefore `det A=+/-1`. In particular, the eigenvalue zero and
loss of rank under time shifts are genuinely excluded.

The row sums are 1 at interior states and `r-1=m` at boundary states, so
`(A-I)u=(m-1)b=k b` is correct.

## 2. PBH argument and boundary elimination

If the Krylov span of `u` is proper, its annihilator is invariant under
right multiplication by `A`. A nonzero finite-dimensional complex invariant
space contains an eigenvector. Thus the proof legitimately obtains a
nonzero left eigenvector `ell` with `ell u=0`. The identity above then gives
`ell b=0`; no converse or unjustified rank equivalence is being assumed.

Writing `z=1/lambda` is permitted because `A` is invertible. In `(d,s)`
coordinates, every interior row of `I-zA` is
`f(d,s)-z f(d,s-1)`. Consequently the interior block has determinant one for
every complex `z`, not merely at nonsingular values of the full matrix.

The two types of boundary excursions respectively have return lengths `d`
and `d-e`. They produce exactly

`K[d,e]=[e<=m+1-d] z^d + [e<d] z^(d-e)`.

For a left nullvector, the block equations give
`h=-v C E^(-1)` and `v(B-C E^(-1)D)=0`. Therefore the surviving boundary
vector `v` is nonzero. Since `b` is one on boundary coordinates and zero
elsewhere, `ell b=0` means precisely `sum v_d=0`. The input vector in the
boundary problem has not silently changed.

## 3. Generating-polynomial calculation

For `V(t)=sum_{d=1}^m v_d t^d`, independently summing the nullvector equation
over `e` gives

`V(t)=t/(1-t)(V(z)-t^(m+1)V(z/t))+(t V(z)-z V(t))/(z-t)`.

The first term uses `sum_{e=1}^{m+1-d} t^e`; the second uses
`sum_{e=1}^{d-1} t^e z^(d-e)`. Hence the endpoints and both exponents are
correct, including the zero second sum when `d=1`.

Put `a=(1-t)(2z-t)`, `b=t^(m+2)(t-z)`, and `c=t(z+1-2t)`.
The equation is `a V=c V(z)+b V(z/t)`. The substitution `t -> z/t` is an
automorphism of `C(t)` because `z != 0`. Eliminating `V(z/t)` is therefore
valid without restrictions such as `z != 1` or `Q_z(1) != 0`.

The reflected coefficients can be checked directly without any numerical
specialization:

`a(z/t)=z(t-z)(2t-1)/t^2`,

`b(z/t)=z^(m+3)(1-t)/t^(m+3)`.

It follows that

`a(t)a(z/t)-b(t)b(z/t)`

`=z(1-t)(t-z)/t^2 * ((2z-t)(2t-1)-z^(m+2)t)`.

Thus `Q_z(t)=-2t^2+(4z+1-z^(m+2))t-2z` is exactly the polynomial in the
proposal. Its leading coefficient `-2` makes it nonzero over `C` for every
constant `z`. In particular, `V(z)=0` forces `V(t)=0` in the rational-function
field; this is a general argument, not a finite test.

Similarly,

`c(t)a(z/t)+b(t)c(z/t)`

`=z(t-z)/t * ((z+1-2t)(2t-1)+t^(m+1)((z+1)t-2z))`.

Cancellation therefore yields precisely `(1-t)Q_z(t)V(t)=t R_z(t)V(z)`.
The cancelled rational function is nonzero even at the exceptional constant
`z=1`, since `t` is still an indeterminate.

Independent differentiation gives `R_z(1)=0` and
`R_z'(1)=(m-2)(1-z)`. Hence

`Q_z(1)V(1)=(m-2)(z-1)V(z)`.

Since `m>=3`, `m-2` is nonzero over `C`. If `v` is nonzero and `V(1)=0`,
the preceding facts force `z=1`. No division by `Q_z(1)` is required.

## 4. The exceptional point and smallest parameter

At `z=1`, the constant row sum of `K` gives `sum v_d=0` for every left
nullvector when `m>=2`. With prefix sums `S_e`, the equation becomes

`2 S_e-S_(e-1)=S_(m+1-e)`.

Starting with `S_0=S_m=0`, the equations at `e=1,m,2,m-1,...` force every
prefix sum to vanish. One may make the bounds explicit by iterating
`j=1,...,ceil(m/2)`; the two ends meet at the central index. The proposal's
induction is valid, but this explicit bound would improve presentation.

Thus `M_m(1)` is invertible. For `k=1`, the displayed three-by-three Krylov
matrix has determinant 1. All positive integer parameters are covered.

## 5. Reversal form and scalar observability

The column reversal in `J` gives
`[i>=q]+[i>=p and j>=q]` for `p<q`. This has support only above a
componentwise-lower pair, with diagonal entry exactly one. Therefore a
linear extension gives the claimed unit triangular matrix and `det J=+/-1`.

For fixed `(i,j)`, the row sum counts ordered distinct pairs in sets of
sizes `i` and `j`; their intersection has size `i`. Hence the row sum is
`ij-i=i(j-1)=w(i,j)`.

For a column `(a,b)` with `a>=2`, the three basis predecessors produce the
stated entry of `JA`: two products of threshold indicators plus the four
single indicators. When `a=1`, all terms containing `i+a` or `j+a` vanish,
and the two remaining terms give exactly the sole boundary predecessor.
Thus the formula is correct in every column. Its symmetry gives
`A^T J=JA`, and therefore `O^T=JC`. Observability follows without requiring
`J` to be positive definite or `A` to have simple eigenvalues.

## 6. Eventual rather than merely initial recurrence order

The shifted Hankel factorization is exactly

`H_L[a,b]=T(L+a+b+1,k)=(O A^L C)[a,b]`.

Every factor is invertible for every integer `L>=0`. An eventual recurrence
of order `d<N` makes column `d` a fixed linear combination of columns
`0,...,d-1` when `L` is large enough. This contradicts invertibility.
The argument also excludes eventual order zero. Cayley--Hamilton supplies
the matching upper bound, so the least order is exactly `N`.

## Scope of the conclusion

The proof closes the general scalar minimality question. It does not
evaluate the Krylov determinant's absolute value or its Smith normal form.
Those stronger formulas can remain explicitly labelled conjectural without
leaving any gap in the minimality theorem proved here.
