# General minimality for A242322

Date: 23 October 2026.

Status: complete algebraic proof; internally audited. External mathematical review remains pending.
This argument does not use the experimental determinant formula.

## 1. Statement and transfer matrix

Fix an integer `k >= 1`, and put `r = k+2`, `m = r-1 = k+1`, and
`N = binomial(r,2)`. Index the coordinates of `C^N` by pairs `(i,j)` with
`1 <= i < j <= r`. Define the row transition matrix `A` by

- if `j < r`, `(A f)(i,j) = f(i+1,j+1)`;
- if `j = r`, `(A f)(i,r) = sum_{u != i+1} f(min(i+1,u),max(i+1,u))`.

Let `u` be the all-one column vector, `w(i,j)=i(j-1)`, and
`T(n,k)=w^T A^(n-1) u` for `n >= 1`, as in the existing enumeration theorem.

**Theorem.** The least order of a homogeneous constant-coefficient scalar recurrence for
`T(n,k)` is exactly `N`, even if the recurrence is required to hold only
eventually.

The proof has two independent parts: `u` is cyclic for `A`, and a
nondegenerate reversal form transfers this to observability by `w`.

## 2. Invertibility of A

Write `e_(i,j)` for the coordinate basis. The transition rule gives

```
A e_(1,j) = e_(j-1,r),

A e_(i,j) = e_(i-1,j-1) + e_(i-1,r) + e_(j-1,r)   (i >= 2).
```

In the domain, put the `r-1` vectors with `i=1` first. In the codomain,
put the `r-1` boundary vectors `e_(a,r)` first. The first formula is a
bijection between these two groups. On the remaining vectors, projection
onto the nonboundary coordinates sends `e_(i,j)` to `e_(i-1,j-1)`, again
bijectively. Thus, after row and column permutations, `A` has block form

```
[ I  B ]
[ 0  I ].
```

In particular, `det A = +/-1`, and zero is not an eigenvalue.

## 3. Reduction of cyclicity to a boundary matrix

Let `b(i,j)=[j=r]`. Row sums of the transition matrix give

```
(A-I)u = k b.                                      (3.1)
```

Suppose that `u` is not cyclic. Its Krylov span is a proper invariant
subspace of `C^N`; its annihilator is a nonzero invariant subspace for the
dual map. Since we work over `C`, this annihilator contains a nonzero left
eigenvector `ell` of `A`. Thus for some `lambda`,

```
ell A = lambda ell,       ell u = 0.
```

Equation (3.1) and `k != 0` imply `ell b=0`. Section 2 shows `lambda != 0`;
put `z=1/lambda`, so `ell (I-zA)=0`.

Use coordinates `(d,s)` with

```
d = j-i,    s = r-j,
1 <= d <= m,    0 <= s <= m-d.
```

The boundary coordinates are exactly `(d,0)`, `1 <= d <= m`. At every
nonboundary coordinate, the matrix equation `(I-zA)f=g` reads

```
f_(d,s) - z f_(d,s-1) = g_(d,s)       (s >= 1).
```

Order the boundary coordinates first. In block form write

```
I-zA = [ B  C ]
       [ D  E ].
```

The interior block `E` is triangular with diagonal ones, hence invertible
for every `z`. With zero interior forcing, eliminate the interior values:
`f_(d,s)=z^s f_(d,0)`. The resulting boundary Schur complement is

```
M_m(z) = B - C E^(-1) D = I-K_m(z),

K_m(z)[d,e] = [e <= m+1-d] z^d + [e < d] z^(d-e).    (3.2)
```

For completeness, start from boundary state `(r-d,r)` and write the newly
chosen other endpoint as `a`, with `a != r-d+1`.

- For `a < r-d+1`, the target has gap `e=r-d+1-a`, boundary distance `d-1`,
  and return length `d`. These are `1 <= e <= m+1-d`.
- For `a > r-d+1`, the target has gap `e=a-(r-d+1)`, boundary distance
  `d-1-e`, and return length `d-e`. These are `1 <= e < d`.

These are exactly the two terms in (3.2), including their multiplicity when
both types give the same gap.

Decompose `ell=(v,h)` compatibly. The right block of
`ell(I-zA)=0` says `h=-v C E^(-1)`; the left block then says `v M_m(z)=0`.
Moreover, `v != 0`, since otherwise `h=0`. Since `b=(1,...,1,0,...,0)`,
the equation `ell b=0` says `v 1=0`.

It remains to prove:

**Boundary lemma.** If `m >= 3`, `z != 0`, `v M_m(z)=0`, and `v 1=0`,
then `v=0`.

## 4. A generating-polynomial identity for a left nullvector

Let `v=(v_1,...,v_m)` satisfy `v M_m(z)=0`, and define

```
V(t) = sum_(d=1)^m v_d t^d.
```

The `e`-th component of the nullvector equation is

```
v_e = sum_(d <= m+1-e) v_d z^d
      + sum_(d > e) v_d z^(d-e).                    (4.1)
```

Multiply by `t^e`, sum over `e`, and use the finite geometric sums. In the
rational-function field `C(t)` this yields

```
V(t) = t/(1-t) * (V(z)-t^(m+1)V(z/t))
       + (t V(z)-z V(t))/(z-t).
```

Multiplication by `(1-t)(z-t)` and collection of terms gives

```
a(t) V(t) = c(t) V(z) + b(t) V(z/t),              (4.2)

a(t) = (1-t)(2z-t),
b(t) = -t^(m+2)(z-t),
c(t) = t(z+1-2t).
```

All denominators here are formal rational functions of the indeterminate
`t`. No evaluation at `t=1` or `t=z` was used in division.

Replace `t` by `z/t` in (4.2), multiply the original equation by `a(z/t)`,
and eliminate `V(z/t)`. The result is

```
(a(t)a(z/t)-b(t)b(z/t)) V(t)
 = (c(t)a(z/t)+b(t)c(z/t)) V(z).                  (4.3)
```

Direct multiplication gives

```
a(t)a(z/t)-b(t)b(z/t)
 = z(1-t)(t-z)/t^2 * Q_z(t),

Q_z(t) = -2t^2 + (4z+1-z^(m+2))t - 2z.           (4.4)
```

Since `z != 0` and the leading coefficient of `Q_z` is `-2`, the rational
function on the left of (4.4) is nonzero. Consequently (4.3) proves that

```
v != 0  implies  V(z) != 0.                       (4.5)
```

Indeed, if `V(z)=0`, equation (4.3) in the integral domain `C(t)` forces
`V(t)=0`, and therefore every coefficient `v_d` is zero.

The other factor in (4.3) expands as

```
c(t)a(z/t)+b(t)c(z/t) = z(t-z)/t * R_z(t),

R_z(t) = (z+1-2t)(2t-1)
         + t^(m+1)((z+1)t-2z).                   (4.6)
```

Cancel the nonzero rational function `z(t-z)/t^2` from (4.3). This gives the
polynomial identity

```
(1-t) Q_z(t) V(t) = t R_z(t) V(z).               (4.7)
```

At `t=1`, direct evaluation and differentiation of (4.6) give

```
R_z(1)=0,
R_z'(1)=(m-2)(1-z).
```

Differentiate (4.7) and evaluate at `t=1`. Since
`Q_z(1)=2z-1-z^(m+2)`, one obtains

```
(2z-1-z^(m+2)) V(1) = (m-2)(z-1) V(z).          (4.8)
```

No division by `Q_z(1)` occurs, so (4.8) also holds when it vanishes.

If now `m>=3`, `v!=0`, and `v 1=V(1)=0`, equations (4.5) and (4.8) force
`z=1`.

## 5. The exceptional point z=1

Every row of `K_m(1)` has sum `m`, so

```
M_m(1) 1 = (1-m) 1.
```

For a left nullvector, multiplication by `1` gives `V(1)=0` when `m>=2`.
Let `S_e=sum_(d=1)^e v_d`, with `S_0=0`. Equation (4.1) at `z=1`, using
`S_m=0`, becomes

```
2S_e-S_(e-1) = S_(m+1-e)       (1 <= e <= m).    (5.1)
```

Starting from `S_0=S_m=0`, the equations with `e=1,m,2,m-1,...` successively
give

```
S_1=S_(m-1)=S_2=S_(m-2)=...=0.
```

More explicitly, if `S_(j-1)=S_(m+1-j)=0`, equation `e=j` gives `S_j=0`;
then equation `e=m+1-j` gives `S_(m-j)=0`. Induction reaches all indices.
Thus every `v_d=S_d-S_(d-1)` is zero. This proves that `M_m(1)` is
invertible, and finishes the boundary lemma.

Sections 3--5 prove that `u` is cyclic for `A` when `k>=2`.

## 6. The remaining small case k=1

In the state order `(1,2),(1,3),(2,3)`,

```
A = [0 0 1]
    [1 0 1]
    [0 1 1],

[u,Au,A^2u] = [1 1 2]
               [1 2 3]
               [1 2 4].
```

The latter determinant is `1`. Thus `u` is cyclic for every `k>=1`.

## 7. The reversal form and observability

Define

```
J[(i,j),(a,b)]
 = [i+a >= r+1 and j+b >= r+1]
   + [i+b >= r+1 and j+a >= r+1].                 (7.1)
```

This matrix is symmetric. To see that it is unimodular, reverse each column
pair by `(a,b)=(r+1-q,r+1-p)` for `p<q`. Its entry becomes

```
[i >= q] + [i >= p and j >= q].
```

Both terms vanish unless `(i,j)` is componentwise at least `(p,q)`, and the
diagonal entry is exactly one. In any linear extension of componentwise
order, the column-reversed matrix is unit lower triangular. Hence
`det J=+/-1`.

For fixed `(i,j)`, summing (7.1) over unordered pairs is the same as counting
ordered distinct pairs `(a,b)` with `a>=r+1-i`, `b>=r+1-j`. There are
`ij-i=i(j-1)` such pairs. Therefore `J u=w`.

Using the basis formulas in Section 2, put `L=r+2`. Direct multiplication
gives the following explicit entry of `JA`:

```
(JA)[(i,j),(a,b)]
 = [i+a>=L][j+b>=L] + [i+b>=L][j+a>=L]
   + [i+a>=L] + [j+a>=L] + [i+b>=L] + [j+b>=L].
```

The same expression holds when `a=1`, because all terms involving `i+a`
or `j+a` then vanish. The displayed expression is symmetric under exchanging
the two pairs. Thus `JA` is symmetric, i.e. `A^T J=JA`.

Let

```
C = [u,Au,...,A^(N-1)u],
O = [w^T;w^T A;...;w^T A^(N-1)].
```

The identities just proved imply `O^T=JC`. Both `J` and `C` are invertible,
so `O` is invertible as well.

## 8. Minimality, including eventual recurrences

For any integer `L>=0`, form the `N` by `N` shifted Hankel matrix

```
H_L[a,b] = T(L+a+b+1,k),     0 <= a,b < N.
```

The transfer formula gives `H_L=O A^L C`, which is invertible by Sections
2, 6, and 7. If an eventual scalar recurrence of order `d<N` existed, choose
`L` large enough for every recurrence used in `H_L` to be valid. The column
with index `d` would then be a linear combination of the preceding `d`
columns, contradicting invertibility. Hence no eventual recurrence of order
less than `N` exists.

Cayley--Hamilton supplies a recurrence of order at most `N`. Its leading
and trailing characteristic coefficients are nonzero because `A` is
invertible. Therefore the least order is exactly `N`, proving the theorem.

## What this does and does not establish

This proof establishes general scalar minimality without evaluating `det C`.
The experimental closed determinant and Smith normal form formulas remain
separate conjectures; the minimality theorem does not depend on either one.
