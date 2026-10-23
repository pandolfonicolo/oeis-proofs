> Status update, 2026-10-23: this file preserves the staged conventional
> audit performed before formal completion. Its historical references to an
> unfinished Lean proof are superseded by the complete concluding kernel
> check and the release verification evidence. The conventional mathematical
> verdict below is unchanged; this audit is not itself the Lean certificate.

# Independent audit of the assembled A354766/A278085 manuscript

Date: 2026-10-23.

Sources reviewed: `main.tex`, `three_squares.tex`, and the preceding
independent lattice audit. I also checked the primary OEIS definitions at
https://oeis.org/A354766 and https://oeis.org/A278085.

## Verdict

No blocking mathematical error was found in the assembled conventional
proof. The lattice product, corrected parity bridge, divisibility by four,
multiplicativity, local formulas, equality classification, and finite sieve
fit together with the same normalization. The finite computations are
properly separated from proof steps. The manuscript clearly does not claim
that the remaining Lean obligation has been discharged.

The initial source-definition clarification for A278085, detailed below,
has now been incorporated and rechecked. It does not require a new theorem
about representations.

## 1. OEIS normalization and the A278085 definition

A354766 is one quarter of the raw total count with sum `n` and square sum
`n^2`, exactly the function called `T` here. A278085's primary definition
uses sum `3n` and square sum `3n^2`; its own comments identify it also as
one quarter of the primitive count for sum `n`, square sum `n^2`, which is
the manuscript's `P`.

To prove that identification directly, add the following bijection. For a
quadruple `q=(h,i,j,k)`, set

`C_n(q)=(n-h,n-i,n-j,n-k)`.

If `sum(q)=n` and `sum(q_i^2)=n^2`, then

`sum(C_n(q))=3n`,

`sum((n-q_i)^2)=4n^2-2n*sum(q)+sum(q_i^2)=3n^2`.

The same involution sends the latter equations back to the former.
It preserves coordinate content. The content of `q` divides `n` by its
coordinate sum and therefore divides every coordinate of `C_n(q)`.
Conversely, if `d` is the positive content of `C_n(q)`, then
`d^2` divides `3n^2`. Prime valuations give `d|n`: for every prime, including
three, `2v_p(d)<=v_p(3)+2v_p(n)` forces `v_p(d)<=v_p(n)`.
Thus `d` divides `n-C_n(q)_i=q_i` for each coordinate. This proves equality
of the two contents and hence a bijection of primitive quadruples.

The valuation argument in the current odd-divisor lemma in fact does not
need the oddness hypotheses; either generalize that lemma or include the
one-sentence valuation argument here. The main proof is already consistent
with OEIS's explicitly stated alternate definition, but this addition makes
the connection to the primary definition self-contained.

## 2. Corrected Hadamard bridge

For odd `n`, three squares summing to `3 mod8` must all be `1 mod8`, so the
three coordinates are odd. The four inverse numerators are congruent mod4.
The two signs of a triple give residues `n+S` and `n-S`, exactly one of
which vanishes mod4. No sign-pair has a fixed point because the norm is
positive. The odd gcd argument proves equivalence of primitivity for the
integral inverse, giving exactly `pq(n)=F(n)/2`.

For `n=2m` with `m` odd, the unnormalized triple is necessarily even.
After halving, its norm is `3m^2` and its three coordinates are odd.
The inverse quadruple is integral and all four coordinates have the same
parity. Negating the triple exchanges an all-odd quadruple with an all-even
one. A primitive normalized triple therefore contributes exactly one
primitive quadruple per sign-pair. Nonprimitive normalized triples contribute
none, using the same odd-gcd argument with denominator two. Thus the middle
case is `F(m)/2`, with the corrected level `m=n/2`.

When `4|n`, parity of the coordinate sum and the square sum modulo four
and eight exclude exactly two or four odd coordinates. Every quadruple is
even, so its primitive count vanishes. All three cases are exhaustive.

## 3. Product formula and arithmetic consequences

The included lattice proof has the same `F(m)` convention throughout:
ordered signed primitive vectors of norm `3m^2`, with `m` positive odd.
I rechecked the neighbor double count, including primitivity away from `p`,
the valuation-one inside contribution, and the exceptional prime three.
The recurrences remove each prime-power factor of `m`, starting from
`F(1)=8`, and give precisely the product used in the main manuscript.

That product is eight times an integer. The bridge therefore makes every
raw primitive count divisible by four before `P` is treated as integer
valued. The content decomposition is a disjoint finite bijection, so it
makes the raw total count divisible by four and gives `T=sum_{d|n}P(d)`.
No rounded natural-number division is interchanged with a sum.

Disjoint prime factors give multiplicativity of `P`; the two-adic factor
is consistent because at most one of two coprime arguments is even.
The divisor factorization then proves multiplicativity of `T`.
The four local cases at 2, 3, primes `1 mod6`, and primes `5 mod6` are the
correct finite geometric sums of the primitive local factors.

## 4. Equality classification

For every odd prime power, `T(p^a)=1 mod3`. This excludes equality when
three divides `n`. Once three is excluded, the odd part's total count is
odd. For a positive two-adic exponent, `T(n)` has exact two-adic valuation
one, so equality forces that exponent to equal one. This correctly prevents
compensation between high powers of two and larger odd-prime factors.

For the remaining cases, every odd local ratio `T(p^a)/p^a` is at least
one; it is one exactly for primes `1 mod6` and strictly larger for primes
`5 mod6`. Multiplication gives the stated necessary and sufficient
classification, including the empty factorization and `n=1,2`.

## 5. Finite density argument

For admissible `q`, coprimality with six justifies the CRT bijection counting
exactly `phi(q)` candidates in `[1,6q]`. Each candidate has a prime factor
`5 mod6` outside `q`, so the finite union bound gives the claimed reciprocal
sum lower bound. Totient multiplicativity and
`p/(p-1)>=1+1/p` give the gain `b(q')>=b(q)+1/6`.
The iteration starts from `q=1`, is explicitly finite at every step, and
produces `phi(q_t)/q_t<=6/(t+6)`. No assertion about infinite prime sums or
Dirichlet density is hidden in this construction.

Finally, counting complete residue blocks and one incomplete block gives
the stated finite cardinality bound. The chosen fixed modulus and explicit
epsilon threshold prove a natural-density limit rather than assuming that
the limit already exists. Applying the exact equality characterization is
therefore valid.

## Formal boundary

This audit concerns the conventional mathematical manuscript. It does not
certify a Lean proof of the primitive three-square theorem or the complete
original Formal Conjectures submission. The current manuscript's explicit
statement that this formal work remains incomplete is correct and must be
retained.

## Final recheck after the source-definition addition

The assembled manuscript now contains the explicit A278085 complement
bijection immediately after the common-divisor lemma. That lemma has been
correctly generalized to all positive `d,m`, with exactly the same valid
prime-valuation proof. The complement involution's content argument is
correct in both directions and closes the source-definition connection
noted above. The equality-density corollary now explicitly identifies the
positive-density conjecture as false; this is a valid deduction from the
proved limit zero for exactly the OEIS-normalized total count.

After this recheck, there is no remaining requested mathematical repair in
this audit. This remains an internal independent-agent audit of the written
argument, with external human review and Lean formal completion distinct.

## Focused inspection of formal foundations

Read-only inspection of the pinned Mathlib sources confirms that substantial
standard foundations exist:

- `MeasureTheory/Group/GeometryOfNumbers.lean` proves
  `exists_ne_zero_mem_lattice_of_measure_mul_two_pow_lt_measure`, the strict
  Minkowski convex-body theorem needed for the open ball argument.
- `Algebra/Module/ZLattice/Covolume.lean` provides
  `ZLattice.covolume_eq_det` and
  `ZLattice.covolume_div_covolume_eq_relIndex` (plus a general-space primed
  version). Thus covolume and index machinery need not be built from scratch.
- `LinearAlgebra/QuadraticForm/IsometryEquiv.lean` supplies quadratic-form
  isometries and diagonalization through
  `QuadraticForm.isometryEquivWeightedSumSquares`.
- `NumberTheory/LegendreSymbol/QuadraticChar/Basic.lean` supplies
  `quadraticChar_card_sqrts`, the finite-field square-root count used in the
  binary-form line count. Quadratic reciprocity has its own existing module.

In these relevant sources I did not find packaged theorems that already
implement the following specific bridges from this manuscript. These are
the concrete new formal obligations, rather than new mathematical
conjectures:

1. From integrality, positive definiteness, covolume one, and rank at most
   three, construct an orthonormal integer basis: apply Minkowski to obtain
   a norm-one vector, split off its integer orthogonal summand, transfer
   covolume, and induct on rank.
2. Define the isotropic one-dimensional subspaces of the standard ternary
   form over `ZMod p`, prove their count `p+1`, and prove that those in a
   nonzero vector's orthogonal plane number
   `1 + legendreSym p (-Q(x))`, including the isotropic-vector case.
3. Define the normalized lift modulo `p^2`, the kernel lattice `M`, and the
   neighbor `M+Z(u/p)`; prove lift independence, integrality, the two indices,
   intersection with `Z^3`, covolume one, and the resulting integer isometry.
4. Prove the primitive-vector bijections across neighbors, including the
   Bezout argument away from `p` and the unique neighbor for `v/p`.
5. Express the finite disjoint-pair count as the two primitive recurrences,
   then derive the prime-power induction and Euler product in the existing
   finite representation-count definitions.

The written proofs of all five items are present in `three_squares.tex`.
What remains is to turn them into definitions and checked proof terms and
connect those terms to the recovered `r3PrimitiveFinite` function. Merely
adding the names of these items as assumptions would not close the formal
gap. No additional Lean process was started for this source inspection.
