import A354766.PrimitiveTransport
import A354766.PrimitiveVectorModel
import A354766.ShellEquivalence
import Mathlib.Algebra.GroupWithZero.Basic
import Mathlib.Algebra.GroupWithZero.Divisibility
import Mathlib.Data.Nat.Prime.Int
import Mathlib.Data.Rat.Cast.Order
import Mathlib.SetTheory.Cardinal.Finite

/-!
# Primitive vectors in a prime neighbor

This file first proves the algebraic pieces of the double count from actual
submodule inclusions. No representation recurrence, multiplicativity, or
representation formula is assumed. The projective family is supplied by the
concrete construction, and the finite-shell coordinates by the geometric
classification; their integration is separate from the lemmas below.
-/

namespace A354766Neighbors

variable {V : Type*} [AddCommGroup V]

/-- Primitivity in a specified submodule, expressed in the common ambient
group. Membership in the submodule is recorded separately in each shell. -/
def PrimitiveIn (L : Submodule ℤ V) (x : V) : Prop :=
  ∀ q : ℕ, q.Prime → ¬ DivisibleIn L q x

theorem primitiveIn_subtype_iff (L : Submodule ℤ V) (x : L) :
    PrimitiveIn L (x : V) ↔ PrimitiveElement x := by
  constructor
  · intro h q hq
    rintro ⟨y, hy⟩
    exact h q hq ⟨y, y.property, congrArg Subtype.val hy⟩
  · intro h q hq
    rintro ⟨y, hy, hxy⟩
    exact h q hq ⟨⟨y, hy⟩, Subtype.ext hxy⟩

theorem primitiveIn_iff_away_and_at (L : Submodule ℤ V)
    (p : ℕ) (hp : p.Prime) (x : V) :
    PrimitiveIn L x ↔ PrimitiveAway L p x ∧ ¬ DivisibleIn L p x := by
  constructor
  · intro h
    exact ⟨fun q hq _ => h q hq, h p hp⟩
  · rintro ⟨haway, hat⟩ q hq
    by_cases hqp : q = p
    · simpa only [hqp] using hat
    · exact haway q hq hqp

theorem primitiveAway_prime_smul_iff (L : Submodule ℤ V) (p : ℕ)
    (hp : p.Prime) (z : V) (hz : z ∈ L) :
    PrimitiveAway L p ((p : ℤ) • z) ↔ PrimitiveAway L p z := by
  have hcop (q : ℕ) (hq : q.Prime) (hqp : q ≠ p) : p.Coprime q := by
    apply hp.coprime_iff_not_dvd.mpr
    intro hd
    exact hqp ((Nat.prime_dvd_prime_iff_eq hp hq).mp hd).symm
  constructor
  · intro h q hq hqp hd
    exact h q hq hqp ((divisibleIn_smul_iff L z hz p q (hcop q hq hqp)).mpr hd)
  · intro h q hq hqp hd
    exact h q hq hqp ((divisibleIn_smul_iff L z hz p q (hcop q hq hqp)).mp hd)

/-- Multiplication by p carries exterior primitive neighbor vectors exactly
to primitive standard vectors. All hypotheses are actual submodule facts. -/
theorem exterior_primitive_scaled_iff
    (L N M : Submodule ℤ V) (p : ℕ) (hp : p.Prime)
    (hML : M ≤ L) (hMN : M ≤ N)
    (hpL : ∀ z ∈ L, (p : ℤ) • z ∈ M)
    (hpN : ∀ z ∈ N, (p : ℤ) • z ∈ M)
    (hcancel : Function.Injective (fun z : V => (p : ℤ) • z))
    (y : V) (hyN : y ∈ N) (hyL : y ∉ L) :
    PrimitiveIn L ((p : ℤ) • y) ↔ PrimitiveIn N y := by
  have hatL : ¬ DivisibleIn L p ((p : ℤ) • y) := by
    intro hd
    exact hyL ((divisibleIn_smul_iff_mem L p hcancel y).mp hd)
  have hatN : ¬ DivisibleIn N p y :=
    not_divisibleIn_of_outside L N p (fun z hz => hML (hpN z hz)) y hyL
  rw [primitiveIn_iff_away_and_at L p hp,
    primitiveIn_iff_away_and_at N p hp]
  simp only [hatL, hatN, not_false_eq_true, and_true]
  exact primitiveAway_scaled_iff L N M p hp hML hMN hpL hpN y hyN

/-- For an inside vector that is primitive in the standard lattice, the only
possible loss of neighbor primitivity is divisibility by p. -/
theorem inside_primitive_iff_not_divisible
    (L N M : Submodule ℤ V) (p : ℕ) (hp : p.Prime)
    (hML : M ≤ L) (hMN : M ≤ N)
    (hpL : ∀ z ∈ L, (p : ℤ) • z ∈ M)
    (hpN : ∀ z ∈ N, (p : ℤ) • z ∈ M)
    (z : V) (hzM : z ∈ M) (hz : PrimitiveIn L z) :
    PrimitiveIn N z ↔ ¬ DivisibleIn N p z := by
  have hawayL : PrimitiveAway L p z := ((primitiveIn_iff_away_and_at L p hp z).mp hz).1
  have hawayN : PrimitiveAway N p z :=
    (primitiveAway_iff_of_prime_multiple_inclusions
      L N M p hp hML hMN hpL hpN z hzM).mp hawayL
  rw [primitiveIn_iff_away_and_at N p hp]
  simp only [hawayN, true_and]

/-- The exact-content-p case: p*z is primitive in N exactly when the
primitive standard quotient z does not belong to N. -/
theorem inside_one_primitive_iff_not_mem
    (L N M : Submodule ℤ V) (p : ℕ) (hp : p.Prime)
    (hML : M ≤ L) (hMN : M ≤ N)
    (hpL : ∀ z ∈ L, (p : ℤ) • z ∈ M)
    (hpN : ∀ z ∈ N, (p : ℤ) • z ∈ M)
    (hcancel : Function.Injective (fun z : V => (p : ℤ) • z))
    (z : V) (hzL : z ∈ L) (hz : PrimitiveIn L z) :
    PrimitiveIn N ((p : ℤ) • z) ↔ z ∉ N := by
  have hawayLz : PrimitiveAway L p z :=
    ((primitiveIn_iff_away_and_at L p hp z).mp hz).1
  have hawayLpz : PrimitiveAway L p ((p : ℤ) • z) :=
    (primitiveAway_prime_smul_iff L p hp z hzL).mpr hawayLz
  have hawayNpz : PrimitiveAway N p ((p : ℤ) • z) :=
    (primitiveAway_iff_of_prime_multiple_inclusions L N M p hp hML hMN hpL hpN
      ((p : ℤ) • z) (hpL z hzL)).mp hawayLpz
  rw [primitiveIn_iff_away_and_at N p hp]
  simp only [hawayNpz, true_and, divisibleIn_smul_iff_mem N p hcancel z]

/-- Content at least p² always destroys primitivity in a neighbor. -/
theorem inside_two_or_more_not_primitive
    (L N : Submodule ℤ V) (p : ℕ) (hp : p.Prime) (a : ℕ) (ha : 2 ≤ a)
    (hpL : ∀ z ∈ L, (p : ℤ) • z ∈ N) (z : V) (hz : z ∈ L) :
    ¬ PrimitiveIn N (((p : ℤ) ^ a) • z) := by
  intro hprim
  exact hprim p hp (divisibleIn_pow_of_two_le L N p a ha hpL z hz)

section ExteriorShell

variable {R : Type*} [CommRing R] [IsDomain R]

def OutsidePrimitiveShell (L N : Submodule ℤ V) (Q : V → R) (level : R) :=
  {y : V // y ∈ N ∧ Q y = level ∧ PrimitiveIn N y ∧ y ∉ L}

def ScaledPrimitiveShell (L N : Submodule ℤ V) (p : ℕ)
    (Q : V → R) (level : R) :=
  {v : V // v ∈ L ∧ Q v = level ∧ PrimitiveIn L v ∧ DivisibleIn N p v}

def outsideScale
    (L N M : Submodule ℤ V) (p : ℕ) (hp : p.Prime)
    (hML : M ≤ L) (hMN : M ≤ N)
    (hpL : ∀ z ∈ L, (p : ℤ) • z ∈ M)
    (hpN : ∀ z ∈ N, (p : ℤ) • z ∈ M)
    (hcancel : Function.Injective (fun z : V => (p : ℤ) • z))
    (Q : V → R) (scale level : R) (hQ : ∀ y, Q ((p : ℤ) • y) = scale * Q y) :
    OutsidePrimitiveShell L N Q level → ScaledPrimitiveShell L N p Q (scale * level) :=
  fun y => ⟨(p : ℤ) • y.val, hML (hpN y.val y.property.1), by
    rw [hQ, y.property.2.1],
    (exterior_primitive_scaled_iff L N M p hp hML hMN hpL hpN hcancel
      y.val y.property.1 y.property.2.2.2).mpr y.property.2.2.1,
    y.val, y.property.1, rfl⟩

theorem outsideScale_bijective
    (L N M : Submodule ℤ V) (p : ℕ) (hp : p.Prime)
    (hML : M ≤ L) (hMN : M ≤ N)
    (hpL : ∀ z ∈ L, (p : ℤ) • z ∈ M)
    (hpN : ∀ z ∈ N, (p : ℤ) • z ∈ M)
    (hcancel : Function.Injective (fun z : V => (p : ℤ) • z))
    (Q : V → R) (scale level : R) (hscale : scale ≠ 0)
    (hQ : ∀ y, Q ((p : ℤ) • y) = scale * Q y) :
    Function.Bijective (outsideScale L N M p hp hML hMN hpL hpN hcancel Q scale level hQ) := by
  constructor
  · intro x y h
    exact Subtype.ext (hcancel (congrArg Subtype.val h))
  · rintro ⟨v, hvL, hvQ, hvprim, y, hyN, hpy⟩
    have hyL : y ∉ L := by
      intro h
      exact hvprim p hp ⟨y, h, hpy⟩
    have hyQ : Q y = level := by
      apply mul_left_cancel₀ hscale
      rw [← hQ, hpy]
      exact hvQ
    have hyprim : PrimitiveIn N y := by
      apply (exterior_primitive_scaled_iff
        L N M p hp hML hMN hpL hpN hcancel y hyN hyL).mp
      simpa only [hpy] using hvprim
    refine ⟨⟨y, hyN, hyQ, hyprim, hyL⟩, ?_⟩
    exact Subtype.ext hpy

/-- A proved bijection for the exterior part at one actual neighbor. The
remaining projective membership step identifies which neighbor occurs. -/
noncomputable def outsidePrimitiveShellEquiv
    (L N M : Submodule ℤ V) (p : ℕ) (hp : p.Prime)
    (hML : M ≤ L) (hMN : M ≤ N)
    (hpL : ∀ z ∈ L, (p : ℤ) • z ∈ M)
    (hpN : ∀ z ∈ N, (p : ℤ) • z ∈ M)
    (hcancel : Function.Injective (fun z : V => (p : ℤ) • z))
    (Q : V → R) (scale level : R) (hscale : scale ≠ 0)
    (hQ : ∀ y, Q ((p : ℤ) • y) = scale * Q y) :
    OutsidePrimitiveShell L N Q level ≃ ScaledPrimitiveShell L N p Q (scale * level) :=
  Equiv.ofBijective (outsideScale L N M p hp hML hMN hpL hpN hcancel Q scale level hQ)
    (outsideScale_bijective L N M p hp hML hMN hpL hpN hcancel Q scale level hscale hQ)

end ExteriorShell

/-- This exact divisibility test includes the ramified prime three: a square
prime divisor of `3*m²` already divides `m`. -/
theorem prime_sq_dvd_three_mul_sq_iff (p m : ℕ) (hp : p.Prime) :
    p ^ 2 ∣ 3 * m ^ 2 ↔ p ∣ m := by
  constructor
  · intro hd
    by_contra hpm
    have hpm2 : ¬ p ∣ m ^ 2 := fun h => hpm (hp.dvd_of_dvd_pow h)
    have hp3 : p ∣ 3 :=
      (hp.dvd_or_dvd ((dvd_pow_self p (by decide : (2 : ℕ) ≠ 0)).trans hd)).resolve_right hpm2
    have hep : p = 3 := (Nat.prime_dvd_prime_iff_eq hp Nat.prime_three).mp hp3
    subst p
    have hm2 : 3 ∣ m ^ 2 :=
      (mul_dvd_mul_iff_left (by decide : (3 : ℕ) ≠ 0)).mp (by simpa only [pow_two] using hd)
    exact hpm (Nat.prime_three.dvd_of_dvd_pow hm2)
  · rintro ⟨k, rfl⟩
    refine ⟨3 * k ^ 2, ?_⟩
    ring

/-- Integral neighbor norms rule out p-division at level `3*m²` when p does
not divide m. This proof remains valid at p=3, where reduction of the norm
itself is zero and a nonzero-residue-norm argument would be incorrect. -/
theorem not_divisibleIn_of_norm_three_mul_sq
    (N : Submodule ℤ V) (p m : ℕ) (hp : p.Prime) (hpm : ¬ p ∣ m)
    (Q : V → ℚ) (hQ : ∀ y, Q ((p : ℤ) • y) = (p : ℚ) ^ 2 * Q y)
    (hintegral : ∀ y ∈ N, ∃ k : ℤ, Q y = (k : ℚ))
    (x : V) (hx : Q x = ((3 * m ^ 2 : ℕ) : ℚ)) :
    ¬ DivisibleIn N p x := by
  rintro ⟨y, hy, hpy⟩
  obtain ⟨k, hk⟩ := hintegral y hy
  have heqQ : ((3 * m ^ 2 : ℕ) : ℚ) = (p : ℚ) ^ 2 * (k : ℚ) := by
    calc
      ((3 * m ^ 2 : ℕ) : ℚ) = Q x := hx.symm
      _ = Q ((p : ℤ) • y) := congrArg Q hpy.symm
      _ = (p : ℚ) ^ 2 * (k : ℚ) := by rw [hQ, hk]
  have heqZ : ((3 * m ^ 2 : ℕ) : ℤ) = (p : ℤ) ^ 2 * k := by
    exact_mod_cast heqQ
  have hdZ : ((p ^ 2 : ℕ) : ℤ) ∣ ((3 * m ^ 2 : ℕ) : ℤ) :=
    ⟨k, by simpa only [Nat.cast_pow] using heqZ⟩
  have hdN : p ^ 2 ∣ 3 * m ^ 2 := Int.natCast_dvd_natCast.mp hdZ
  exact hpm ((prime_sq_dvd_three_mul_sq_iff p m hp).mp hdN)

section InsideFibers

variable {I : Type*}

/-- In exact content p, the admissible neighbors are exactly the complement
of the neighbors containing the primitive quotient. -/
noncomputable def insideOneFiberEquiv
    (L : Submodule ℤ V) (N M : I → Submodule ℤ V) (p : ℕ) (hp : p.Prime)
    (hML : ∀ i, M i ≤ L) (hMN : ∀ i, M i ≤ N i)
    (hpL : ∀ i z, z ∈ L → (p : ℤ) • z ∈ M i)
    (hpN : ∀ i z, z ∈ N i → (p : ℤ) • z ∈ M i)
    (hcancel : Function.Injective (fun z : V => (p : ℤ) • z))
    (z : V) (hzL : z ∈ L) (hz : PrimitiveIn L z) :
    {i : I // (p : ℤ) • z ∈ N i ∧ PrimitiveIn (N i) ((p : ℤ) • z)} ≃
      {i : I // z ∉ N i} :=
  Equiv.subtypeEquivRight (fun i => by
    have hm : (p : ℤ) • z ∈ N i := hMN i (hpL i z hzL)
    simp only [hm, true_and]
    exact inside_one_primitive_iff_not_mem
      L (N i) (M i) p hp (hML i) (hMN i) (hpL i) (hpN i) hcancel z hzL hz)

theorem card_inside_one_fiber [Finite I]
    (L : Submodule ℤ V) (N M : I → Submodule ℤ V) (p : ℕ) (hp : p.Prime)
    (hML : ∀ i, M i ≤ L) (hMN : ∀ i, M i ≤ N i)
    (hpL : ∀ i z, z ∈ L → (p : ℤ) • z ∈ M i)
    (hpN : ∀ i z, z ∈ N i → (p : ℤ) • z ∈ M i)
    (hcancel : Function.Injective (fun z : V => (p : ℤ) • z))
    (z : V) (hzL : z ∈ L) (hz : PrimitiveIn L z) :
    Nat.card {i : I // (p : ℤ) • z ∈ N i ∧ PrimitiveIn (N i) ((p : ℤ) • z)} =
      Nat.card I - Nat.card {i : I // z ∈ N i} := by
  classical
  letI : Fintype I := Fintype.ofFinite I
  rw [Nat.card_congr (insideOneFiberEquiv L N M p hp hML hMN hpL hpN hcancel z hzL hz)]
  simp only [Nat.card_eq_fintype_card, Fintype.card_subtype_compl]

/-- At exact content one and p∤m, every neighbor containing the standard
vector keeps it primitive. The integrality argument includes p=3. -/
noncomputable def insideZeroNondivFiberEquiv
    (L : Submodule ℤ V) (N M : I → Submodule ℤ V) (p m : ℕ) (hp : p.Prime)
    (hpm : ¬ p ∣ m)
    (hML : ∀ i, M i ≤ L) (hMN : ∀ i, M i ≤ N i)
    (hcommon : ∀ i, L ⊓ N i ≤ M i)
    (hpL : ∀ i z, z ∈ L → (p : ℤ) • z ∈ M i)
    (hpN : ∀ i z, z ∈ N i → (p : ℤ) • z ∈ M i)
    (Q : V → ℚ) (hQ : ∀ y, Q ((p : ℤ) • y) = (p : ℚ) ^ 2 * Q y)
    (hintegral : ∀ i y, y ∈ N i → ∃ k : ℤ, Q y = (k : ℚ))
    (z : V) (hzL : z ∈ L) (hz : PrimitiveIn L z)
    (hzQ : Q z = ((3 * m ^ 2 : ℕ) : ℚ)) :
    {i : I // z ∈ N i ∧ PrimitiveIn (N i) z} ≃ {i : I // z ∈ N i} :=
  Equiv.subtypeEquivRight (fun i => by
    constructor
    · exact And.left
    · intro hzi
      refine ⟨hzi, ?_⟩
      apply (inside_primitive_iff_not_divisible L (N i) (M i) p hp
        (hML i) (hMN i) (hpL i) (hpN i) z (hcommon i ⟨hzL, hzi⟩) hz).mpr
      exact not_divisibleIn_of_norm_three_mul_sq (N i) p m hp hpm Q hQ
        (hintegral i) z hzQ)

theorem card_inside_two_or_more_fiber_zero
    (L : Submodule ℤ V) (N : I → Submodule ℤ V)
    (p : ℕ) (hp : p.Prime) (a : ℕ) (ha : 2 ≤ a)
    (hpL : ∀ i z, z ∈ L → (p : ℤ) • z ∈ N i)
    (z : V) (hzL : z ∈ L) :
    Nat.card {i : I // ((p : ℤ) ^ a) • z ∈ N i ∧
      PrimitiveIn (N i) (((p : ℤ) ^ a) • z)} = 0 := by
  letI : IsEmpty {i : I // ((p : ℤ) ^ a) • z ∈ N i ∧
      PrimitiveIn (N i) (((p : ℤ) ^ a) • z)} :=
    ⟨fun i => inside_two_or_more_not_primitive
      L (N i.val) p hp a ha (hpL i.val) z hzL i.property.2⟩
  exact Nat.card_of_isEmpty

end InsideFibers

end A354766Neighbors

#print axioms A354766Neighbors.exterior_primitive_scaled_iff
#print axioms A354766Neighbors.inside_one_primitive_iff_not_mem
#print axioms A354766Neighbors.inside_two_or_more_not_primitive
#print axioms A354766Neighbors.outsidePrimitiveShellEquiv
#print axioms A354766Neighbors.not_divisibleIn_of_norm_three_mul_sq
#print axioms A354766Neighbors.card_inside_one_fiber
#print axioms A354766Neighbors.insideZeroNondivFiberEquiv
#print axioms A354766Neighbors.card_inside_two_or_more_fiber_zero
