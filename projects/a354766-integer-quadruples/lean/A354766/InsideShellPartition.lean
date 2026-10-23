import A354766.InsideContentClassification
import Mathlib.Algebra.GroupWithZero.Basic

namespace A354766Neighbors

variable {V R : Type*} [AddCommGroup V] [CommRing R] [IsDomain R]

def InsidePrimitiveShell (L N : Submodule ℤ V) (Q : V → R) (level : R) :=
  {x : V // x ∈ L ∧ x ∈ N ∧ Q x = level ∧ PrimitiveIn N x}

def InsidePrimitiveZeroShell (L N : Submodule ℤ V) (p : ℕ)
    (Q : V → R) (level : R) :=
  {x : V // x ∈ L ∧ x ∈ N ∧ Q x = level ∧
    PrimitiveIn L x ∧ ¬ DivisibleIn N p x}

def insidePartsMap
    (L N M : Submodule ℤ V) (p : ℕ) (hp : p.Prime)
    (hML : M ≤ L) (hMN : M ≤ N) (hcommon : L ⊓ N ≤ M)
    (hpL : ∀ z ∈ L, (p : ℤ) • z ∈ M)
    (hpN : ∀ z ∈ N, (p : ℤ) • z ∈ M)
    (hcancel : Function.Injective (fun z : V => (p : ℤ) • z))
    (Q : V → R) (scale level : R)
    (hQ : ∀ z, Q ((p : ℤ) • z) = scale * Q z) :
    (InsidePrimitiveZeroShell L N p Q (scale * level) ⊕
      OutsidePrimitiveShell N L Q level) →
      InsidePrimitiveShell L N Q (scale * level)
  | Sum.inl x => ⟨x.val, x.property.1, x.property.2.1,
      x.property.2.2.1,
      (inside_primitive_iff_not_divisible L N M p hp hML hMN hpL hpN
        x.val (hcommon ⟨x.property.1, x.property.2.1⟩)
        x.property.2.2.2.1).mpr x.property.2.2.2.2⟩
  | Sum.inr z => ⟨(p : ℤ) • z.val, hML (hpL z.val z.property.1),
      hMN (hpL z.val z.property.1), by rw [hQ, z.property.2.1],
      (inside_one_primitive_iff_not_mem L N M p hp hML hMN hpL hpN
        hcancel z.val z.property.1 z.property.2.2.1).mpr z.property.2.2.2⟩

theorem insidePartsMap_bijective
    (L N M : Submodule ℤ V) (p : ℕ) (hp : p.Prime)
    (hML : M ≤ L) (hMN : M ≤ N) (hcommon : L ⊓ N ≤ M)
    (hpL : ∀ z ∈ L, (p : ℤ) • z ∈ M)
    (hpN : ∀ z ∈ N, (p : ℤ) • z ∈ M)
    (hcancel : Function.Injective (fun z : V => (p : ℤ) • z))
    (Q : V → R) (scale level : R) (hscale : scale ≠ 0)
    (hQ : ∀ z, Q ((p : ℤ) • z) = scale * Q z) :
    Function.Bijective (insidePartsMap
      L N M p hp hML hMN hcommon hpL hpN hcancel Q scale level hQ) := by
  constructor
  · intro x y h
    have hval := congrArg Subtype.val h
    cases x with
    | inl x =>
      cases y with
      | inl y => exact congrArg Sum.inl (Subtype.ext hval)
      | inr z =>
        have hdiv : DivisibleIn L p x.val := ⟨z.val, z.property.1, hval.symm⟩
        exact False.elim (x.property.2.2.2.1 p hp hdiv)
    | inr z =>
      cases y with
      | inl y =>
        have hdiv : DivisibleIn L p y.val := ⟨z.val, z.property.1, hval⟩
        exact False.elim (y.property.2.2.2.1 p hp hdiv)
      | inr w => exact congrArg Sum.inr (Subtype.ext (hcancel hval))
  · intro x
    rcases inside_primitive_cases L N M p hp hML hMN hcommon hpL hpN
      x.val x.property.1 x.property.2.1 x.property.2.2.2 with hx | hz
    · refine ⟨Sum.inl ⟨x.val, x.property.1, x.property.2.1,
        x.property.2.2.1, hx, x.property.2.2.2 p hp⟩, ?_⟩
      rfl
    · obtain ⟨z, hzL, hzprim, hxz, hzN⟩ := hz
      have hzQ : Q z = level := by
        apply mul_left_cancel₀ hscale
        rw [← hQ, ← hxz]
        exact x.property.2.2.1
      refine ⟨Sum.inr ⟨z, hzL, hzQ, hzprim, hzN⟩, ?_⟩
      exact Subtype.ext hxz.symm

/-- The actual content-zero/content-one partition of an inside primitive
shell. The second part consists of primitive standard vectors outside N,
at the unscaled norm. -/
noncomputable def insidePrimitiveShellEquiv
    (L N M : Submodule ℤ V) (p : ℕ) (hp : p.Prime)
    (hML : M ≤ L) (hMN : M ≤ N) (hcommon : L ⊓ N ≤ M)
    (hpL : ∀ z ∈ L, (p : ℤ) • z ∈ M)
    (hpN : ∀ z ∈ N, (p : ℤ) • z ∈ M)
    (hcancel : Function.Injective (fun z : V => (p : ℤ) • z))
    (Q : V → R) (scale level : R) (hscale : scale ≠ 0)
    (hQ : ∀ z, Q ((p : ℤ) • z) = scale * Q z) :
    (InsidePrimitiveZeroShell L N p Q (scale * level) ⊕
      OutsidePrimitiveShell N L Q level) ≃
      InsidePrimitiveShell L N Q (scale * level) :=
  Equiv.ofBijective
    (insidePartsMap L N M p hp hML hMN hcommon hpL hpN hcancel Q scale level hQ)
    (insidePartsMap_bijective
      L N M p hp hML hMN hcommon hpL hpN hcancel Q scale level hscale hQ)

end A354766Neighbors

#print axioms A354766Neighbors.insidePrimitiveShellEquiv
