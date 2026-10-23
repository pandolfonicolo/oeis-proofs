import Mathlib.LinearAlgebra.Span.Basic
import Mathlib.Data.Nat.Prime.Defs
import Mathlib.SetTheory.Cardinal.Finite

/-!
Integral linear equivalences preserve primitivity and give genuine
equivalences of primitive shells whenever they preserve the indicated norm.
-/

namespace A354766Neighbors

variable {U W : Type*} [AddCommGroup U] [AddCommGroup W]

def PrimitiveElement (x : U) : Prop :=
  ∀ p : ℕ, p.Prime → ¬ ∃ y : U, (p : ℤ) • y = x

theorem linearEquiv_scalar_divisibility (e : U ≃ₗ[ℤ] W) (p : ℕ) (x : U) :
    (∃ y : U, (p : ℤ) • y = x) ↔ ∃ y : W, (p : ℤ) • y = e x := by
  constructor
  · rintro ⟨y, hy⟩
    refine ⟨e y, ?_⟩
    rw [← e.map_smul, hy]
  · rintro ⟨y, hy⟩
    refine ⟨e.symm y, ?_⟩
    apply e.injective
    rw [e.map_smul, e.apply_symm_apply, hy]

theorem linearEquiv_primitive (e : U ≃ₗ[ℤ] W) (x : U) :
    PrimitiveElement x ↔ PrimitiveElement (e x) := by
  constructor
  · intro h p hp hd
    exact h p hp ((linearEquiv_scalar_divisibility e p x).mpr hd)
  · intro h p hp hd
    exact h p hp ((linearEquiv_scalar_divisibility e p x).mp hd)

def primitiveShellEquiv {A : Type*} (e : U ≃ₗ[ℤ] W)
    (Q : U → A) (R : W → A) (hQ : ∀ x, R (e x) = Q x) (level : A) :
    {x : U // Q x = level ∧ PrimitiveElement x} ≃
      {y : W // R y = level ∧ PrimitiveElement y} where
  toFun x := ⟨e x.1, by
    rw [hQ]
    exact ⟨x.property.1, (linearEquiv_primitive e x.1).mp x.property.2⟩⟩
  invFun y := ⟨e.symm y.1, by
    refine ⟨?_, (linearEquiv_primitive e (e.symm y.1)).mpr ?_⟩
    · rw [← hQ, e.apply_symm_apply]
      exact y.property.1
    · simpa only [e.apply_symm_apply] using y.property.2⟩
  left_inv x := by
    apply Subtype.ext
    exact e.symm_apply_apply x.1
  right_inv y := by
    apply Subtype.ext
    exact e.apply_symm_apply y.1

theorem primitiveShell_card_eq {A : Type*} (e : U ≃ₗ[ℤ] W)
    (Q : U → A) (R : W → A) (hQ : ∀ x, R (e x) = Q x) (level : A) :
    Nat.card {x : U // Q x = level ∧ PrimitiveElement x} =
      Nat.card {y : W // R y = level ∧ PrimitiveElement y} :=
  Nat.card_congr (primitiveShellEquiv e Q R hQ level)

end A354766Neighbors

#print axioms A354766Neighbors.linearEquiv_primitive
#print axioms A354766Neighbors.primitiveShell_card_eq
