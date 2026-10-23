import A354766.FiniteCounts
import Mathlib.Data.Fin.VecNotation
import Mathlib.Tactic.FinCases

/-!
The exact connection between primitive three-square counts in the recovered
integer-triple model and the coordinate-vector model used for neighbors.
-/

namespace A354766Neighbors

abbrev IntegerVector := Fin 3 → ℤ

def vectorContent (v : IntegerVector) : ℕ :=
  Nat.gcd (v 0).natAbs (Nat.gcd (v 1).natAbs (v 2).natAbs)

def vectorNorm (v : IntegerVector) : ℤ := (v 0) ^ 2 + (v 1) ^ 2 + (v 2) ^ 2

def tripleVectorEquiv : A354766.Triple ≃ IntegerVector where
  toFun u := ![u.1, u.2.1, u.2.2]
  invFun v := (v 0, v 1, v 2)
  left_inv := by rintro ⟨a, b, c⟩; rfl
  right_inv := by
    intro v
    funext i
    fin_cases i <;> rfl

theorem vectorContent_eq_one_iff (v : IntegerVector) :
    vectorContent v = 1 ↔
      ∀ p : ℕ, p.Prime → ¬ ((p : ℤ) ∣ v 0 ∧ (p : ℤ) ∣ v 1 ∧ (p : ℤ) ∣ v 2) := by
  rw [Nat.eq_one_iff_not_exists_prime_dvd]
  simp only [vectorContent, Nat.dvd_gcd_iff, Int.natCast_dvd]

theorem scalar_divisibility_iff_coordinates (p : ℕ) (v : IntegerVector) :
    (∃ w : IntegerVector, (p : ℤ) • w = v) ↔
      (p : ℤ) ∣ v 0 ∧ (p : ℤ) ∣ v 1 ∧ (p : ℤ) ∣ v 2 := by
  constructor
  · rintro ⟨w, hw⟩
    refine ⟨⟨w 0, ?_⟩, ⟨w 1, ?_⟩, ⟨w 2, ?_⟩⟩
    · simpa only [Pi.smul_apply, smul_eq_mul] using (congrFun hw 0).symm
    · simpa only [Pi.smul_apply, smul_eq_mul] using (congrFun hw 1).symm
    · simpa only [Pi.smul_apply, smul_eq_mul] using (congrFun hw 2).symm
  · rintro ⟨⟨a, ha⟩, ⟨b, hb⟩, ⟨c, hc⟩⟩
    refine ⟨![a, b, c], ?_⟩
    funext i
    fin_cases i <;> simp [Pi.smul_apply, smul_eq_mul, ha, hb, hc]

theorem vectorContent_eq_one_iff_primitive (v : IntegerVector) :
    vectorContent v = 1 ↔
      ∀ p : ℕ, p.Prime → ¬ ∃ w : IntegerVector, (p : ℤ) • w = v := by
  rw [vectorContent_eq_one_iff]
  simp only [scalar_divisibility_iff_coordinates]

def PrimitiveVectorShell (N : ℕ) :=
  {v : IntegerVector // vectorNorm v = (N : ℤ) ∧ vectorContent v = 1}

def primitiveVectorShellEquiv (N : ℕ) :
    PrimitiveVectorShell N ≃ {u : A354766.Triple // u ∈ A354766.primitiveThreeSquareFinset N} where
  toFun v := ⟨tripleVectorEquiv.symm v.1, by
    apply A354766.mem_primitiveThreeSquareFinset.mpr
    exact v.property⟩
  invFun u := ⟨tripleVectorEquiv u.1, by
    have h := A354766.mem_primitiveThreeSquareFinset.mp u.property
    exact h⟩
  left_inv := by
    intro v
    apply Subtype.ext
    exact tripleVectorEquiv.apply_symm_apply v.1
  right_inv := by
    intro u
    apply Subtype.ext
    exact tripleVectorEquiv.symm_apply_apply u.1

instance (N : ℕ) : Finite (PrimitiveVectorShell N) :=
  Finite.of_equiv {u : A354766.Triple // u ∈ A354766.primitiveThreeSquareFinset N}
    (primitiveVectorShellEquiv N).symm

theorem primitiveVectorShell_card (N : ℕ) :
    Nat.card (PrimitiveVectorShell N) = A354766.r3PrimitiveFinite N := by
  rw [Nat.card_congr (primitiveVectorShellEquiv N)]
  simp only [Nat.card_eq_fintype_card, Fintype.card_coe, A354766.r3PrimitiveFinite]

end A354766Neighbors

#print axioms A354766Neighbors.vectorContent_eq_one_iff_primitive
#print axioms A354766Neighbors.primitiveVectorShell_card
