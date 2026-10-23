import Mathlib.NumberTheory.LegendreSymbol.QuadraticReciprocity
import Mathlib.Tactic.NormNum.LegendreSymbol

/-!
Local arithmetic supporting the Cooper--Hirschhorn specialization.
This file does not assert the missing all-m representation-count theorem.
-/

namespace A354766Research

def residueCharacter (p : ℕ) : ℤ :=
  if p % 6 = 1 then 1 else if p % 6 = 5 then -1 else 0

theorem legendre_neg_three_eq_at_three (p : ℕ) [Fact p.Prime] (hp2 : p ≠ 2) :
    legendreSym p (-3) = legendreSym 3 (p : ℤ) := by
  haveI : Fact (Nat.Prime 3) := ⟨by decide⟩
  have hodd : p % 2 = 1 :=
    (Nat.Prime.mod_two_eq_one_iff_ne_two Fact.out).mpr hp2
  have hqr : legendreSym p (3 : ℤ) =
      (-1 : ℤ) ^ (p / 2) * legendreSym 3 (p : ℤ) := by
    simpa using
      (legendreSym.quadratic_reciprocity' (p := 3) (q := p) (by decide) hp2)
  calc
    legendreSym p (-3) = legendreSym p (-1) * legendreSym p 3 := by
      rw [← legendreSym.mul]
      norm_num
    _ = (-1 : ℤ) ^ (p / 2) *
        ((-1 : ℤ) ^ (p / 2) * legendreSym 3 (p : ℤ)) := by
      rw [legendreSym.at_neg_one hp2, ZMod.χ₄_eq_neg_one_pow hodd, hqr]
    _ = legendreSym 3 (p : ℤ) := by
      rcases neg_one_pow_eq_or ℤ (p / 2) with h | h <;> simp [h]

theorem legendre_neg_three_eq_residueCharacter (p : ℕ) [Fact p.Prime]
    (hp2 : p ≠ 2) :
    legendreSym p (-3) = residueCharacter p := by
  haveI : Fact (Nat.Prime 3) := ⟨by decide⟩
  rw [legendre_neg_three_eq_at_three p hp2, legendreSym.mod 3 (p : ℤ),
    ← Int.natCast_mod]
  have hodd : p % 2 = 1 :=
    (Nat.Prime.mod_two_eq_one_iff_ne_two Fact.out).mpr hp2
  have h6 : p % 6 = 1 ∨ p % 6 = 3 ∨ p % 6 = 5 := by omega
  rcases h6 with h | h | h
  · have h3 : p % 3 = 1 := by omega
    norm_num [h3, residueCharacter, h]
  · have h3 : p % 3 = 0 := by omega
    norm_num [h3, residueCharacter, h]
  · have h3 : p % 3 = 2 := by omega
    norm_num [h3, residueCharacter, h]

end A354766Research

#print axioms A354766Research.legendre_neg_three_eq_at_three
#print axioms A354766Research.legendre_neg_three_eq_residueCharacter
