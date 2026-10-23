import A354766.MinusThreeCharacter

/-! Character coefficients for the primitive neighbor recurrence. -/

namespace A354766Research

theorem legendre_neg_three_mul_square (p : ℕ) [Fact p.Prime] (hp2 : p ≠ 2) (k : ℕ) :
    legendreSym p (-3 * (k : ℤ) ^ 2) = if p ∣ k then 0 else residueCharacter p := by
  by_cases hk : p ∣ k
  · rw [if_pos hk]
    apply (legendreSym.eq_zero_iff p (-3 * (k : ℤ) ^ 2)).mpr
    have hk0 : ((k : ℤ) : ZMod p) = 0 :=
      (ZMod.intCast_zmod_eq_zero_iff_dvd (k : ℤ) p).mpr
        (Int.natCast_dvd_natCast.mpr hk)
    have hk0' : (k : ZMod p) = 0 := by simpa only [Int.cast_natCast] using hk0
    simp [hk0']
  · rw [if_neg hk]
    have hk0 : ((k : ℤ) : ZMod p) ≠ 0 := by
      intro h
      exact hk (Int.natCast_dvd_natCast.mp
        ((ZMod.intCast_zmod_eq_zero_iff_dvd (k : ℤ) p).mp h))
    rw [legendreSym.mul, legendreSym.sq_one' p hk0, mul_one,
      legendre_neg_three_eq_residueCharacter p hp2]

theorem residueCharacter_range (p : ℕ) :
    residueCharacter p = 0 ∨ residueCharacter p = 1 ∨ residueCharacter p = -1 := by
  by_cases h1 : p % 6 = 1
  · simp [residueCharacter, h1]
  · by_cases h5 : p % 6 = 5 <;> simp [residueCharacter, h1, h5]

@[simp] theorem residueCharacter_three : residueCharacter 3 = 0 := by
  norm_num [residueCharacter]

theorem legendre_neg_three_mul_square_at_three (k : ℕ) :
    legendreSym 3 (-3 * (k : ℤ) ^ 2) = 0 := by
  haveI : Fact (Nat.Prime 3) := ⟨by decide⟩
  rw [legendre_neg_three_mul_square 3 (by decide)]
  split <;> simp

end A354766Research

#print axioms A354766Research.legendre_neg_three_mul_square
#print axioms A354766Research.residueCharacter_range
#print axioms A354766Research.legendre_neg_three_mul_square_at_three
