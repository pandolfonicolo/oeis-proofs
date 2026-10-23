import Mathlib.Data.Nat.Prime.Int
import Mathlib.RingTheory.Coprime.Lemmas
import Mathlib.Tactic.Ring

/-!
# Lifting a nonzero isotropic integer triple modulo an odd prime

This is an elementary prerequisite for the integral p-neighbor construction.
It proves the lift itself, rather than assuming any neighbor-counting theorem
or recurrence for representation numbers.
-/

namespace A354766Research

/-- The standard positive ternary quadratic form on integer triples. -/
def tripleNormSq (u : ℤ × ℤ × ℤ) : ℤ :=
  u.1 ^ 2 + u.2.1 ^ 2 + u.2.2 ^ 2

/-- Coordinatewise congruence, stated with integer divisibility. -/
def tripleCongruent (p : ℕ) (u v : ℤ × ℤ × ℤ) : Prop :=
  (p : ℤ) ∣ u.1 - v.1 ∧
    (p : ℤ) ∣ u.2.1 - v.2.1 ∧ (p : ℤ) ∣ u.2.2 - v.2.2

/-- A triple remains nonzero after reduction modulo p. -/
def tripleNonzeroMod (p : ℕ) (u : ℤ × ℤ × ℤ) : Prop :=
  ¬((p : ℤ) ∣ u.1 ∧ (p : ℤ) ∣ u.2.1 ∧ (p : ℤ) ∣ u.2.2)

private theorem not_dvd_coordinate_shift (p : ℕ) (a t : ℤ)
    (ha : ¬(p : ℤ) ∣ a) : ¬(p : ℤ) ∣ a + (p : ℤ) * t := by
  intro h
  apply ha
  simpa using dvd_sub h (dvd_mul_right (p : ℤ) t)

/-- Adjusting a coordinate that is nonzero modulo p lifts isotropy from p to p². -/
theorem exists_isotropic_coordinate_shift (p : ℕ) (hp : p.Prime) (hp2 : p ≠ 2)
    (a b c : ℤ) (ha : ¬(p : ℤ) ∣ a)
    (hQ : (p : ℤ) ∣ a ^ 2 + b ^ 2 + c ^ 2) :
    ∃ t : ℤ, (p : ℤ) ^ 2 ∣ (a + (p : ℤ) * t) ^ 2 + b ^ 2 + c ^ 2 := by
  have hprime : Prime (p : ℤ) := Nat.prime_iff_prime_int.mp hp
  have hcoef : ¬(p : ℤ) ∣ 2 * a := by
    intro h
    rcases hprime.dvd_or_dvd h with htwo | ha'
    · have htwo' : p ∣ 2 := Int.natCast_dvd_natCast.mp htwo
      exact hp2 (Nat.le_antisymm (Nat.le_of_dvd (by decide) htwo') hp.two_le)
    · exact ha ha'
  have hcopNat : Nat.Coprime p (2 * a).natAbs :=
    hp.coprime_iff_not_dvd.mpr (by
      intro h
      exact hcoef (Int.natCast_dvd.mpr h))
  have hcop : IsCoprime (p : ℤ) (2 * a) :=
    Int.isCoprime_iff_gcd_eq_one.mpr (by
      simpa only [Int.gcd_def, Int.natAbs_natCast] using hcopNat)
  rcases hcop with ⟨s, t, hbez⟩
  rcases hQ with ⟨k, hk⟩
  refine ⟨-k * t, k * s + (-k * t) ^ 2, ?_⟩
  calc
    (a + (p : ℤ) * (-k * t)) ^ 2 + b ^ 2 + c ^ 2 =
        (a ^ 2 + b ^ 2 + c ^ 2) +
          (p : ℤ) * (-2 * a * k * t) + (p : ℤ) ^ 2 * (-k * t) ^ 2 := by ring
    _ = (p : ℤ) * k * (1 - t * (2 * a)) +
          (p : ℤ) ^ 2 * (-k * t) ^ 2 := by rw [hk]; ring
    _ = (p : ℤ) ^ 2 * (k * s + (-k * t) ^ 2) := by
      rw [← eq_sub_of_add_eq hbez]
      ring

/-- A nonzero isotropic class modulo an odd prime has an integer lift whose norm
is divisible by p². The lift stays in the original residue class and remains
nonzero modulo p. The proof changes just one coordinate. -/
theorem exists_normalized_isotropic_lift (p : ℕ) (hp : p.Prime) (hp2 : p ≠ 2)
    (u : ℤ × ℤ × ℤ) (hu : tripleNonzeroMod p u)
    (hQ : (p : ℤ) ∣ tripleNormSq u) :
    ∃ v : ℤ × ℤ × ℤ, tripleCongruent p v u ∧
      (p : ℤ) ^ 2 ∣ tripleNormSq v ∧ tripleNonzeroMod p v := by
  rcases u with ⟨a, b, c⟩
  change ¬((p : ℤ) ∣ a ∧ (p : ℤ) ∣ b ∧ (p : ℤ) ∣ c) at hu
  change (p : ℤ) ∣ a ^ 2 + b ^ 2 + c ^ 2 at hQ
  by_cases ha : (p : ℤ) ∣ a
  · by_cases hb : (p : ℤ) ∣ b
    · have hc : ¬(p : ℤ) ∣ c := fun hc => hu ⟨ha, hb, hc⟩
      have hQ' : (p : ℤ) ∣ c ^ 2 + a ^ 2 + b ^ 2 := by
        rw [show c ^ 2 + a ^ 2 + b ^ 2 = a ^ 2 + b ^ 2 + c ^ 2 by ring]
        exact hQ
      obtain ⟨t, ht⟩ := exists_isotropic_coordinate_shift p hp hp2 c a b hc hQ'
      refine ⟨(a, b, c + (p : ℤ) * t), ?_, ?_, ?_⟩
      · change (p : ℤ) ∣ a - a ∧ (p : ℤ) ∣ b - b ∧
          (p : ℤ) ∣ (c + (p : ℤ) * t) - c
        refine ⟨by simp, by simp, t, ?_⟩
        ring
      · change (p : ℤ) ^ 2 ∣ a ^ 2 + b ^ 2 + (c + (p : ℤ) * t) ^ 2
        rw [show a ^ 2 + b ^ 2 + (c + (p : ℤ) * t) ^ 2 =
          (c + (p : ℤ) * t) ^ 2 + a ^ 2 + b ^ 2 by ring]
        exact ht
      · intro h
        exact not_dvd_coordinate_shift p c t hc h.2.2
    · obtain ⟨t, ht⟩ := exists_isotropic_coordinate_shift p hp hp2 b a c hb (by
        rw [add_comm (b ^ 2) (a ^ 2)]
        exact hQ)
      refine ⟨(a, b + (p : ℤ) * t, c), ?_, ?_, ?_⟩
      · change (p : ℤ) ∣ a - a ∧ (p : ℤ) ∣ (b + (p : ℤ) * t) - b ∧
          (p : ℤ) ∣ c - c
        refine ⟨by simp, ⟨t, ?_⟩, by simp⟩
        ring
      · change (p : ℤ) ^ 2 ∣ a ^ 2 + (b + (p : ℤ) * t) ^ 2 + c ^ 2
        rw [add_comm (a ^ 2) ((b + (p : ℤ) * t) ^ 2)]
        exact ht
      · intro h
        exact not_dvd_coordinate_shift p b t hb h.2.1
  · obtain ⟨t, ht⟩ := exists_isotropic_coordinate_shift p hp hp2 a b c ha hQ
    refine ⟨(a + (p : ℤ) * t, b, c), ?_, ht, ?_⟩
    · change (p : ℤ) ∣ (a + (p : ℤ) * t) - a ∧ (p : ℤ) ∣ b - b ∧
        (p : ℤ) ∣ c - c
      refine ⟨⟨t, ?_⟩, by simp, by simp⟩
      ring
    · intro h
      exact not_dvd_coordinate_shift p a t ha h.1

end A354766Research

#print axioms A354766Research.exists_isotropic_coordinate_shift
#print axioms A354766Research.exists_normalized_isotropic_lift
