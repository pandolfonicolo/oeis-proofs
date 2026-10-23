import Mathlib.Data.Nat.Factorization.Induction
import Mathlib.Data.Nat.Factorization.Basic
import Mathlib.Algebra.Ring.Parity
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum

/-!
# Euler product from the explicit odd-prime recurrences

The hypotheses describe only recurrences and the normalization at one.
No Euler product or multiplicativity assumption is made.  In fact the proof
works for an arbitrary integer-valued `χ`, without restrictions on its values.
-/

namespace A354766Research

/-- The structural input to be supplied by the lattice/counting argument. -/
structure OddPrimeRecurrences (F χ : ℕ → ℤ) : Prop where
  at_one : F 1 = 8
  first_step : ∀ (p b : ℕ), p.Prime → Odd p → 0 < b → Odd b → ¬ p ∣ b →
    F (p * b) = ((p : ℤ) - χ p) * F b
  repeated_step : ∀ (p m : ℕ), p.Prime → Odd p → 0 < m → Odd m → p ∣ m →
    F (p * m) = ((p : ℤ) + 1) * F m -
      (if p ∣ m / p then (p : ℤ) else (p : ℤ) - χ p) * F (m / p)

/-- Pure algebra: the exceptional second term determines every later term. -/
theorem sequence_from_recurrence (A : ℕ → ℤ) (q c : ℤ)
    (h₁ : A 1 = (q - c) * A 0)
    (h₂ : A 2 = (q + 1) * A 1 - (q - c) * A 0)
    (hrec : ∀ n : ℕ, A (n + 3) = (q + 1) * A (n + 2) - q * A (n + 1))
    (n : ℕ) : A (n + 1) = q ^ n * (q - c) * A 0 := by
  induction n using Nat.twoStepInduction with
  | zero => simpa using h₁
  | one => rw [h₂, h₁]; ring
  | more n hn hn₁ =>
    rw [show n + 2 + 1 = n + 3 by omega, hrec, hn₁, hn]
    ring

/-- A prime-power multiple, with the exponent written as `n+1`. -/
theorem prime_power_mul_succ {F χ : ℕ → ℤ} (h : OddPrimeRecurrences F χ)
    {p b : ℕ} (hp : p.Prime) (hpo : Odd p) (hb : 0 < b) (hbo : Odd b)
    (hpb : ¬ p ∣ b) (n : ℕ) :
    F (p ^ (n + 1) * b) = (p : ℤ) ^ n * ((p : ℤ) - χ p) * F b := by
  have hdiv (k : ℕ) : (p ^ (k + 1) * b) / p = p ^ k * b := by
    rw [pow_succ', mul_assoc, Nat.mul_div_cancel_left _ hp.pos]
  have hpos (k : ℕ) : 0 < p ^ k * b := mul_pos (pow_pos hp.pos _) hb
  have hodd (k : ℕ) : Odd (p ^ k * b) := (hpo.pow).mul hbo
  have hdvd (k : ℕ) : p ∣ p ^ (k + 1) * b := by
    rw [pow_succ', mul_assoc]
    exact dvd_mul_right _ _
  have hmul (k : ℕ) : p * (p ^ k * b) = p ^ (k + 1) * b := by
    rw [pow_succ', mul_assoc]
  have h₁ : F (p ^ 1 * b) = ((p : ℤ) - χ p) * F (p ^ 0 * b) := by
    simpa using h.first_step p b hp hpo hb hbo hpb
  have h₂ : F (p ^ 2 * b) = ((p : ℤ) + 1) * F (p ^ 1 * b) -
      ((p : ℤ) - χ p) * F (p ^ 0 * b) := by
    have hr := h.repeated_step p (p ^ 1 * b) hp hpo (hpos 1) (hodd 1) (hdvd 0)
    simpa only [hmul, hdiv, pow_zero, one_mul, if_neg hpb] using hr
  have hr (k : ℕ) : F (p ^ (k + 3) * b) =
      ((p : ℤ) + 1) * F (p ^ (k + 2) * b) - (p : ℤ) * F (p ^ (k + 1) * b) := by
    have hr := h.repeated_step p (p ^ (k + 2) * b) hp hpo
      (hpos (k + 2)) (hodd (k + 2)) (hdvd (k + 1))
    simpa only [hmul, hdiv, if_pos (hdvd k)] using hr
  simpa using sequence_from_recurrence (fun k => F (p ^ k * b)) (p : ℤ) (χ p)
    h₁ h₂ hr n

/-- Closed form on a prime-power multiple, for any positive exponent. -/
theorem prime_power_mul {F χ : ℕ → ℤ} (h : OddPrimeRecurrences F χ)
    {p b a : ℕ} (hp : p.Prime) (hpo : Odd p) (hb : 0 < b) (hbo : Odd b)
    (hpb : ¬ p ∣ b) (ha : 1 ≤ a) :
    F (p ^ a * b) = (p : ℤ) ^ (a - 1) * ((p : ℤ) - χ p) * F b := by
  obtain ⟨n, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : a ≠ 0)
  simpa using prime_power_mul_succ h hp hpo hb hbo hpb n

/-- The Euler product, directly from the recurrence hypotheses. -/
theorem euler_product {F χ : ℕ → ℤ} (h : OddPrimeRecurrences F χ)
    {m : ℕ} (hm : 0 < m) (hmo : Odd m) :
    F m = 8 * ∏ p ∈ m.primeFactors,
      ((p : ℤ) ^ (m.factorization p - 1) * ((p : ℤ) - χ p)) := by
  classical
  suffices hprod : ∀ n : ℕ, 0 < n → Odd n →
      F n = 8 * n.factorization.prod
        (fun p a => (p : ℤ) ^ (a - 1) * ((p : ℤ) - χ p)) by
    exact hprod m hm hmo
  apply Nat.recOnPrimePow
  · intro hzero _
    omega
  · intro _ _
    simpa using h.at_one
  · intro b p a hp hpb ha ih hpos hodd
    have hb : 0 < b := Nat.pos_of_mul_pos_left hpos
    have hbo : Odd b := (Nat.odd_mul.mp hodd).2
    have hpo : Odd p := (Nat.odd_pow_iff (by omega : a ≠ 0)).mp
      (Nat.odd_mul.mp hodd).1
    have hcop : (p ^ a).Coprime b :=
      ((hp.coprime_iff_not_dvd).mpr hpb).pow_left a
    rw [prime_power_mul h hp hpo hb hbo hpb ha, ih hb hbo,
      Nat.factorization_mul (pow_ne_zero _ hp.ne_zero) hb.ne',
      Finsupp.prod_add_index_of_disjoint hcop.disjoint_primeFactors,
      hp.factorization_pow]
    have hsingle : (Finsupp.single p a).prod
        (fun q k => (q : ℤ) ^ (k - 1) * ((q : ℤ) - χ q)) =
        (p : ℤ) ^ (a - 1) * ((p : ℤ) - χ p) := by
      simp [Finsupp.prod, Finsupp.support_single_ne_zero p (by omega : a ≠ 0)]
    rw [hsingle]
    ring

/-- The equivalent rational Euler product, with nonzero denominators proved
from membership in `m.primeFactors`. -/
theorem euler_product_rat {F χ : ℕ → ℤ} (h : OddPrimeRecurrences F χ)
    {m : ℕ} (hm : 0 < m) (hmo : Odd m) :
    (F m : ℚ) = 8 * (m : ℚ) *
      ∏ p ∈ m.primeFactors, (1 - (χ p : ℚ) / (p : ℚ)) := by
  classical
  have hcast : (F m : ℚ) = 8 * ∏ p ∈ m.primeFactors,
      ((p : ℚ) ^ (m.factorization p - 1) * ((p : ℚ) - (χ p : ℚ))) := by
    exact_mod_cast euler_product h hm hmo
  have hpow : (∏ p ∈ m.primeFactors, (p : ℚ) ^ m.factorization p) = (m : ℚ) := by
    have hnat := Nat.factorization_prod_pow_eq_self hm.ne'
    change (∏ p ∈ m.primeFactors, p ^ m.factorization p) = m at hnat
    exact_mod_cast hnat
  have hfactor (p : ℕ) (hpm : p ∈ m.primeFactors) :
      (p : ℚ) ^ (m.factorization p - 1) * ((p : ℚ) - (χ p : ℚ)) =
      (p : ℚ) ^ m.factorization p * (1 - (χ p : ℚ) / (p : ℚ)) := by
    have hp : p.Prime := Nat.prime_of_mem_primeFactors hpm
    have hp0 : (p : ℚ) ≠ 0 := by exact_mod_cast hp.ne_zero
    have ha : 1 ≤ m.factorization p :=
      hp.factorization_pos_of_dvd hm.ne' (Nat.dvd_of_mem_primeFactors hpm)
    have hc : (p : ℚ) * (1 - (χ p : ℚ) / (p : ℚ)) = (p : ℚ) - (χ p : ℚ) := by
      rw [mul_sub, mul_one, mul_div_cancel₀ _ hp0]
    calc
      _ = (p : ℚ) ^ (m.factorization p - 1) *
          ((p : ℚ) * (1 - (χ p : ℚ) / (p : ℚ))) := by rw [hc]
      _ = _ := by rw [← mul_assoc, ← pow_succ, Nat.sub_add_cancel ha]
  calc
    (F m : ℚ) = 8 * ∏ p ∈ m.primeFactors,
        ((p : ℚ) ^ m.factorization p * (1 - (χ p : ℚ) / (p : ℚ))) := by
      rw [hcast]
      congr 1
      exact Finset.prod_congr rfl hfactor
    _ = 8 * (m : ℚ) * ∏ p ∈ m.primeFactors, (1 - (χ p : ℚ) / (p : ℚ)) := by
      rw [Finset.prod_mul_distrib, hpow, mul_assoc]

end A354766Research

#print axioms A354766Research.prime_power_mul
#print axioms A354766Research.euler_product
#print axioms A354766Research.euler_product_rat
