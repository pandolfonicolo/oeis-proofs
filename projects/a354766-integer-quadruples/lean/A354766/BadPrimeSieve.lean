import Mathlib.Data.Nat.Totient
import Mathlib.Data.Nat.Cast.Order.Field
import Mathlib.Data.Nat.GCD.BigOperators
import Mathlib.Algebra.BigOperators.Associated
import Mathlib.Data.Real.Archimedean
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

/-!
An elementary finite sieve for primes congruent to five modulo six.
This file is independent of the A354766 counting formula.
-/

open scoped BigOperators
open Finset

namespace A354766Sieve

def BadPrime (p : ℕ) : Prop := p.Prime ∧ p % 6 = 5

instance (p : ℕ) : Decidable (BadPrime p) := by
  unfold BadPrime
  infer_instance

def Admissible (q : ℕ) : Prop :=
  0 < q ∧ ∀ p, p.Prime → p ∣ q → p % 6 = 5

theorem prime_eq_two_or_three_or_mod_six {p : ℕ} (hp : p.Prime) :
    p = 2 ∨ p = 3 ∨ p % 6 = 1 ∨ p % 6 = 5 := by
  by_cases hp2 : p = 2
  · exact Or.inl hp2
  right
  by_cases hp3 : p = 3
  · exact Or.inl hp3
  right
  have hoddmod : p % 2 = 1 := Nat.odd_iff.mp (hp.odd_of_ne_two hp2)
  have hmod3 : p % 3 ≠ 0 := by
    intro h
    have hdvd : 3 ∣ p := Nat.dvd_iff_mod_eq_zero.mpr h
    have heq : 3 = p :=
      (Nat.prime_dvd_prime_iff_eq Nat.prime_three hp).mp hdvd
    exact hp3 heq.symm
  omega

theorem prod_mod_six_eq_one {s : Finset ℕ} {f : ℕ → ℕ}
    (h : ∀ p ∈ s, f p % 6 = 1) :
    (∏ p ∈ s, f p) % 6 = 1 := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert p s hpMem ih =>
      rw [Finset.prod_insert hpMem, Nat.mul_mod]
      rw [h p (Finset.mem_insert_self p s),
        ih (fun q hq => h q (Finset.mem_insert_of_mem hq))]

theorem exists_bad_prime_dvd {n : ℕ} (hn : n % 6 = 5) :
    ∃ p, p.Prime ∧ p ∣ n ∧ p % 6 = 5 := by
  have hn0 : n ≠ 0 := by omega
  by_contra! h
  have hprimes : ∀ p ∈ n.primeFactors, p % 6 = 1 := by
    intro p hpMem
    have hp : p.Prime := Nat.prime_of_mem_primeFactors hpMem
    have hpdvd : p ∣ n := (Nat.mem_primeFactors.mp hpMem).2.1
    rcases prime_eq_two_or_three_or_mod_six hp with hp2 | hp3 | hp1 | hp5
    · subst p
      have h2 := Nat.dvd_iff_mod_eq_zero.mp hpdvd
      omega
    · subst p
      have h3 := Nat.dvd_iff_mod_eq_zero.mp hpdvd
      omega
    · exact hp1
    · exact False.elim (h p hp hpdvd hp5)
  have hpow : ∀ p ∈ n.primeFactors, (p ^ n.factorization p) % 6 = 1 := by
    intro p hpMem
    rw [Nat.pow_mod, hprimes p hpMem]
    simp
  have hprod := prod_mod_six_eq_one hpow
  have hnprod : (∏ p ∈ n.primeFactors, p ^ n.factorization p) = n := by
    exact Nat.factorization_prod_pow_eq_self hn0
  rw [hnprod] at hprod
  omega

theorem admissible_coprime_six {q : ℕ} (hq : Admissible q) :
    Nat.Coprime 6 q := by
  apply Nat.coprime_of_dvd
  intro p hp hp6 hpq
  have hp5 := hq.2 p hp hpq
  have hp_le : p ≤ 6 := Nat.le_of_dvd (by norm_num) hp6
  have hp_eq : p = 5 := by omega
  subst p
  norm_num at hp6

def residueSieve (q : ℕ) : Finset ℕ :=
  (Finset.range (6 * q)).filter fun n => n % 6 = 5 ∧ q.Coprime n

theorem residueSieve_card {q : ℕ} (hq0 : q ≠ 0) (hq6 : Nat.Coprime 6 q) :
    (residueSieve q).card = q.totient := by
  classical
  rw [Nat.totient_eq_card_coprime]
  symm
  apply Finset.card_bij fun n _ => (Nat.chineseRemainder hq6 5 n).val
  · intro n hn
    rcases Finset.mem_filter.mp hn with ⟨hnRange, hnCop⟩
    have hnlt : n < q := Finset.mem_range.mp hnRange
    refine Finset.mem_filter.mpr ⟨Finset.mem_range.mpr ?_, ?_, ?_⟩
    · exact Nat.chineseRemainder_lt_mul hq6 5 n (by norm_num) hq0
    · simpa [Nat.ModEq] using
        (Nat.chineseRemainder hq6 5 n).property.1
    · change Nat.gcd q (Nat.chineseRemainder hq6 5 n).val = 1
      rw [Nat.gcd_comm, (Nat.chineseRemainder hq6 5 n).property.2.gcd_eq,
        Nat.gcd_comm]
      exact hnCop
  · intro n hn m hm hnm
    have hnlt : n < q := Finset.mem_range.mp (Finset.mem_filter.mp hn).1
    have hmlt : m < q := Finset.mem_range.mp (Finset.mem_filter.mp hm).1
    calc
      n = (Nat.chineseRemainder hq6 5 n).val % q := by
        symm
        simpa only [Nat.ModEq, Nat.mod_eq_of_lt hnlt] using
          (Nat.chineseRemainder hq6 5 n).property.2
      _ = (Nat.chineseRemainder hq6 5 m).val % q := congrArg (· % q) hnm
      _ = m := by
        simpa only [Nat.ModEq, Nat.mod_eq_of_lt hmlt] using
          (Nat.chineseRemainder hq6 5 m).property.2
  · intro n hn
    rcases Finset.mem_filter.mp hn with ⟨hnRange, hnMod, hnCop⟩
    have hnlt : n < 6 * q := Finset.mem_range.mp hnRange
    refine ⟨n % q, Finset.mem_filter.mpr ⟨?_, ?_⟩, ?_⟩
    · exact Finset.mem_range.mpr (Nat.mod_lt n (Nat.pos_of_ne_zero hq0))
    · have hm : n % q ≡ n [MOD q] := by simp [Nat.ModEq]
      change Nat.gcd q (n % q) = 1
      rw [Nat.gcd_comm, hm.gcd_eq, Nat.gcd_comm]
      exact hnCop
    · symm
      apply (Nat.chineseRemainder_modEq_unique hq6 ?_ ?_).eq_of_lt_of_lt hnlt
      · exact Nat.chineseRemainder_lt_mul hq6 5 (n % q) (by norm_num) hq0
      · simpa [Nat.ModEq] using hnMod
      · simp [Nat.ModEq]

theorem one_add_sum_le_prod_one_add {ι : Type*} (s : Finset ι) (f : ι → ℝ)
    (hf : ∀ i ∈ s, 0 ≤ f i) :
    1 + ∑ i ∈ s, f i ≤ ∏ i ∈ s, (1 + f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert a s ha ih =>
      have hfa : 0 ≤ f a := hf a (Finset.mem_insert_self a s)
      have hfs : ∀ i ∈ s, 0 ≤ f i :=
        fun i hi => hf i (Finset.mem_insert_of_mem hi)
      have hsum : 0 ≤ ∑ i ∈ s, f i := Finset.sum_nonneg hfs
      have hmul := mul_le_mul_of_nonneg_left (ih hfs) (by linarith : 0 ≤ 1 + f a)
      rw [Finset.sum_insert ha, Finset.prod_insert ha]
      nlinarith [mul_nonneg hfa hsum]

theorem reciprocal_product_lower_bound (s : Finset ℕ)
    (hs : ∀ p ∈ s, 1 < p) :
    1 + ∑ p ∈ s, (p : ℝ)⁻¹ ≤ ∏ p ∈ s, ((p : ℝ) / ((p : ℝ) - 1)) := by
  calc
    1 + ∑ p ∈ s, (p : ℝ)⁻¹ ≤ ∏ p ∈ s, (1 + (p : ℝ)⁻¹) :=
      one_add_sum_le_prod_one_add s _ (by intros; positivity)
    _ ≤ ∏ p ∈ s, ((p : ℝ) / ((p : ℝ) - 1)) := by
      apply Finset.prod_le_prod
      · intro p hp
        positivity
      · intro p hp
        have hp1 : (1 : ℝ) < p := by exact_mod_cast hs p hp
        have hp0 : (0 : ℝ) < p := by linarith
        rw [le_div_iff₀ (by linarith : (0 : ℝ) < p - 1)]
        have hinv : (p : ℝ)⁻¹ * p = 1 := inv_mul_cancel₀ (ne_of_gt hp0)
        have hinv0 : 0 ≤ (p : ℝ)⁻¹ := inv_nonneg.mpr hp0.le
        nlinarith

theorem reciprocal_ratio_step (s : Finset ℕ) (b : ℝ) (hb : 0 ≤ b)
    (hs : ∀ p ∈ s, 1 < p)
    (hgain : (1 : ℝ) / 6 ≤ b * ∑ p ∈ s, (p : ℝ)⁻¹) :
    b + 1 / 6 ≤ b * ∏ p ∈ s, ((p : ℝ) / ((p : ℝ) - 1)) := by
  have hprod := mul_le_mul_of_nonneg_left (reciprocal_product_lower_bound s hs) hb
  nlinarith

end A354766Sieve

namespace A354766Sieve

def newBadPrimes (q : ℕ) : Finset ℕ :=
  (Finset.range (6 * q + 1)).filter fun p => BadPrime p ∧ ¬p ∣ q

theorem mem_newBadPrimes {p q : ℕ} :
    p ∈ newBadPrimes q ↔ p ≤ 6 * q ∧ p.Prime ∧ p % 6 = 5 ∧ ¬p ∣ q := by
  simp only [newBadPrimes, Finset.mem_filter, Finset.mem_range, Nat.lt_succ_iff,
    BadPrime, and_assoc]

theorem residueSieve_subset_multiples_union (q : ℕ) :
    residueSieve q ⊆ (newBadPrimes q).biUnion
      (fun p => (Finset.Ioc 0 (6 * q)).filter fun n => p ∣ n) := by
  classical
  intro n hn
  rcases Finset.mem_filter.mp hn with ⟨hnRange, hnMod, hnCop⟩
  have hnlt : n < 6 * q := Finset.mem_range.mp hnRange
  obtain ⟨p, hp, hpn, hpMod⟩ := exists_bad_prime_dvd hnMod
  have hnpos : 0 < n := by omega
  have hpq : ¬p ∣ q := by
    intro hpq
    have hdiv : p ∣ q.gcd n := Nat.dvd_gcd hpq hpn
    have hdivone : p ∣ 1 := hnCop ▸ hdiv
    exact hp.ne_one (Nat.dvd_one.mp hdivone)
  apply Finset.mem_biUnion.mpr
  refine ⟨p, mem_newBadPrimes.mpr ⟨?_, hp, hpMod, hpq⟩, ?_⟩
  · exact (Nat.le_of_dvd hnpos hpn).trans hnlt.le
  · exact Finset.mem_filter.mpr ⟨Finset.mem_Ioc.mpr ⟨hnpos, hnlt.le⟩, hpn⟩

theorem totient_le_sum_div_newBadPrimes {q : ℕ} (hq : Admissible q) :
    q.totient ≤ ∑ p ∈ newBadPrimes q, (6 * q) / p := by
  classical
  calc
    q.totient = (residueSieve q).card :=
      (residueSieve_card (Nat.ne_of_gt hq.1) (admissible_coprime_six hq)).symm
    _ ≤ ((newBadPrimes q).biUnion
        (fun p => (Finset.Ioc 0 (6 * q)).filter fun n => p ∣ n)).card :=
      Finset.card_le_card (residueSieve_subset_multiples_union q)
    _ ≤ ∑ p ∈ newBadPrimes q,
        ((Finset.Ioc 0 (6 * q)).filter fun n => p ∣ n).card :=
      Finset.card_biUnion_le
    _ = ∑ p ∈ newBadPrimes q, (6 * q) / p := by
      apply Finset.sum_congr rfl
      intro p hp
      exact Nat.Ioc_filter_dvd_card_eq_div (6 * q) p

theorem reciprocal_sum_newBadPrimes_lower_bound {q : ℕ} (hq : Admissible q) :
    (q.totient : ℝ) / (6 * q) ≤ ∑ p ∈ newBadPrimes q, (p : ℝ)⁻¹ := by
  have hnat := totient_le_sum_div_newBadPrimes hq
  have hcast : (q.totient : ℝ) ≤
      ∑ p ∈ newBadPrimes q, (((6 * q) / p : ℕ) : ℝ) := by
    exact_mod_cast hnat
  have hsum : (q.totient : ℝ) ≤
      (6 * q : ℝ) * ∑ p ∈ newBadPrimes q, (p : ℝ)⁻¹ := by
    calc
      (q.totient : ℝ) ≤ ∑ p ∈ newBadPrimes q, (((6 * q) / p : ℕ) : ℝ) := hcast
      _ ≤ ∑ p ∈ newBadPrimes q, ((6 * q : ℕ) : ℝ) / p := by
        exact Finset.sum_le_sum (fun p hp => Nat.cast_div_le)
      _ = (6 * q : ℝ) * ∑ p ∈ newBadPrimes q, (p : ℝ)⁻¹ := by
        simp only [Nat.cast_mul, Nat.cast_ofNat, div_eq_mul_inv, Finset.mul_sum]
  have hqpos : (0 : ℝ) < q := by exact_mod_cast hq.1
  exact (div_le_iff₀ (by positivity : (0 : ℝ) < 6 * q)).mpr (by simpa [mul_comm] using hsum)

end A354766Sieve

namespace A354766Sieve

theorem totient_prod_primes (s : Finset ℕ) (hs : ∀ p ∈ s, p.Prime) :
    (∏ p ∈ s, p).totient = ∏ p ∈ s, (p - 1) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert p s hpNotMem ih =>
      have hp : p.Prime := hs p (Finset.mem_insert_self p s)
      have hs' : ∀ r ∈ s, r.Prime :=
        fun r hr => hs r (Finset.mem_insert_of_mem hr)
      have hcop : p.Coprime (∏ r ∈ s, r) := by
        apply Nat.coprime_prod_right_iff.mpr
        intro r hr
        apply (Nat.coprime_primes hp (hs' r hr)).mpr
        intro heq
        exact hpNotMem (heq.symm ▸ hr)
      rw [Finset.prod_insert hpNotMem, Nat.totient_mul hcop,
        Nat.totient_prime hp, ih hs', Finset.prod_insert hpNotMem]

def extendModulus (q : ℕ) : ℕ := q * ∏ p ∈ newBadPrimes q, p

theorem extendModulus_admissible {q : ℕ} (hq : Admissible q) :
    Admissible (extendModulus q) := by
  classical
  constructor
  · apply Nat.mul_pos hq.1
    apply Finset.prod_pos
    intro p hp
    exact (mem_newBadPrimes.mp hp).2.1.pos
  · intro p hp hpdvd
    rcases hp.dvd_mul.mp hpdvd with hpq | hpG
    · exact hq.2 p hp hpq
    · obtain ⟨r, hr, hpr⟩ := (hp.prime.dvd_finset_prod_iff (fun r : ℕ => r)).mp hpG
      have hrprime := (mem_newBadPrimes.mp hr).2.1
      have heq : p = r := (Nat.prime_dvd_prime_iff_eq hp hrprime).mp hpr
      simpa only [heq] using (mem_newBadPrimes.mp hr).2.2.1

theorem reciprocal_totient_extendModulus {q : ℕ} (_hq : Admissible q) :
    (extendModulus q : ℝ) / (extendModulus q).totient =
      ((q : ℝ) / q.totient) *
        ∏ p ∈ newBadPrimes q, ((p : ℝ) / ((p : ℝ) - 1)) := by
  classical
  have hprimes : ∀ p ∈ newBadPrimes q, p.Prime :=
    fun p hp => (mem_newBadPrimes.mp hp).2.1
  have hcop : q.Coprime (∏ p ∈ newBadPrimes q, p) := by
    apply Nat.coprime_prod_right_iff.mpr
    intro p hp
    exact ((hprimes p hp).coprime_iff_not_dvd.mpr
      (mem_newBadPrimes.mp hp).2.2.2).symm
  rw [extendModulus, Nat.totient_mul hcop, totient_prod_primes _ hprimes]
  simp only [Nat.cast_mul, Nat.cast_prod]
  rw [mul_div_mul_comm, ← Finset.prod_div_distrib]
  congr 1
  apply Finset.prod_congr rfl
  intro p hp
  rw [Nat.cast_sub (hprimes p hp).one_le, Nat.cast_one]

theorem reciprocal_totient_extension_gain {q : ℕ} (hq : Admissible q) :
    ((q : ℝ) / q.totient) + 1 / 6 ≤
      (extendModulus q : ℝ) / (extendModulus q).totient := by
  have hqpos : (0 : ℝ) < q := by exact_mod_cast hq.1
  have hphipos : (0 : ℝ) < q.totient := by
    exact_mod_cast Nat.totient_pos.mpr hq.1
  have hsum := reciprocal_sum_newBadPrimes_lower_bound hq
  have hgain : (1 : ℝ) / 6 ≤
      ((q : ℝ) / q.totient) * ∑ p ∈ newBadPrimes q, (p : ℝ)⁻¹ := by
    calc
      (1 : ℝ) / 6 = ((q : ℝ) / q.totient) *
          ((q.totient : ℝ) / (6 * q)) := by
        field_simp [ne_of_gt hqpos, ne_of_gt hphipos]
      _ ≤ ((q : ℝ) / q.totient) *
          ∑ p ∈ newBadPrimes q, (p : ℝ)⁻¹ :=
        mul_le_mul_of_nonneg_left hsum (by positivity)
  rw [reciprocal_totient_extendModulus hq]
  apply reciprocal_ratio_step _ _ (by positivity) _ hgain
  intro p hp
  exact (mem_newBadPrimes.mp hp).2.1.one_lt

theorem exists_admissible_reciprocal_ratio_ge (t : ℕ) :
    ∃ q, Admissible q ∧ 1 + (t : ℝ) / 6 ≤ (q : ℝ) / q.totient := by
  induction t with
  | zero =>
      refine ⟨1, ?_, ?_⟩
      · constructor
        · norm_num
        · intro p hp hpdvd
          exact False.elim (hp.ne_one (Nat.dvd_one.mp hpdvd))
      · norm_num
  | succ t ih =>
      obtain ⟨q, hq, hbound⟩ := ih
      refine ⟨extendModulus q, extendModulus_admissible hq, ?_⟩
      have hgain := reciprocal_totient_extension_gain hq
      simp only [Nat.cast_add, Nat.cast_one]
      linarith

theorem exists_admissible_totient_ratio_lt (ε : ℝ) (hε : 0 < ε) :
    ∃ q, Admissible q ∧ (q.totient : ℝ) / q < ε := by
  obtain ⟨t, ht⟩ := exists_nat_gt ((6 : ℝ) / ε)
  obtain ⟨q, hq, hbound⟩ := exists_admissible_reciprocal_ratio_ge t
  refine ⟨q, hq, ?_⟩
  have hqpos : (0 : ℝ) < q := by exact_mod_cast hq.1
  have hphipos : (0 : ℝ) < q.totient := by
    exact_mod_cast Nat.totient_pos.mpr hq.1
  have ht' : (1 : ℝ) / ε < (t : ℝ) / 6 := by
    apply (lt_div_iff₀ (by norm_num : (0 : ℝ) < 6)).mpr
    simpa [div_eq_mul_inv, mul_comm] using ht
  have hlarge : (1 : ℝ) / ε < (q : ℝ) / q.totient := by
    linarith
  have hcross := (div_lt_div_iff₀ hε hphipos).mp hlarge
  apply (div_lt_iff₀ hqpos).mpr
  simpa [mul_comm] using hcross

end A354766Sieve
