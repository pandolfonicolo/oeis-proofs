import A354766.BadPrimeSieve
import Mathlib.Data.Set.Card
import Mathlib.Topology.MetricSpace.Pseudo.Defs
import Mathlib.Topology.Instances.Real.Lemmas

open Set Filter
open scoped BigOperators Topology

namespace A354766Sieve

def AvoidsBadPrimes (S : Set ℕ) : Prop :=
  ∀ n ∈ S, 0 < n → ∀ p, p.Prime → p % 6 = 5 → ¬p ∣ n

theorem count_avoiding_le_sieve (S : Set ℕ) (hS : AvoidsBadPrimes S)
    (N q : ℕ) (hq : Admissible q) :
    (S ∩ Icc 1 N).ncard ≤ q.totient * (N / q + 1) := by
  classical
  let C : Finset ℕ := (Finset.Ico 1 (1 + N)).filter fun n => q.Coprime n
  have hsub : S ∩ Icc 1 N ⊆ (C : Set ℕ) := by
    intro n hn
    rcases hn with ⟨hnS, hnOne, hnN⟩
    simp only [C, Finset.mem_coe, Finset.mem_filter, Finset.mem_Ico]
    refine ⟨⟨hnOne, by omega⟩, ?_⟩
    apply Nat.coprime_of_dvd
    intro p hp hpq hpn
    exact False.elim (hS n hnS (by omega) p hp (hq.2 p hp hpq) hpn)
  calc
    (S ∩ Icc 1 N).ncard ≤ (C : Set ℕ).ncard :=
      Set.ncard_le_ncard hsub (Finset.finite_toSet C)
    _ = C.card := Set.ncard_coe_finset C
    _ ≤ q.totient * (N / q + 1) := by
      simpa [C, Nat.coprime_comm, Nat.add_comm] using
        (Nat.Ico_filter_coprime_le (a := q) 1 N (Nat.ne_of_gt hq.1))

theorem density_small_eventually (S : Set ℕ) (hS : AvoidsBadPrimes S)
    (ε : ℝ) (hε : 0 < ε) :
    ∃ N : ℕ, ∀ n ≥ N,
      (((S ∩ Icc 1 n).ncard : ℕ) : ℝ) / n < ε := by
  obtain ⟨q, hq, hratio⟩ := exists_admissible_totient_ratio_lt (ε / 2) (by positivity)
  obtain ⟨N, hN⟩ := exists_nat_gt (2 * (q.totient : ℝ) / ε)
  refine ⟨max N 1, ?_⟩
  intro n hn
  have hnpos : 0 < n := lt_of_lt_of_le Nat.zero_lt_one ((le_max_right N 1).trans hn)
  have hnR : (0 : ℝ) < n := by exact_mod_cast hnpos
  have hqR : (0 : ℝ) < q := by exact_mod_cast hq.1
  have hNn : N ≤ n := (le_max_left N 1).trans hn
  have hnlarge : 2 * (q.totient : ℝ) / ε < n :=
    hN.trans_le (by exact_mod_cast hNn)
  have hphin : (q.totient : ℝ) / n < ε / 2 := by
    apply (div_lt_iff₀ hnR).mpr
    have hcross := (div_lt_iff₀ hε).mp hnlarge
    nlinarith
  have hcountNat := count_avoiding_le_sieve S hS n q hq
  have hcount : (((S ∩ Icc 1 n).ncard : ℕ) : ℝ) ≤
      (q.totient : ℝ) * (((n / q : ℕ) : ℝ) + 1) := by
    exact_mod_cast hcountNat
  have hcount' : (((S ∩ Icc 1 n).ncard : ℕ) : ℝ) ≤
      (q.totient : ℝ) * ((n : ℝ) / q + 1) := by
    have hdiv : ((n / q : ℕ) : ℝ) ≤ (n : ℝ) / q := Nat.cast_div_le
    have hadd : ((n / q : ℕ) : ℝ) + 1 ≤ (n : ℝ) / q + 1 := by linarith
    exact hcount.trans (mul_le_mul_of_nonneg_left hadd (by positivity))
  calc
    (((S ∩ Icc 1 n).ncard : ℕ) : ℝ) / n ≤
        ((q.totient : ℝ) * ((n : ℝ) / q + 1)) / n :=
      div_le_div_of_nonneg_right hcount' hnR.le
    _ = (q.totient : ℝ) / q + (q.totient : ℝ) / n := by
      field_simp [ne_of_gt hnR, ne_of_gt hqR]
      <;> ring
    _ < ε := by linarith

/-- Any set of positive integers avoiding primes five modulo six has density zero. -/
theorem density_zero_of_avoidsBadPrimes (S : Set ℕ) (hS : AvoidsBadPrimes S) :
    Tendsto (fun N : ℕ => (((S ∩ Icc 1 N).ncard : ℕ) : ℝ) / N)
      atTop (𝓝 0) := by
  apply Metric.tendsto_atTop.mpr
  intro ε hε
  obtain ⟨N, hN⟩ := density_small_eventually S hS ε hε
  refine ⟨N, ?_⟩
  intro n hn
  rw [Real.dist_eq, sub_zero, abs_of_nonneg (by positivity)]
  exact hN n hn

end A354766Sieve
