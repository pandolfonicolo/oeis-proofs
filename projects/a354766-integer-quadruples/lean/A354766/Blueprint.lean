import Mathlib.Data.Nat.Totient
import Mathlib.NumberTheory.ArithmeticFunction.Zeta
import A354766.Elementary
import A354766.DoublingBridge
import A354766.NormalizedDecomposition
import A354766.DensityLimit
import A354766.PrimitiveNeighborCount
import A354766.A278085Complement

/-!
# OEIS A354766: arithmetic conclusions

The primitive representation formula is supplied by the explicit, instantiated
lattice-neighbor double count. The density theorem uses the finite CRT sieve.
-/

open Set Filter
open scoped BigOperators Topology

namespace A354766

def content (q : QuadCoords) : ℕ :=
  quadContent q

def quadSet (n : ℕ) : Set QuadCoords :=
  {q | IsQuad (n : ℤ) q}

def primitiveQuadSet (n : ℕ) : Set QuadCoords :=
  {q | q ∈ quadSet n ∧ content q = 1}

def tq (n : ℕ) : ℕ := tqFinite n
def pq (n : ℕ) : ℕ := pqFinite n
def T (n : ℕ) : ℕ := tq n / 4
def P (n : ℕ) : ℕ := pq n / 4

theorem A278085Primary_eq_P (n : ℕ) : A278085Primary n = P n := by
  simpa only [P, pq] using A278085Primary_eq_normalized_count n

def IsMultiplicative (f : ℕ → ℕ) : Prop :=
  f 1 = 1 ∧ ∀ ⦃m n : ℕ⦄, Nat.Coprime m n → f (m * n) = f m * f n

def primitiveThreeSquareSet (N : ℕ) : Set (ℤ × ℤ × ℤ) :=
  {u | u.1 ^ 2 + u.2.1 ^ 2 + u.2.2 ^ 2 = (N : ℤ) ∧
    Nat.gcd u.1.natAbs (Nat.gcd u.2.1.natAbs u.2.2.natAbs) = 1}

def r3Primitive (N : ℕ) : ℕ := r3PrimitiveFinite N

/-- The elementary counting bridge. This is the first substantial target. -/
theorem primitive_quad_count_bridge (n : ℕ) (hn : 0 < n) :
    pq n =
      if Odd n then r3Primitive (3 * n ^ 2) / 2
      else if n % 4 = 2 then r3Primitive (3 * (n / 2) ^ 2) / 2
      else 0 := by
  have _hnUsed : n ≠ 0 := Nat.ne_of_gt hn
  by_cases hodd : Odd n
  · rw [if_pos hodd]
    exact pqFinite_eq_r3PrimitiveFinite_div_two_of_odd hodd
  · rw [if_neg hodd]
    by_cases hmod : n % 4 = 2
    · rw [if_pos hmod]
      exact pqFinite_mod_four_eq_two hmod
    · rw [if_neg hmod]
      have heven : n % 2 = 0 := Nat.not_odd_iff.mp hodd
      have hmodZero : n % 4 = 0 := by
        have hlt := Nat.mod_lt n (by omega : 0 < 4)
        omega
      have hfour : 4 ∣ n := Nat.dvd_iff_mod_eq_zero.mpr hmodZero
      exact pqFinite_eq_zero_of_four_dvd hfour

def chiMinusThree (p : ℕ) : ℤ :=
  if p % 6 = 1 then 1 else if p % 6 = 5 then -1 else 0

noncomputable def cooperHirschhornRhs (m : ℕ) : ℚ :=
  (8 : ℚ) * m *
    ∏ p ∈ m.primeFactors,
      (1 - (chiMinusThree p : ℚ) / (p : ℚ))

/--
The primitive three-square product follows from the concrete lattice-neighbor
double count and the prime-power recurrence, including the ramified prime three.
-/
theorem cooper_hirschhorn_specialization (m : ℕ) (hm : Odd m) :
    (r3Primitive (3 * m ^ 2) : ℚ) = cooperHirschhornRhs m := by
  have hmPos : 0 < m := by
    rcases hm with ⟨a, ha⟩
    omega
  simpa only [r3Primitive, cooperHirschhornRhs, chiMinusThree,
    A354766Research.residueCharacter] using
    A354766Neighbors.primitive_three_squares_euler_product m hmPos hm

noncomputable def primitiveOddRhs (m : ℕ) : ℚ :=
  (m : ℚ) *
    ∏ p ∈ m.primeFactors,
      (1 - (chiMinusThree p : ℚ) / (p : ℚ))

theorem cooperHirschhornRhs_eq (m : ℕ) :
    cooperHirschhornRhs m = 8 * primitiveOddRhs m := by
  simp only [cooperHirschhornRhs, primitiveOddRhs]
  ring

theorem primitiveOddRhs_mul_of_coprime {m n : ℕ} (h : Nat.Coprime m n) :
    primitiveOddRhs (m * n) = primitiveOddRhs m * primitiveOddRhs n := by
  rw [primitiveOddRhs, primitiveOddRhs, primitiveOddRhs,
    h.primeFactors_mul, Finset.prod_union h.disjoint_primeFactors]
  push_cast
  ring

theorem P_cast_eq_primitiveOddRhs {m : ℕ} (hm : Odd m) :
    (P m : ℚ) = primitiveOddRhs m := by
  have hfour : 4 ∣ pqFinite m := four_dvd_pqFinite m
  have htwo := r3PrimitiveFinite_eq_two_mul_pqFinite_of_odd hm
  have htwoQ :
      (r3PrimitiveFinite (3 * m ^ 2) : ℚ) = 2 * (pqFinite m : ℚ) := by
    exact_mod_cast htwo
  calc
    (P m : ℚ) = (pqFinite m : ℚ) / 4 := by
      exact Nat.cast_div_charZero hfour
    _ = (r3PrimitiveFinite (3 * m ^ 2) : ℚ) / 8 := by
      rw [htwoQ]
      ring
    _ = cooperHirschhornRhs m / 8 := by
      have hCH := cooper_hirschhorn_specialization m hm
      simpa only [r3Primitive] using congrArg (fun x : ℚ => x / 8) hCH
    _ = primitiveOddRhs m := by
      rw [cooperHirschhornRhs_eq]
      ring

theorem P_mul_of_odd {m n : ℕ} (hm : Odd m) (hn : Odd n)
    (hcop : Nat.Coprime m n) :
    P (m * n) = P m * P n := by
  have hQ :
      (P (m * n) : ℚ) = (P m : ℚ) * (P n : ℚ) := by
    rw [P_cast_eq_primitiveOddRhs (hm.mul hn),
      P_cast_eq_primitiveOddRhs hm, P_cast_eq_primitiveOddRhs hn,
      primitiveOddRhs_mul_of_coprime hcop]
  exact_mod_cast hQ

theorem P_twice_odd {m : ℕ} (hm : Odd m) : P (2 * m) = P m := by
  simp only [P, pq]
  rw [pqFinite_twice_odd hm]

theorem P_eq_zero_of_four_dvd {n : ℕ} (hn : 4 ∣ n) : P n = 0 := by
  simp [P, pq, pqFinite_eq_zero_of_four_dvd hn]

theorem P_one : P 1 = 1 := by
  have h := P_cast_eq_primitiveOddRhs (by simp : Odd 1)
  norm_num [primitiveOddRhs] at h
  exact_mod_cast h

theorem P_zero : P 0 = 0 := by
  exact P_eq_zero_of_four_dvd (by simp)

theorem P_prime_pow_cast {p k : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hk : k ≠ 0) :
    (P (p ^ k) : ℚ) =
      (p ^ k : ℚ) *
        (1 - (chiMinusThree p : ℚ) / (p : ℚ)) := by
  have hodd : Odd (p ^ k) := (hp.odd_of_ne_two hp2).pow
  rw [P_cast_eq_primitiveOddRhs hodd, primitiveOddRhs,
    Nat.primeFactors_prime_pow hk hp]
  simp

theorem P_prime_pow_mod_six_one {p k : ℕ} (hp : p.Prime)
    (hk : k ≠ 0) (hpmod : p % 6 = 1) :
    P (p ^ k) = p ^ (k - 1) * (p - 1) := by
  have hp2 : p ≠ 2 := by omega
  have hQ := P_prime_pow_cast hp hp2 hk
  rw [chiMinusThree, if_pos hpmod] at hQ
  have hkEq : k - 1 + 1 = k := by omega
  have hpPow : (p : ℚ) ^ k = (p : ℚ) ^ (k - 1) * p := by
    rw [← pow_succ, hkEq]
  have hpQ : (p : ℚ) ≠ 0 := by exact_mod_cast hp.ne_zero
  have htarget :
      (P (p ^ k) : ℚ) = (p ^ (k - 1) * (p - 1) : ℕ) := by
    rw [hQ]
    push_cast
    rw [Nat.cast_sub (by omega : 1 ≤ p), hpPow]
    field_simp [hpQ]
    ring
  exact_mod_cast htarget

theorem P_prime_pow_mod_six_five {p k : ℕ} (hp : p.Prime)
    (hk : k ≠ 0) (hpmod : p % 6 = 5) :
    P (p ^ k) = p ^ (k - 1) * (p + 1) := by
  have hp2 : p ≠ 2 := by omega
  have hQ := P_prime_pow_cast hp hp2 hk
  rw [chiMinusThree, if_neg (by omega : ¬p % 6 = 1), if_pos hpmod] at hQ
  have hkEq : k - 1 + 1 = k := by omega
  have hpPow : (p : ℚ) ^ k = (p : ℚ) ^ (k - 1) * p := by
    rw [← pow_succ, hkEq]
  have hpQ : (p : ℚ) ≠ 0 := by exact_mod_cast hp.ne_zero
  have htarget :
      (P (p ^ k) : ℚ) = (p ^ (k - 1) * (p + 1) : ℕ) := by
    rw [hQ]
    push_cast
    rw [hpPow]
    field_simp [hpQ]
    ring
  exact_mod_cast htarget

theorem P_three_pow {k : ℕ} (hk : k ≠ 0) :
    P (3 ^ k) = 3 ^ k := by
  have hQ := P_prime_pow_cast Nat.prime_three
    (by norm_num) hk
  norm_num [chiMinusThree] at hQ
  exact_mod_cast hQ

theorem P_multiplicative : IsMultiplicative P := by
  constructor
  · exact P_one
  · intro m n hcop
    rcases m.eq_zero_or_pos with rfl | hmPos
    · have hnOne : n = 1 := by
        simpa [Nat.coprime_zero_left] using hcop
      simp [hnOne, P_zero, P_one]
    rcases n.eq_zero_or_pos with rfl | hnPos
    · have hmOne : m = 1 := by
        simpa [Nat.coprime_zero_right] using hcop
      simp [hmOne, P_zero, P_one]
    by_cases hmOdd : Odd m
    · by_cases hnOdd : Odd n
      · exact P_mul_of_odd hmOdd hnOdd hcop
      · have hnEven : n % 2 = 0 := Nat.not_odd_iff.mp hnOdd
        by_cases hnFour : 4 ∣ n
        · have hprodFour : 4 ∣ m * n := dvd_mul_of_dvd_right hnFour m
          simp [P_eq_zero_of_four_dvd hnFour, P_eq_zero_of_four_dvd hprodFour]
        · have hnMod : n % 4 = 2 := by
            rw [Nat.dvd_iff_mod_eq_zero] at hnFour
            have hlt := Nat.mod_lt n (by omega : 0 < 4)
            omega
          have hnEq : n = 2 * (n / 2) := by omega
          have hnHalfOdd : Odd (n / 2) := by
            rw [Nat.odd_iff]
            omega
          have hcopHalf : Nat.Coprime m (n / 2) :=
            hcop.coprime_dvd_right (Nat.div_dvd_of_dvd (by omega : 2 ∣ n))
          have hmnEq : m * n = 2 * (m * (n / 2)) := by
            calc
              m * n = m * (2 * (n / 2)) := congrArg (m * ·) hnEq
              _ = 2 * (m * (n / 2)) := by ring
          have hPn : P n = P (n / 2) := by
            calc
              P n = P (2 * (n / 2)) := congrArg P hnEq
              _ = P (n / 2) := P_twice_odd hnHalfOdd
          calc
            P (m * n) = P (2 * (m * (n / 2))) := by rw [hmnEq]
            _ = P (m * (n / 2)) := P_twice_odd (hmOdd.mul hnHalfOdd)
            _ = P m * P (n / 2) := P_mul_of_odd hmOdd hnHalfOdd hcopHalf
            _ = P m * P n := by rw [hPn]
    · have hmEven : m % 2 = 0 := Nat.not_odd_iff.mp hmOdd
      by_cases hnOdd : Odd n
      · by_cases hmFour : 4 ∣ m
        · have hprodFour : 4 ∣ m * n := dvd_mul_of_dvd_left hmFour n
          simp [P_eq_zero_of_four_dvd hmFour, P_eq_zero_of_four_dvd hprodFour]
        · have hmMod : m % 4 = 2 := by
            rw [Nat.dvd_iff_mod_eq_zero] at hmFour
            have hlt := Nat.mod_lt m (by omega : 0 < 4)
            omega
          have hmEq : m = 2 * (m / 2) := by omega
          have hmHalfOdd : Odd (m / 2) := by
            rw [Nat.odd_iff]
            omega
          have hcopHalf : Nat.Coprime (m / 2) n :=
            hcop.coprime_dvd_left (Nat.div_dvd_of_dvd (by omega : 2 ∣ m))
          have hmnEq : m * n = 2 * ((m / 2) * n) := by
            calc
              m * n = (2 * (m / 2)) * n := congrArg (· * n) hmEq
              _ = 2 * ((m / 2) * n) := by ring
          have hPm : P m = P (m / 2) := by
            calc
              P m = P (2 * (m / 2)) := congrArg P hmEq
              _ = P (m / 2) := P_twice_odd hmHalfOdd
          calc
            P (m * n) = P (2 * ((m / 2) * n)) := by rw [hmnEq]
            _ = P ((m / 2) * n) := P_twice_odd (hmHalfOdd.mul hnOdd)
            _ = P (m / 2) * P n := P_mul_of_odd hmHalfOdd hnOdd hcopHalf
            _ = P m * P n := by rw [hPm]
      · have hnEven : n % 2 = 0 := Nat.not_odd_iff.mp hnOdd
        have htwoM : 2 ∣ m := Nat.dvd_iff_mod_eq_zero.mpr hmEven
        have htwoN : 2 ∣ n := Nat.dvd_iff_mod_eq_zero.mpr hnEven
        have htwoGcd : 2 ∣ Nat.gcd m n := Nat.dvd_gcd htwoM htwoN
        rw [hcop.gcd_eq_one] at htwoGcd
        norm_num at htwoGcd

/-- Every quad decomposes uniquely into its content times a primitive quad. -/
theorem total_as_divisor_sum (n : ℕ) (hn : 0 < n) :
    T n = ∑ d ∈ n.divisors, P d := by
  exact tqFinite_div_four_eq_sum_pqFinite_div_four n hn

theorem T_one : T 1 = 1 := by
  rw [total_as_divisor_sum 1 (by omega)]
  simp [P_one]

theorem T_prime_pow_succ {p : ℕ} (hp : p.Prime) (k : ℕ) :
    T (p ^ (k + 1)) = T (p ^ k) + P (p ^ (k + 1)) := by
  rw [total_as_divisor_sum _ (pow_pos hp.pos _),
    total_as_divisor_sum _ (pow_pos hp.pos _),
    Nat.sum_divisors_prime_pow hp, Nat.sum_divisors_prime_pow hp]
  simp only [Finset.sum_range_succ]

theorem T_prime_pow_mod_six_one {p k : ℕ} (hp : p.Prime)
    (hpmod : p % 6 = 1) :
    T (p ^ k) = p ^ k := by
  induction k with
  | zero => simpa using T_one
  | succ k ih =>
      rw [T_prime_pow_succ hp k, ih,
        P_prime_pow_mod_six_one hp (by omega) hpmod]
      simp only [Nat.add_sub_cancel]
      have hpone : 1 ≤ p := hp.one_le
      rw [pow_succ]
      calc
        p ^ k + p ^ k * (p - 1) =
            p ^ k * 1 + p ^ k * (p - 1) := by simp
        _ = p ^ k * (1 + (p - 1)) := by rw [Nat.mul_add]
        _ = p ^ k * p := by
          congr
          omega

theorem T_three_pow {k : ℕ} :
    T (3 ^ k) = (3 ^ (k + 1) - 1) / 2 := by
  induction k with
  | zero =>
      norm_num
      exact T_one
  | succ k ih =>
      rw [T_prime_pow_succ Nat.prime_three k, ih,
        P_three_pow (by omega)]
      rw [pow_succ, pow_succ]
      omega

theorem T_two_pow_succ {k : ℕ} :
    T (2 ^ (k + 1)) = 2 := by
  induction k with
  | zero =>
      rw [T_prime_pow_succ Nat.prime_two 0]
      have h := P_twice_odd (by norm_num : Odd 1)
      norm_num only [Nat.mul_one] at h
      norm_num only [pow_zero, pow_one, zero_add]
      rw [T_one, h, P_one]
  | succ k ih =>
      rw [T_prime_pow_succ Nat.prime_two (k + 1), ih]
      have hfour : 4 ∣ 2 ^ (k + 1 + 1) := by
        use 2 ^ k
        ring
      rw [P_eq_zero_of_four_dvd hfour]

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

theorem three_dvd_P_prime_pow_succ {p k : ℕ} (hp : p.Prime)
    (hp2 : p ≠ 2) :
    3 ∣ P (p ^ (k + 1)) := by
  rcases prime_eq_two_or_three_or_mod_six hp with
      rfl | rfl | hpmod | hpmod
  · exact False.elim (hp2 rfl)
  · rw [P_three_pow (by omega)]
    exact dvd_pow_self 3 (by omega)
  · rw [P_prime_pow_mod_six_one hp (by omega) hpmod]
    apply dvd_mul_of_dvd_right
    rw [Nat.dvd_iff_mod_eq_zero]
    omega
  · rw [P_prime_pow_mod_six_five hp (by omega) hpmod]
    apply dvd_mul_of_dvd_right
    rw [Nat.dvd_iff_mod_eq_zero]
    omega

theorem T_prime_pow_mod_three {p k : ℕ} (hp : p.Prime)
    (hp2 : p ≠ 2) :
    T (p ^ k) % 3 = 1 := by
  induction k with
  | zero =>
      simpa using congrArg (fun x : ℕ => x % 3) T_one
  | succ k ih =>
      rw [T_prime_pow_succ hp k, Nat.add_mod, ih]
      have hdiv := three_dvd_P_prime_pow_succ hp hp2 (k := k)
      rw [Nat.dvd_iff_mod_eq_zero] at hdiv
      omega

theorem even_P_prime_pow_succ {p k : ℕ} (hp : p.Prime)
    (hp2 : p ≠ 2) (hp3 : p ≠ 3) :
    Even (P (p ^ (k + 1))) := by
  rcases prime_eq_two_or_three_or_mod_six hp with
      rfl | rfl | hpmod | hpmod
  · exact False.elim (hp2 rfl)
  · exact False.elim (hp3 rfl)
  · rw [P_prime_pow_mod_six_one hp (by omega) hpmod]
    rcases hp.odd_of_ne_two hp2 with ⟨a, ha⟩
    apply Even.mul_left
    use a
    omega
  · rw [P_prime_pow_mod_six_five hp (by omega) hpmod]
    rcases hp.odd_of_ne_two hp2 with ⟨a, ha⟩
    apply Even.mul_left
    use a + 1
    omega

theorem odd_T_prime_pow {p k : ℕ} (hp : p.Prime)
    (hp2 : p ≠ 2) (hp3 : p ≠ 3) :
    Odd (T (p ^ k)) := by
  induction k with
  | zero =>
      simpa [T_one]
  | succ k ih =>
      rw [T_prime_pow_succ hp k]
      exact ih.add_even (even_P_prime_pow_succ hp hp2 hp3)

theorem T_prime_pow_ge {p k : ℕ} (hp : p.Prime)
    (hp2 : p ≠ 2) (hp3 : p ≠ 3) :
    p ^ k ≤ T (p ^ k) := by
  rcases prime_eq_two_or_three_or_mod_six hp with
      rfl | rfl | hpmod | hpmod
  · exact False.elim (hp2 rfl)
  · exact False.elim (hp3 rfl)
  · rw [T_prime_pow_mod_six_one hp hpmod]
  · induction k with
    | zero =>
        simpa using le_of_eq T_one.symm
    | succ k ih =>
        rw [T_prime_pow_succ hp k,
          P_prime_pow_mod_six_five hp (by omega) hpmod]
        simp only [Nat.add_sub_cancel, pow_succ]
        calc
          p ^ k * p ≤ p ^ k * (p + 1) := Nat.mul_le_mul_left _ (by omega)
          _ ≤ T (p ^ k) + p ^ k * (p + 1) := Nat.le_add_left _ _

theorem T_prime_pow_eq_iff_mod_six_one {p k : ℕ} (hp : p.Prime)
    (hp2 : p ≠ 2) (hp3 : p ≠ 3) (hk : k ≠ 0) :
    T (p ^ k) = p ^ k ↔ p % 6 = 1 := by
  rcases prime_eq_two_or_three_or_mod_six hp with
      rfl | rfl | hpmod | hpmod
  · exact False.elim (hp2 rfl)
  · exact False.elim (hp3 rfl)
  · simp [hpmod, T_prime_pow_mod_six_one hp hpmod]
  · have hgt : p ^ k < T (p ^ k) := by
      obtain ⟨j, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hk
      rw [T_prime_pow_succ hp j,
        P_prime_pow_mod_six_five hp (by omega) hpmod]
      simp only [Nat.add_sub_cancel, pow_succ]
      calc
        p ^ j * p < p ^ j * (p + 1) :=
          Nat.mul_lt_mul_of_pos_left (by omega) (pow_pos hp.pos j)
        _ ≤ T (p ^ j) + p ^ j * (p + 1) := Nat.le_add_left _ _
    constructor
    · intro heq
      omega
    · intro h
      omega

/-- Main multiplicativity conclusion. -/
theorem multiplicative_conclusion :
    IsMultiplicative P ∧ IsMultiplicative T := by
  refine ⟨P_multiplicative, ?_⟩
  have hTone : T 1 = 1 := by
    rw [total_as_divisor_sum 1 (by omega)]
    simp [P_one]
  let pAF : ArithmeticFunction ℕ := ⟨P, P_zero⟩
  have hpAF : pAF.IsMultiplicative := by
    exact P_multiplicative
  have hconv : (ArithmeticFunction.zeta * pAF).IsMultiplicative :=
    ArithmeticFunction.isMultiplicative_zeta.mul hpAF
  have hT {k : ℕ} (hk : 0 < k) :
      T k = (ArithmeticFunction.zeta * pAF) k := by
    rw [total_as_divisor_sum k hk, ArithmeticFunction.zeta_mul_apply]
    rfl
  constructor
  · exact hTone
  · intro m n hcop
    rcases m.eq_zero_or_pos with rfl | hm
    · have hn : n = 1 := by
        simpa [Nat.coprime_zero_left] using hcop
      simp [hn, hTone]
    rcases n.eq_zero_or_pos with rfl | hn
    · have hmOne : m = 1 := by
        simpa [Nat.coprime_zero_right] using hcop
      simp [hmOne, hTone]
    rw [hT (Nat.mul_pos hm hn), hT hm, hT hn]
    exact hconv.map_mul_of_coprime hcop

theorem T_factorization {n : ℕ} (hn : n ≠ 0) :
    T n = n.factorization.prod fun p k => T (p ^ k) := by
  exact Nat.multiplicative_factorization T
    (fun _ _ h => multiplicative_conclusion.2.2 h) T_one hn

theorem T_odd_no_three_eq_iff {m : ℕ} (hm : Odd m)
    (h3 : ¬3 ∣ m) :
    T m = m ↔ ∀ p ∈ m.primeFactors, p % 6 = 1 := by
  have hm0 : m ≠ 0 := by
    rcases hm with ⟨a, ha⟩
    omega
  have hT := T_factorization hm0
  have hmprod := Nat.factorization_prod_pow_eq_self hm0
  rw [hT]
  conv_lhs =>
    rhs
    rw [← hmprod]
  rw [eq_comm]
  have hle : ∀ p ∈ m.factorization.support,
      p ^ m.factorization p ≤ T (p ^ m.factorization p) := by
    intro p hpMem
    have hpPrimeMem : p ∈ m.primeFactors := by simpa using hpMem
    have hp : p.Prime := Nat.prime_of_mem_primeFactors hpPrimeMem
    have hp2 : p ≠ 2 := by
      intro hpEq
      subst p
      have hdiv : 2 ∣ m := (Nat.mem_primeFactors.mp hpPrimeMem).2.1
      rw [Nat.dvd_iff_mod_eq_zero] at hdiv
      have hoddmod : m % 2 = 1 := Nat.odd_iff.mp hm
      omega
    have hp3 : p ≠ 3 := by
      intro hpEq
      subst p
      exact h3 (Nat.mem_primeFactors.mp hpPrimeMem).2.1
    exact T_prime_pow_ge hp hp2 hp3
  constructor
  · intro hprod p hpMem
    have hpSupp : p ∈ m.factorization.support := by simpa using hpMem
    have hp : p.Prime := Nat.prime_of_mem_primeFactors hpMem
    have hp2 : p ≠ 2 := by
      intro hpEq
      subst p
      have hdiv : 2 ∣ m := (Nat.mem_primeFactors.mp hpMem).2.1
      rw [Nat.dvd_iff_mod_eq_zero] at hdiv
      have hoddmod : m % 2 = 1 := Nat.odd_iff.mp hm
      omega
    have hp3 : p ≠ 3 := by
      intro hpEq
      subst p
      exact h3 (Nat.mem_primeFactors.mp hpMem).2.1
    have hk : m.factorization p ≠ 0 :=
      Finsupp.mem_support_iff.mp hpSupp
    have heqLocal :
        p ^ m.factorization p = T (p ^ m.factorization p) := by
      by_contra hne
      have hlt :
          p ^ m.factorization p < T (p ^ m.factorization p) :=
        lt_of_le_of_ne (hle p hpSupp) hne
      have hprodlt := Finset.prod_lt_prod
        (s := m.factorization.support)
        (f := fun q => q ^ m.factorization q)
        (g := fun q => T (q ^ m.factorization q))
        (fun q hq => by
          have hqMem : q ∈ m.primeFactors := by simpa using hq
          exact pow_pos (Nat.prime_of_mem_primeFactors hqMem).pos _)
        hle ⟨p, hpSupp, hlt⟩
      exact (ne_of_lt hprodlt) hprod
    exact (T_prime_pow_eq_iff_mod_six_one hp hp2 hp3 hk).mp
      heqLocal.symm
  · intro h
    apply Finset.prod_congr rfl
    intro p hpSupp
    have hpMem : p ∈ m.primeFactors := by simpa using hpSupp
    have hp : p.Prime := Nat.prime_of_mem_primeFactors hpMem
    exact (T_prime_pow_mod_six_one hp (h p hpMem)).symm

theorem prod_mod_three_eq_one {s : Finset ℕ} {f : ℕ → ℕ}
    (h : ∀ p ∈ s, f p % 3 = 1) :
    (∏ p ∈ s, f p) % 3 = 1 := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert p s hpMem ih =>
      rw [Finset.prod_insert hpMem, Nat.mul_mod]
      rw [h p (Finset.mem_insert_self p s),
        ih (fun q hq => h q (Finset.mem_insert_of_mem hq))]

theorem prod_mod_two_eq_one {s : Finset ℕ} {f : ℕ → ℕ}
    (h : ∀ p ∈ s, f p % 2 = 1) :
    (∏ p ∈ s, f p) % 2 = 1 := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert p s hpMem ih =>
      rw [Finset.prod_insert hpMem, Nat.mul_mod]
      rw [h p (Finset.mem_insert_self p s),
        ih (fun q hq => h q (Finset.mem_insert_of_mem hq))]

theorem T_mod_three_eq_one_or_two {n : ℕ} (hn : n ≠ 0) :
    T n % 3 = if 2 ∣ n then 2 else 1 := by
  rw [T_factorization hn]
  classical
  by_cases h2 : 2 ∣ n
  · rw [if_pos h2]
    change
      (∏ p ∈ n.factorization.support,
        T (p ^ n.factorization p)) % 3 = 2
    have hfacPos : 0 < n.factorization 2 :=
      Nat.Prime.factorization_pos_of_dvd Nat.prime_two hn h2
    have h2Mem : 2 ∈ n.factorization.support :=
      Finsupp.mem_support_iff.mpr (by omega)
    rw [← Finset.mul_prod_erase n.factorization.support
      (fun p => T (p ^ n.factorization p)) h2Mem, Nat.mul_mod]
    obtain ⟨k, hk⟩ := Nat.exists_eq_succ_of_ne_zero (by omega :
      n.factorization 2 ≠ 0)
    rw [hk, T_two_pow_succ]
    have hrest :
        (∏ p ∈ n.factorization.support.erase 2,
          T (p ^ n.factorization p)) % 3 = 1 := by
      apply prod_mod_three_eq_one
      intro p hpMem
      have hpSupport : p ∈ n.factorization.support :=
        (Finset.mem_erase.mp hpMem).2
      have hpPrimeMem : p ∈ n.primeFactors := by simpa using hpSupport
      have hp : p.Prime := Nat.prime_of_mem_primeFactors hpPrimeMem
      have hp2 : p ≠ 2 := (Finset.mem_erase.mp hpMem).1
      exact T_prime_pow_mod_three hp hp2
    rw [hrest]
  · rw [if_neg h2]
    change
      (∏ p ∈ n.factorization.support,
        T (p ^ n.factorization p)) % 3 = 1
    apply prod_mod_three_eq_one
    intro p hpMem
    have hpPrimeMem : p ∈ n.primeFactors := by simpa using hpMem
    have hp : p.Prime := Nat.prime_of_mem_primeFactors hpPrimeMem
    have hp2 : p ≠ 2 := by
      intro hpEq
      subst p
      exact h2 (Nat.mem_primeFactors.mp hpPrimeMem).2.1
    exact T_prime_pow_mod_three hp hp2

theorem T_even_no_three_mod_four {n : ℕ} (hn : n ≠ 0)
    (h2 : 2 ∣ n) (h3 : ¬3 ∣ n) :
    T n % 4 = 2 := by
  rw [T_factorization hn]
  classical
  change
    (∏ p ∈ n.factorization.support,
      T (p ^ n.factorization p)) % 4 = 2
  have hfacPos : 0 < n.factorization 2 :=
    Nat.Prime.factorization_pos_of_dvd Nat.prime_two hn h2
  have h2Mem : 2 ∈ n.factorization.support :=
    Finsupp.mem_support_iff.mpr (by omega)
  rw [← Finset.mul_prod_erase n.factorization.support
    (fun p => T (p ^ n.factorization p)) h2Mem]
  obtain ⟨k, hk⟩ := Nat.exists_eq_succ_of_ne_zero (by omega :
    n.factorization 2 ≠ 0)
  rw [hk, T_two_pow_succ]
  have hrestOdd :
      (∏ p ∈ n.factorization.support.erase 2,
        T (p ^ n.factorization p)) % 2 = 1 := by
    apply prod_mod_two_eq_one
    intro p hpMem
    have hpSupport : p ∈ n.factorization.support :=
      (Finset.mem_erase.mp hpMem).2
    have hpPrimeMem : p ∈ n.primeFactors := by simpa using hpSupport
    have hp : p.Prime := Nat.prime_of_mem_primeFactors hpPrimeMem
    have hp2 : p ≠ 2 := (Finset.mem_erase.mp hpMem).1
    have hp3 : p ≠ 3 := by
      intro hpEq
      subst p
      exact h3 (Nat.mem_primeFactors.mp hpPrimeMem).2.1
    exact Nat.odd_iff.mp (odd_T_prime_pow hp hp2 hp3)
  omega

/-- Exact characterization that refutes the positive-density conjecture. -/
theorem equality_characterization (n : ℕ) (hn : 0 < n) :
    T n = n ↔
      ∃ ε ≤ 1, ∃ m,
        n = 2 ^ ε * m ∧
        Odd m ∧
        ∀ p ∈ m.primeFactors, p % 6 = 1 := by
  have hn0 : n ≠ 0 := Nat.ne_of_gt hn
  have hT2 : T 2 = 2 := by
    simpa using (T_two_pow_succ (k := 0))
  constructor
  · intro hEq
    have h3 : ¬3 ∣ n := by
      intro h3div
      have hmod := T_mod_three_eq_one_or_two hn0
      rw [hEq] at hmod
      have hnmod : n % 3 = 0 := Nat.dvd_iff_mod_eq_zero.mp h3div
      split at hmod <;> omega
    by_cases hodd : Odd n
    · refine ⟨0, by omega, n, by simp, hodd, ?_⟩
      exact (T_odd_no_three_eq_iff hodd h3).mp hEq
    · have hevenmod : n % 2 = 0 := Nat.not_odd_iff.mp hodd
      have h2 : 2 ∣ n := Nat.dvd_iff_mod_eq_zero.mpr hevenmod
      by_cases h4 : 4 ∣ n
      · have hTmod := T_even_no_three_mod_four hn0 h2 h3
        rw [hEq] at hTmod
        have hnmod : n % 4 = 0 := Nat.dvd_iff_mod_eq_zero.mp h4
        omega
      · have hnmod4 : n % 4 = 2 := by
          rw [Nat.dvd_iff_mod_eq_zero] at h4
          have hlt := Nat.mod_lt n (by omega : 0 < 4)
          omega
        let m := n / 2
        have hnEq : n = 2 * m := by
          dsimp [m]
          omega
        have hmOdd : Odd m := by
          rw [Nat.odd_iff]
          dsimp [m]
          omega
        have hmPos : 0 < m := by
          dsimp [m]
          omega
        have h3m : ¬3 ∣ m := by
          intro h
          apply h3
          rw [hnEq]
          exact dvd_mul_of_dvd_right h 2
        have hmul := multiplicative_conclusion.2.2 hmOdd.coprime_two_left
        have hmEq : T m = m := by
          rw [← hnEq, hEq] at hmul
          rw [hT2] at hmul
          omega
        refine ⟨1, by omega, m, ?_, hmOdd, ?_⟩
        · simpa using hnEq
        · exact (T_odd_no_three_eq_iff hmOdd h3m).mp hmEq
  · rintro ⟨ε, hε, m, hnEq, hmOdd, hprimes⟩
    have hm0 : m ≠ 0 := by
      rcases hmOdd with ⟨a, ha⟩
      omega
    have h3m : ¬3 ∣ m := by
      intro h3div
      have h3Mem : 3 ∈ m.primeFactors :=
        Nat.mem_primeFactors.mpr ⟨Nat.prime_three, h3div, hm0⟩
      have := hprimes 3 h3Mem
      norm_num at this
    have hmEq : T m = m :=
      (T_odd_no_three_eq_iff hmOdd h3m).mpr hprimes
    interval_cases ε
    · simpa [hnEq] using hmEq
    · rw [pow_one] at hnEq
      rw [hnEq, multiplicative_conclusion.2.2 hmOdd.coprime_two_left,
        hT2, hmEq]

def equalitySet : Set ℕ := {n | 0 < n ∧ T n = n}

/-- The equality set has natural density zero. -/
theorem equalitySet_density_zero :
    Tendsto
      (fun N : ℕ =>
        (((equalitySet ∩ Icc 1 N).ncard : ℕ) : ℝ) / N)
      atTop (𝓝 0) := by
  apply A354766Sieve.density_zero_of_avoidsBadPrimes
  intro n hn hnPos p hp hp5 hpn
  rcases (equality_characterization n hnPos).mp hn.2 with
    ⟨ε, hε, m, hnForm, hmOdd, hmPrimes⟩
  have hpNeTwo : p ≠ 2 := by
    intro h
    subst p
    norm_num at hp5
  have hpNotPow : ¬p ∣ 2 ^ ε := by
    intro h
    have hd : p ∣ 2 := hp.dvd_of_dvd_pow h
    exact hpNeTwo ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp hd)
  have hpm : p ∣ m := by
    rw [hnForm] at hpn
    exact (hp.dvd_mul.mp hpn).resolve_left hpNotPow
  have hm0 : m ≠ 0 := by
    rcases hmOdd with ⟨a, ha⟩
    omega
  have hpMem : p ∈ m.primeFactors := Nat.mem_primeFactors.mpr ⟨hp, hpm, hm0⟩
  have hp1 := hmPrimes p hpMem
  omega

theorem A278085Primary_multiplicative : IsMultiplicative A278085Primary := by
  have h : A278085Primary = P := funext A278085Primary_eq_P
  rw [h]
  exact P_multiplicative

end A354766
