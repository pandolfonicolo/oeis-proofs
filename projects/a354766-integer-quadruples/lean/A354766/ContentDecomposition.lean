import A354766.FiniteCounts

/-!
# Content decomposition for A354766

This file develops the scaling and quotient operations needed to partition all
quads at level `n` by their (positive) content.
-/

namespace A354766

def scaleQuad (d : ℕ) (q : QuadCoords) : QuadCoords where
  h := (d : ℤ) * q.h
  i := (d : ℤ) * q.i
  j := (d : ℤ) * q.j
  k := (d : ℤ) * q.k

def divideQuad (q : QuadCoords) : QuadCoords where
  h := q.h / (quadContent q : ℤ)
  i := q.i / (quadContent q : ℤ)
  j := q.j / (quadContent q : ℤ)
  k := q.k / (quadContent q : ℤ)

@[simp] theorem scaleQuad_zero (q : QuadCoords) :
    scaleQuad 0 q = ⟨0, 0, 0, 0⟩ := by
  cases q
  simp [scaleQuad]

@[simp] theorem scaleQuad_one (q : QuadCoords) : scaleQuad 1 q = q := by
  cases q
  simp [scaleQuad]

@[simp] theorem scaleQuad_mul (a b : ℕ) (q : QuadCoords) :
    scaleQuad a (scaleQuad b q) = scaleQuad (a * b) q := by
  cases q
  simp [scaleQuad, mul_assoc]

theorem scaleQuad_injective {d : ℕ} (hd : 0 < d) :
    Function.Injective (scaleQuad d) := by
  have hdZ : (d : ℤ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hd)
  intro q r h
  cases q with
  | mk qh qi qj qk =>
    cases r with
    | mk rh ri rj rk =>
      simp only [scaleQuad, QuadCoords.mk.injEq] at h ⊢
      exact ⟨mul_left_cancel₀ hdZ h.1,
        mul_left_cancel₀ hdZ h.2.1,
        mul_left_cancel₀ hdZ h.2.2.1,
        mul_left_cancel₀ hdZ h.2.2.2⟩

theorem isQuad_scale {n : ℕ} {q : QuadCoords} (hq : IsQuad (n : ℤ) q) (d : ℕ) :
    IsQuad ((d * n : ℕ) : ℤ) (scaleQuad d q) := by
  rcases hq with ⟨hsum, hnorm⟩
  constructor
  · simp only [scaleQuad, Nat.cast_mul]
    push_cast
    calc
      (d : ℤ) * q.h + (d : ℤ) * q.i + (d : ℤ) * q.j + (d : ℤ) * q.k =
          (d : ℤ) * (q.h + q.i + q.j + q.k) := by ring
      _ = (d : ℤ) * n := by rw [hsum]
  · simp only [scaleQuad, Nat.cast_mul]
    push_cast
    calc
      ((d : ℤ) * q.h) ^ 2 + ((d : ℤ) * q.i) ^ 2 +
          ((d : ℤ) * q.j) ^ 2 + ((d : ℤ) * q.k) ^ 2 =
          (d : ℤ) ^ 2 * (q.h ^ 2 + q.i ^ 2 + q.j ^ 2 + q.k ^ 2) := by ring
      _ = (d : ℤ) ^ 2 * (n : ℤ) ^ 2 := by rw [hnorm]
      _ = ((d : ℤ) * n) ^ 2 := by ring

@[simp] theorem quadContent_scale (d : ℕ) (q : QuadCoords) :
    quadContent (scaleQuad d q) = d * quadContent q := by
  simp only [quadContent, scaleQuad, Int.natAbs_mul, Int.natAbs_natCast,
    Nat.gcd_mul_left]

theorem quadContent_pos_of_isQuad {n : ℕ} (hn : 0 < n) {q : QuadCoords}
    (hq : IsQuad (n : ℤ) q) :
    0 < quadContent q := by
  by_contra hnot
  have hc : quadContent q = 0 := Nat.eq_zero_of_not_pos hnot
  have hh : q.h.natAbs = 0 := by
    have := Nat.gcd_eq_zero_iff.mp hc
    exact this.1
  have hi : q.i.natAbs = 0 := by
    have := Nat.gcd_eq_zero_iff.mp hc
    exact (Nat.gcd_eq_zero_iff.mp this.2).1
  have hj : q.j.natAbs = 0 := by
    have := Nat.gcd_eq_zero_iff.mp hc
    exact (Nat.gcd_eq_zero_iff.mp (Nat.gcd_eq_zero_iff.mp this.2).2).1
  have hk : q.k.natAbs = 0 := by
    have := Nat.gcd_eq_zero_iff.mp hc
    exact (Nat.gcd_eq_zero_iff.mp (Nat.gcd_eq_zero_iff.mp this.2).2).2
  have hqzero : q = ⟨0, 0, 0, 0⟩ := by
    cases q with
    | mk qh qi qj qk =>
      simp only at hh hi hj hk
      have eh : qh = 0 := Int.natAbs_eq_zero.mp hh
      have ei : qi = 0 := Int.natAbs_eq_zero.mp hi
      have ej : qj = 0 := Int.natAbs_eq_zero.mp hj
      have ek : qk = 0 := Int.natAbs_eq_zero.mp hk
      subst qh
      subst qi
      subst qj
      subst qk
      rfl
  subst q
  have hz : (0 : ℤ) = n := by simpa [IsQuad] using hq.1
  have : n = 0 := by exact_mod_cast hz.symm
  omega

theorem quadContent_dvd_h (q : QuadCoords) : (quadContent q : ℤ) ∣ q.h := by
  rw [Int.natCast_dvd]
  exact (Nat.gcd_dvd_left _ _)

theorem quadContent_dvd_i (q : QuadCoords) : (quadContent q : ℤ) ∣ q.i := by
  rw [Int.natCast_dvd]
  exact (Nat.gcd_dvd_right _ _).trans (Nat.gcd_dvd_left _ _)

theorem quadContent_dvd_j (q : QuadCoords) : (quadContent q : ℤ) ∣ q.j := by
  rw [Int.natCast_dvd]
  exact (Nat.gcd_dvd_right _ _).trans
    ((Nat.gcd_dvd_right _ _).trans (Nat.gcd_dvd_left _ _))

theorem quadContent_dvd_k (q : QuadCoords) : (quadContent q : ℤ) ∣ q.k := by
  rw [Int.natCast_dvd]
  exact (Nat.gcd_dvd_right _ _).trans
    ((Nat.gcd_dvd_right _ _).trans (Nat.gcd_dvd_right _ _))

theorem quadContent_dvd_level {n : ℕ} {q : QuadCoords} (hq : IsQuad (n : ℤ) q) :
    quadContent q ∣ n := by
  have hz : (quadContent q : ℤ) ∣ (n : ℤ) := by
    rw [← hq.1]
    exact dvd_add (dvd_add (dvd_add (quadContent_dvd_h q) (quadContent_dvd_i q))
      (quadContent_dvd_j q)) (quadContent_dvd_k q)
  exact_mod_cast hz

theorem isQuad_of_scale {d m : ℕ} (hd : 0 < d) {q : QuadCoords}
    (hq : IsQuad ((d * m : ℕ) : ℤ) (scaleQuad d q)) :
    IsQuad (m : ℤ) q := by
  have hdZ : (d : ℤ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hd)
  rcases hq with ⟨hsum, hnorm⟩
  constructor
  · apply mul_left_cancel₀ hdZ
    calc
      (d : ℤ) * (q.h + q.i + q.j + q.k) =
          (scaleQuad d q).h + (scaleQuad d q).i +
            (scaleQuad d q).j + (scaleQuad d q).k := by
              simp only [scaleQuad]
              ring
      _ = ((d * m : ℕ) : ℤ) := hsum
      _ = (d : ℤ) * (m : ℤ) := by push_cast; rfl
  · apply mul_left_cancel₀ (pow_ne_zero 2 hdZ)
    calc
      (d : ℤ) ^ 2 * (q.h ^ 2 + q.i ^ 2 + q.j ^ 2 + q.k ^ 2) =
          (scaleQuad d q).h ^ 2 + (scaleQuad d q).i ^ 2 +
            (scaleQuad d q).j ^ 2 + (scaleQuad d q).k ^ 2 := by
              simp only [scaleQuad]
              ring
      _ = ((d * m : ℕ) : ℤ) ^ 2 := hnorm
      _ = (d : ℤ) ^ 2 * (m : ℤ) ^ 2 := by push_cast; ring

theorem scaleQuad_divideQuad {n : ℕ} (hn : 0 < n) {q : QuadCoords}
    (hq : IsQuad (n : ℤ) q) :
    scaleQuad (quadContent q) (divideQuad q) = q := by
  have hh := quadContent_dvd_h q
  have hi := quadContent_dvd_i q
  have hj := quadContent_dvd_j q
  have hk := quadContent_dvd_k q
  cases q with
  | mk h i j k =>
    simp only [scaleQuad, divideQuad, QuadCoords.mk.injEq]
    constructor
    · rw [mul_comm]
      exact Int.ediv_mul_cancel hh
    · constructor
      · rw [mul_comm]
        exact Int.ediv_mul_cancel hi
      · constructor
        · rw [mul_comm]
          exact Int.ediv_mul_cancel hj
        · rw [mul_comm]
          exact Int.ediv_mul_cancel hk

theorem divideQuad_isQuad {n : ℕ} (hn : 0 < n) {q : QuadCoords}
    (hq : IsQuad (n : ℤ) q) :
    IsQuad ((n / quadContent q : ℕ) : ℤ) (divideQuad q) := by
  have hcpos := quadContent_pos_of_isQuad hn hq
  have hcd := quadContent_dvd_level hq
  apply isQuad_of_scale hcpos
  have hlevel : quadContent q * (n / quadContent q) = n :=
    Nat.mul_div_cancel' hcd
  rw [hlevel, scaleQuad_divideQuad hn hq]
  exact hq

theorem divideQuad_primitive {n : ℕ} (hn : 0 < n) {q : QuadCoords}
    (hq : IsQuad (n : ℤ) q) :
    quadContent (divideQuad q) = 1 := by
  have hcpos := quadContent_pos_of_isQuad hn hq
  have heq := congrArg quadContent (scaleQuad_divideQuad hn hq)
  rw [quadContent_scale] at heq
  apply mul_left_cancel₀ (Nat.ne_of_gt hcpos)
  simpa using heq

def quadContentFinset (n d : ℕ) : Finset QuadCoords :=
  (quadFinset n).filter fun q => quadContent q = d

@[simp] theorem mem_quadContentFinset {n d : ℕ} {q : QuadCoords} :
    q ∈ quadContentFinset n d ↔ IsQuad (n : ℤ) q ∧ quadContent q = d := by
  simp [quadContentFinset]

theorem card_quadContentFinset {n d : ℕ} (hn : 0 < n) (hdvd : d ∣ n) :
    (quadContentFinset n d).card = pqFinite (n / d) := by
  have hdpos : 0 < d := Nat.pos_of_dvd_of_pos hdvd hn
  symm
  apply Finset.card_bij'
      (fun q _ => scaleQuad d q)
      (fun q _ => divideQuad q)
  · intro q hq
    rw [mem_quadContentFinset]
    rw [mem_primitiveQuadFinset] at hq
    constructor
    · rw [← Nat.mul_div_cancel' hdvd]
      exact isQuad_scale hq.1 d
    · simpa [hq.2] using quadContent_scale d q
  · intro q hq
    rw [mem_primitiveQuadFinset]
    rw [mem_quadContentFinset] at hq
    constructor
    · simpa [hq.2] using divideQuad_isQuad hn hq.1
    · exact divideQuad_primitive hn hq.1
  · intro q hq
    rw [mem_primitiveQuadFinset] at hq
    apply scaleQuad_injective hdpos
    have hs : IsQuad (n : ℤ) (scaleQuad d q) := by
      rw [← Nat.mul_div_cancel' hdvd]
      exact isQuad_scale hq.1 d
    simpa [hq.2] using scaleQuad_divideQuad hn hs
  · intro q hq
    rw [mem_quadContentFinset] at hq
    simpa [hq.2] using scaleQuad_divideQuad hn hq.1

theorem tqFinite_eq_sum_pqFinite (n : ℕ) (hn : 0 < n) :
    tqFinite n = ∑ d ∈ n.divisors, pqFinite d := by
  unfold tqFinite
  calc
    (quadFinset n).card =
        ∑ d ∈ n.divisors, ((quadFinset n).filter fun q => quadContent q = d).card := by
      apply Finset.card_eq_sum_card_fiberwise
      intro q hq
      rw [Finset.mem_coe, Nat.mem_divisors]
      exact ⟨quadContent_dvd_level (mem_quadFinset.mp hq), hn.ne'⟩
    _ = ∑ d ∈ n.divisors, pqFinite (n / d) := by
      apply Finset.sum_congr rfl
      intro d hd
      change (quadContentFinset n d).card = pqFinite (n / d)
      exact card_quadContentFinset hn (Nat.dvd_of_mem_divisors hd)
    _ = ∑ d ∈ n.divisors, pqFinite d := by
      rw [Nat.sum_div_divisors]

end A354766
