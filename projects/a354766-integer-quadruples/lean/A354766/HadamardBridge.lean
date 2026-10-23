import A354766.Bridge

/-!
# Forward and inverse Hadamard maps

This file turns the identities in `Elementary` into genuine maps and inverse
lemmas.  It does not yet perform the parity or primitive-content count.
-/

namespace A354766

@[ext] theorem quadCoords_ext {q₁ q₂ : QuadCoords}
    (hh : q₁.h = q₂.h) (hi : q₁.i = q₂.i)
    (hj : q₁.j = q₂.j) (hk : q₁.k = q₂.k) :
    q₁ = q₂ := by
  cases q₁
  cases q₂
  simp_all

def forwardTriple (q : QuadCoords) : Triple :=
  (x q, y q, z q)

def negateTriple (u : Triple) : Triple :=
  (-u.1, -u.2.1, -u.2.2)

@[simp] theorem negateTriple_fst (u : Triple) :
    (negateTriple u).1 = -u.1 := rfl

@[simp] theorem negateTriple_snd_fst (u : Triple) :
    (negateTriple u).2.1 = -u.2.1 := rfl

@[simp] theorem negateTriple_snd_snd (u : Triple) :
    (negateTriple u).2.2 = -u.2.2 := rfl

@[simp] theorem negateTriple_involutive (u : Triple) :
    negateTriple (negateTriple u) = u := by
  rcases u with ⟨x, y, z⟩
  simp [negateTriple]

theorem forwardTriple_isThreeSquare {n : ℕ} {q : QuadCoords}
    (hq : IsQuad (n : ℤ) q) :
    IsThreeSquare (3 * n ^ 2) (forwardTriple q) := by
  unfold IsThreeSquare forwardTriple
  simpa [Nat.cast_mul, Nat.cast_pow] using three_square_of_quad hq

theorem forwardTriple_injective_at_level {n : ℤ} {q₁ q₂ : QuadCoords}
    (hq₁ : IsQuad n q₁) (hq₂ : IsQuad n q₂)
    (hforward : forwardTriple q₁ = forwardTriple q₂) :
    q₁ = q₂ := by
  have hx : x q₁ = x q₂ := congrArg Prod.fst hforward
  have hy : y q₁ = y q₂ := congrArg (fun u : Triple => u.2.1) hforward
  have hz : z q₁ = z q₂ := congrArg (fun u : Triple => u.2.2) hforward
  apply quadCoords_ext
  · have h₁ := inverse_h q₁
    have h₂ := inverse_h q₂
    rw [hq₁.1, hx, hy, hz] at h₁
    rw [hq₂.1] at h₂
    linarith
  · have h₁ := inverse_i q₁
    have h₂ := inverse_i q₂
    rw [hq₁.1, hx, hy, hz] at h₁
    rw [hq₂.1] at h₂
    linarith
  · have h₁ := inverse_j q₁
    have h₂ := inverse_j q₂
    rw [hq₁.1, hx, hy, hz] at h₁
    rw [hq₂.1] at h₂
    linarith
  · have h₁ := inverse_k q₁
    have h₂ := inverse_k q₂
    rw [hq₁.1, hx, hy, hz] at h₁
    rw [hq₂.1] at h₂
    linarith

def InverseNumeratorsDivisible (n : ℤ) (u : Triple) : Prop :=
  (4 : ℤ) ∣ hNum n u.1 u.2.1 u.2.2 ∧
  (4 : ℤ) ∣ iNum n u.1 u.2.1 u.2.2 ∧
  (4 : ℤ) ∣ jNum n u.1 u.2.1 u.2.2 ∧
  (4 : ℤ) ∣ kNum n u.1 u.2.1 u.2.2

def inverseQuad (n : ℤ) (u : Triple) : QuadCoords where
  h := hNum n u.1 u.2.1 u.2.2 / 4
  i := iNum n u.1 u.2.1 u.2.2 / 4
  j := jNum n u.1 u.2.1 u.2.2 / 4
  k := kNum n u.1 u.2.1 u.2.2 / 4

theorem four_mul_inverseQuad_h {n : ℤ} {u : Triple}
    (hdiv : InverseNumeratorsDivisible n u) :
    4 * (inverseQuad n u).h = hNum n u.1 u.2.1 u.2.2 := by
  simpa [inverseQuad, mul_comm] using
    Int.ediv_mul_cancel hdiv.1

theorem four_mul_inverseQuad_i {n : ℤ} {u : Triple}
    (hdiv : InverseNumeratorsDivisible n u) :
    4 * (inverseQuad n u).i = iNum n u.1 u.2.1 u.2.2 := by
  simpa [inverseQuad, mul_comm] using
    Int.ediv_mul_cancel hdiv.2.1

theorem four_mul_inverseQuad_j {n : ℤ} {u : Triple}
    (hdiv : InverseNumeratorsDivisible n u) :
    4 * (inverseQuad n u).j = jNum n u.1 u.2.1 u.2.2 := by
  simpa [inverseQuad, mul_comm] using
    Int.ediv_mul_cancel hdiv.2.2.1

theorem four_mul_inverseQuad_k {n : ℤ} {u : Triple}
    (hdiv : InverseNumeratorsDivisible n u) :
    4 * (inverseQuad n u).k = kNum n u.1 u.2.1 u.2.2 := by
  simpa [inverseQuad, mul_comm] using
    Int.ediv_mul_cancel hdiv.2.2.2

theorem inverseQuad_sum {n : ℤ} {u : Triple}
    (hdiv : InverseNumeratorsDivisible n u) :
    (inverseQuad n u).h + (inverseQuad n u).i +
        (inverseQuad n u).j + (inverseQuad n u).k = n := by
  have hh := four_mul_inverseQuad_h hdiv
  have hi := four_mul_inverseQuad_i hdiv
  have hj := four_mul_inverseQuad_j hdiv
  have hk := four_mul_inverseQuad_k hdiv
  have hsum := numerator_sum n u.1 u.2.1 u.2.2
  linarith

theorem inverseQuad_isQuad {n : ℕ} {u : Triple}
    (hu : IsThreeSquare (3 * n ^ 2) u)
    (hdiv : InverseNumeratorsDivisible (n : ℤ) u) :
    IsQuad (n : ℤ) (inverseQuad (n : ℤ) u) := by
  refine ⟨inverseQuad_sum hdiv, ?_⟩
  have hh := four_mul_inverseQuad_h hdiv
  have hi := four_mul_inverseQuad_i hdiv
  have hj := four_mul_inverseQuad_j hdiv
  have hk := four_mul_inverseQuad_k hdiv
  have hnorm := numerator_norm (n : ℤ) u.1 u.2.1 u.2.2
  unfold IsThreeSquare at hu
  norm_num [Nat.cast_mul, Nat.cast_pow] at hu
  rw [← hh, ← hi, ← hj, ← hk] at hnorm
  ring_nf at hnorm
  nlinarith

theorem forwardTriple_inverseQuad {n : ℤ} {u : Triple}
    (hdiv : InverseNumeratorsDivisible n u) :
    forwardTriple (inverseQuad n u) = u := by
  rcases u with ⟨x₀, y₀, z₀⟩
  apply Prod.ext
  · have hh := four_mul_inverseQuad_h hdiv
    have hi := four_mul_inverseQuad_i hdiv
    have hj := four_mul_inverseQuad_j hdiv
    have hk := four_mul_inverseQuad_k hdiv
    have hx := numerator_hadamard_x n x₀ y₀ z₀
    simp only [forwardTriple, x]
    dsimp only at hh hi hj hk
    linarith
  · apply Prod.ext
    · have hh := four_mul_inverseQuad_h hdiv
      have hi := four_mul_inverseQuad_i hdiv
      have hj := four_mul_inverseQuad_j hdiv
      have hk := four_mul_inverseQuad_k hdiv
      have hy := numerator_hadamard_y n x₀ y₀ z₀
      simp only [forwardTriple, y]
      dsimp only at hh hi hj hk
      linarith
    · have hh := four_mul_inverseQuad_h hdiv
      have hi := four_mul_inverseQuad_i hdiv
      have hj := four_mul_inverseQuad_j hdiv
      have hk := four_mul_inverseQuad_k hdiv
      have hz := numerator_hadamard_z n x₀ y₀ z₀
      simp only [forwardTriple, z]
      dsimp only at hh hi hj hk
      linarith

theorem inverseNumeratorsDivisible_forwardTriple {n : ℤ} {q : QuadCoords}
    (hq : IsQuad n q) :
    InverseNumeratorsDivisible n (forwardTriple q) := by
  have hh := inverse_h q
  have hi := inverse_i q
  have hj := inverse_j q
  have hk := inverse_k q
  rw [hq.1] at hh hi hj hk
  refine ⟨?_, ?_, ?_, ?_⟩
  · exact ⟨q.h, by simpa [forwardTriple, hNum, mul_comm] using hh⟩
  · exact ⟨q.i, by simpa [forwardTriple, iNum, mul_comm] using hi⟩
  · exact ⟨q.j, by simpa [forwardTriple, jNum, mul_comm] using hj⟩
  · exact ⟨q.k, by simpa [forwardTriple, kNum, mul_comm] using hk⟩

theorem inverseQuad_forwardTriple {n : ℤ} {q : QuadCoords}
    (hq : IsQuad n q) :
    inverseQuad n (forwardTriple q) = q := by
  have hdiv := inverseNumeratorsDivisible_forwardTriple hq
  apply quadCoords_ext
  · have hh := four_mul_inverseQuad_h hdiv
    have hh' := inverse_h q
    rw [hq.1] at hh'
    dsimp [forwardTriple, hNum] at hh
    apply mul_left_cancel₀ (by norm_num : (4 : ℤ) ≠ 0)
    exact hh.trans hh'
  · have hi := four_mul_inverseQuad_i hdiv
    have hi' := inverse_i q
    rw [hq.1] at hi'
    dsimp [forwardTriple, iNum] at hi
    apply mul_left_cancel₀ (by norm_num : (4 : ℤ) ≠ 0)
    exact hi.trans hi'
  · have hj := four_mul_inverseQuad_j hdiv
    have hj' := inverse_j q
    rw [hq.1] at hj'
    dsimp [forwardTriple, jNum] at hj
    apply mul_left_cancel₀ (by norm_num : (4 : ℤ) ≠ 0)
    exact hj.trans hj'
  · have hk := four_mul_inverseQuad_k hdiv
    have hk' := inverse_k q
    rw [hq.1] at hk'
    dsimp [forwardTriple, kNum] at hk
    apply mul_left_cancel₀ (by norm_num : (4 : ℤ) ≠ 0)
    exact hk.trans hk'

end A354766
