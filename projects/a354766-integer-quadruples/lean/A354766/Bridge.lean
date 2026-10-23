import A354766.FiniteCounts
import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic.DeriveFintype

/-!
# Parity and content lemmas for the Hadamard bridge

The key local obstruction is modulo eight: if four integer squares sum to the
square of a multiple of four, then all four integers are even.  The finite
`ZMod 8` lemma below checks exactly the 4096 possible residue quadruples; the
remaining lemmas lift that closed modular fact back to integers and to the
quad content.
-/

namespace A354766

inductive SquareResidue8
  | zero
  | one
  | four
  deriving DecidableEq, Fintype

def SquareResidue8.value : SquareResidue8 → ZMod 8
  | .zero => 0
  | .one => 1
  | .four => 4

def SquareResidue8.parity : SquareResidue8 → ZMod 2
  | .zero => 0
  | .one => 1
  | .four => 0

/-- Every square modulo eight has one of three residues, which also records
the parity of its square root. -/
theorem zmod8_square_class :
    ∀ a : ZMod 8, ∃ r : SquareResidue8,
      a ^ 2 = r.value ∧
      ZMod.castHom (by decide : 2 ∣ 8) (ZMod 2) a = r.parity := by
  decide

/-- Among four square residues, a zero sum modulo eight contains no odd
square.  This is the 81-case finite core of the congruence argument. -/
theorem squareResidue8_sum_zero :
    ∀ a b c d : SquareResidue8,
      a.value + b.value + c.value + d.value = 0 →
        a.parity = 0 ∧ b.parity = 0 ∧ c.parity = 0 ∧ d.parity = 0 := by
  decide

/-- A sum of four squares that vanishes modulo eight has even coordinates. -/
theorem zmod8_sum_four_squares_even
    (a b c d : ZMod 8)
    (hsum : a ^ 2 + b ^ 2 + c ^ 2 + d ^ 2 = 0) :
    ZMod.castHom (by decide : 2 ∣ 8) (ZMod 2) a = 0 ∧
    ZMod.castHom (by decide : 2 ∣ 8) (ZMod 2) b = 0 ∧
    ZMod.castHom (by decide : 2 ∣ 8) (ZMod 2) c = 0 ∧
    ZMod.castHom (by decide : 2 ∣ 8) (ZMod 2) d = 0 := by
  obtain ⟨ra, haSq, haParity⟩ := zmod8_square_class a
  obtain ⟨rb, hbSq, hbParity⟩ := zmod8_square_class b
  obtain ⟨rc, hcSq, hcParity⟩ := zmod8_square_class c
  obtain ⟨rd, hdSq, hdParity⟩ := zmod8_square_class d
  have hr :
      ra.value + rb.value + rc.value + rd.value = 0 := by
    simpa [haSq, hbSq, hcSq, hdSq] using hsum
  have hp := squareResidue8_sum_zero ra rb rc rd hr
  simpa [haParity, hbParity, hcParity, hdParity] using hp

theorem zmod8_four_mul_sq_zero :
    ∀ a : ZMod 8, (4 * a) ^ 2 = 0 := by
  decide

/-- If the norm of four integers is the square of a multiple of four, every
coordinate is even. -/
theorem even_coordinates_of_norm_eq_sq_of_four_dvd
    {n h i j k : ℤ} (hn : (4 : ℤ) ∣ n)
    (hnorm : h ^ 2 + i ^ 2 + j ^ 2 + k ^ 2 = n ^ 2) :
    Even h ∧ Even i ∧ Even j ∧ Even k := by
  obtain ⟨m, rfl⟩ := hn
  have hmod8 :
      (h : ZMod 8) ^ 2 + (i : ZMod 8) ^ 2 +
          (j : ZMod 8) ^ 2 + (k : ZMod 8) ^ 2 = 0 := by
    have hc := congrArg (Int.castRingHom (ZMod 8)) hnorm
    norm_num at hc
    calc
      (h : ZMod 8) ^ 2 + (i : ZMod 8) ^ 2 +
          (j : ZMod 8) ^ 2 + (k : ZMod 8) ^ 2 =
          (4 * (m : ZMod 8)) ^ 2 := by simpa using hc
      _ = 0 := zmod8_four_mul_sq_zero (m : ZMod 8)
  have he := zmod8_sum_four_squares_even
    (h : ZMod 8) (i : ZMod 8) (j : ZMod 8) (k : ZMod 8) hmod8
  simpa [ZMod.intCast_eq_zero_iff_even] using he

/-- A quad at a level divisible by four cannot have content one. -/
theorem quadContent_ne_one_of_four_dvd
    {n : ℕ} {q : QuadCoords} (hn : 4 ∣ n) (hq : IsQuad (n : ℤ) q) :
    quadContent q ≠ 1 := by
  have hnInt : (4 : ℤ) ∣ (n : ℤ) := by
    exact_mod_cast hn
  have he := even_coordinates_of_norm_eq_sq_of_four_dvd hnInt hq.2
  have hh : 2 ∣ q.h.natAbs :=
    even_iff_two_dvd.mp (Int.natAbs_even.mpr he.1)
  have hi : 2 ∣ q.i.natAbs :=
    even_iff_two_dvd.mp (Int.natAbs_even.mpr he.2.1)
  have hj : 2 ∣ q.j.natAbs :=
    even_iff_two_dvd.mp (Int.natAbs_even.mpr he.2.2.1)
  have hk : 2 ∣ q.k.natAbs :=
    even_iff_two_dvd.mp (Int.natAbs_even.mpr he.2.2.2)
  have hdiv : 2 ∣ quadContent q := by
    exact Nat.dvd_gcd hh (Nat.dvd_gcd hi (Nat.dvd_gcd hj hk))
  intro hcontent
  rw [hcontent] at hdiv
  norm_num at hdiv

/-- The primitive quad search is empty at every level divisible by four. -/
theorem primitiveQuadFinset_eq_empty_of_four_dvd
    {n : ℕ} (hn : 4 ∣ n) :
    primitiveQuadFinset n = ∅ := by
  apply Finset.eq_empty_iff_forall_notMem.mpr
  intro q hq
  rw [mem_primitiveQuadFinset] at hq
  exact quadContent_ne_one_of_four_dvd hn hq.1 hq.2

/-- Consequently the exact primitive quad count vanishes when `4 ∣ n`. -/
theorem pqFinite_eq_zero_of_four_dvd {n : ℕ} (hn : 4 ∣ n) :
    pqFinite n = 0 := by
  simp [pqFinite, primitiveQuadFinset_eq_empty_of_four_dvd hn]

end A354766
