import A354766.Elementary
import Mathlib.Data.Int.Interval
import Mathlib.Algebra.Order.Ring.Abs

/-!
# Finite counting models for OEIS A354766

This file replaces noncomputable `Set.ncard` definitions by explicit finite
search spaces.  The bounds are deliberately loose: every coordinate in a quad
for `n` has absolute value at most `n`, and every coordinate in a three-square
representation of `N` has absolute value at most `N`.
-/

namespace A354766

instance (n : ℤ) (q : QuadCoords) : Decidable (IsQuad n q) := by
  unfold IsQuad
  infer_instance

def intInterval (B : ℕ) : Finset ℤ :=
  Finset.Icc (-(B : ℤ)) (B : ℤ)

def quadSearchSpace (n : ℕ) : Finset QuadCoords :=
  (((intInterval n).product (intInterval n)).product
      ((intInterval n).product (intInterval n))).image
    fun u =>
      { h := u.1.1
        i := u.1.2
        j := u.2.1
        k := u.2.2 }

def quadFinset (n : ℕ) : Finset QuadCoords :=
  (quadSearchSpace n).filter (IsQuad (n : ℤ))

def quadContent (q : QuadCoords) : ℕ :=
  Nat.gcd q.h.natAbs
    (Nat.gcd q.i.natAbs (Nat.gcd q.j.natAbs q.k.natAbs))

def primitiveQuadFinset (n : ℕ) : Finset QuadCoords :=
  (quadFinset n).filter fun q => quadContent q = 1

abbrev Triple := ℤ × ℤ × ℤ

def tripleSearchSpace (N : ℕ) : Finset Triple :=
  (intInterval N).product ((intInterval N).product (intInterval N))

def IsThreeSquare (N : ℕ) (u : Triple) : Prop :=
  u.1 ^ 2 + u.2.1 ^ 2 + u.2.2 ^ 2 = (N : ℤ)

instance (N : ℕ) (u : Triple) : Decidable (IsThreeSquare N u) := by
  unfold IsThreeSquare
  infer_instance

def tripleContent (u : Triple) : ℕ :=
  Nat.gcd u.1.natAbs (Nat.gcd u.2.1.natAbs u.2.2.natAbs)

def threeSquareFinset (N : ℕ) : Finset Triple :=
  (tripleSearchSpace N).filter (IsThreeSquare N)

def primitiveThreeSquareFinset (N : ℕ) : Finset Triple :=
  (threeSquareFinset N).filter fun u => tripleContent u = 1

def tqFinite (n : ℕ) : ℕ := (quadFinset n).card
def pqFinite (n : ℕ) : ℕ := (primitiveQuadFinset n).card
def r3Finite (N : ℕ) : ℕ := (threeSquareFinset N).card
def r3PrimitiveFinite (N : ℕ) : ℕ := (primitiveThreeSquareFinset N).card

@[simp] theorem mem_intInterval {B : ℕ} {a : ℤ} :
    a ∈ intInterval B ↔ -(B : ℤ) ≤ a ∧ a ≤ (B : ℤ) := by
  simp [intInterval]

theorem quad_mem_searchSpace_of_isQuad {n : ℕ} {q : QuadCoords}
    (hq : IsQuad (n : ℤ) q) :
    q ∈ quadSearchSpace n := by
  have hhSq : q.h ^ 2 ≤ (n : ℤ) ^ 2 := by
    rcases hq with ⟨_, hnorm⟩
    nlinarith [sq_nonneg q.i, sq_nonneg q.j, sq_nonneg q.k]
  have hiSq : q.i ^ 2 ≤ (n : ℤ) ^ 2 := by
    rcases hq with ⟨_, hnorm⟩
    nlinarith [sq_nonneg q.h, sq_nonneg q.j, sq_nonneg q.k]
  have hjSq : q.j ^ 2 ≤ (n : ℤ) ^ 2 := by
    rcases hq with ⟨_, hnorm⟩
    nlinarith [sq_nonneg q.h, sq_nonneg q.i, sq_nonneg q.k]
  have hkSq : q.k ^ 2 ≤ (n : ℤ) ^ 2 := by
    rcases hq with ⟨_, hnorm⟩
    nlinarith [sq_nonneg q.h, sq_nonneg q.i, sq_nonneg q.j]
  have hh := abs_le_of_sq_le_sq' hhSq (by positivity : (0 : ℤ) ≤ n)
  have hi := abs_le_of_sq_le_sq' hiSq (by positivity : (0 : ℤ) ≤ n)
  have hj := abs_le_of_sq_le_sq' hjSq (by positivity : (0 : ℤ) ≤ n)
  have hk := abs_le_of_sq_le_sq' hkSq (by positivity : (0 : ℤ) ≤ n)
  refine Finset.mem_image.mpr
    ⟨((q.h, q.i), (q.j, q.k)), ?_, ?_⟩
  · simp [intInterval, hh, hi, hj, hk]
  · cases q
    rfl

@[simp] theorem mem_quadFinset {n : ℕ} {q : QuadCoords} :
    q ∈ quadFinset n ↔ IsQuad (n : ℤ) q := by
  constructor
  · exact fun h => (Finset.mem_filter.mp h).2
  · intro h
    exact Finset.mem_filter.mpr ⟨quad_mem_searchSpace_of_isQuad h, h⟩

@[simp] theorem mem_primitiveQuadFinset {n : ℕ} {q : QuadCoords} :
    q ∈ primitiveQuadFinset n ↔
      IsQuad (n : ℤ) q ∧ quadContent q = 1 := by
  simp [primitiveQuadFinset]

theorem natCast_le_sq (N : ℕ) : (N : ℤ) ≤ (N : ℤ) ^ 2 := by
  by_cases hN : N = 0
  · simp [hN]
  · have hOne : (1 : ℤ) ≤ (N : ℤ) := by
      exact_mod_cast (Nat.one_le_iff_ne_zero.mpr hN)
    nlinarith [mul_nonneg (show (0 : ℤ) ≤ N by positivity) (sub_nonneg.mpr hOne)]

theorem triple_mem_searchSpace_of_isThreeSquare {N : ℕ} {u : Triple}
    (hu : IsThreeSquare N u) :
    u ∈ tripleSearchSpace N := by
  have hxSq : u.1 ^ 2 ≤ (N : ℤ) := by
    unfold IsThreeSquare at hu
    nlinarith [sq_nonneg u.2.1, sq_nonneg u.2.2]
  have hySq : u.2.1 ^ 2 ≤ (N : ℤ) := by
    unfold IsThreeSquare at hu
    nlinarith [sq_nonneg u.1, sq_nonneg u.2.2]
  have hzSq : u.2.2 ^ 2 ≤ (N : ℤ) := by
    unfold IsThreeSquare at hu
    nlinarith [sq_nonneg u.1, sq_nonneg u.2.1]
  have hN := natCast_le_sq N
  have hx := abs_le_of_sq_le_sq' (hxSq.trans hN) (by positivity : (0 : ℤ) ≤ N)
  have hy := abs_le_of_sq_le_sq' (hySq.trans hN) (by positivity : (0 : ℤ) ≤ N)
  have hz := abs_le_of_sq_le_sq' (hzSq.trans hN) (by positivity : (0 : ℤ) ≤ N)
  simp [tripleSearchSpace, intInterval, hx, hy, hz]

@[simp] theorem mem_threeSquareFinset {N : ℕ} {u : Triple} :
    u ∈ threeSquareFinset N ↔ IsThreeSquare N u := by
  constructor
  · exact fun h => (Finset.mem_filter.mp h).2
  · intro h
    exact Finset.mem_filter.mpr ⟨triple_mem_searchSpace_of_isThreeSquare h, h⟩

@[simp] theorem mem_primitiveThreeSquareFinset {N : ℕ} {u : Triple} :
    u ∈ primitiveThreeSquareFinset N ↔
      IsThreeSquare N u ∧ tripleContent u = 1 := by
  simp [primitiveThreeSquareFinset]

theorem r3PrimitiveFinite_three : r3PrimitiveFinite 3 = 8 := by
  native_decide

end A354766
