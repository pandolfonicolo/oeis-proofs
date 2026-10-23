import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.Convert
import Mathlib.Algebra.Ring.Parity
import Mathlib.Algebra.Ring.Int.Parity
import Mathlib.Data.Nat.Factorization.Basic
import Mathlib.NumberTheory.Divisors
import Mathlib.Data.Set.Card

/-!
# OEIS A354766: elementary Hadamard layer

This file formalizes the exact algebraic transformation used in the proposed
proof. It intentionally contains no proof placeholders.

Compilation status: checked against Lean/Mathlib v4.27.0 on 2026-07-23.
-/

namespace A354766

structure QuadCoords where
  h : ℤ
  i : ℤ
  j : ℤ
  k : ℤ
deriving DecidableEq

def IsQuad (n : ℤ) (q : QuadCoords) : Prop :=
  q.h + q.i + q.j + q.k = n ∧
    q.h ^ 2 + q.i ^ 2 + q.j ^ 2 + q.k ^ 2 = n ^ 2

def x (q : QuadCoords) : ℤ := q.h + q.i - q.j - q.k
def y (q : QuadCoords) : ℤ := q.h - q.i + q.j - q.k
def z (q : QuadCoords) : ℤ := q.h - q.i - q.j + q.k

theorem hadamard_identity (q : QuadCoords) :
    x q ^ 2 + y q ^ 2 + z q ^ 2 + (q.h + q.i + q.j + q.k) ^ 2 =
      4 * (q.h ^ 2 + q.i ^ 2 + q.j ^ 2 + q.k ^ 2) := by
  simp only [x, y, z]
  ring

theorem three_square_of_quad {n : ℤ} {q : QuadCoords} (hq : IsQuad n q) :
    x q ^ 2 + y q ^ 2 + z q ^ 2 = 3 * n ^ 2 := by
  rcases hq with ⟨hsum, hsq⟩
  have h := hadamard_identity q
  rw [hsum, hsq] at h
  nlinarith

theorem inverse_h (q : QuadCoords) :
    (q.h + q.i + q.j + q.k) + x q + y q + z q = 4 * q.h := by
  simp only [x, y, z]
  ring

theorem inverse_i (q : QuadCoords) :
    (q.h + q.i + q.j + q.k) + x q - y q - z q = 4 * q.i := by
  simp only [x, y, z]
  ring

theorem inverse_j (q : QuadCoords) :
    (q.h + q.i + q.j + q.k) - x q + y q - z q = 4 * q.j := by
  simp only [x, y, z]
  ring

theorem inverse_k (q : QuadCoords) :
    (q.h + q.i + q.j + q.k) - x q - y q + z q = 4 * q.k := by
  simp only [x, y, z]
  ring

def hNum (n x y z : ℤ) : ℤ := n + x + y + z
def iNum (n x y z : ℤ) : ℤ := n + x - y - z
def jNum (n x y z : ℤ) : ℤ := n - x + y - z
def kNum (n x y z : ℤ) : ℤ := n - x - y + z

theorem numerator_sum (n x y z : ℤ) :
    hNum n x y z + iNum n x y z + jNum n x y z + kNum n x y z = 4 * n := by
  simp only [hNum, iNum, jNum, kNum]
  ring

theorem numerator_hadamard_x (n x y z : ℤ) :
    hNum n x y z + iNum n x y z - jNum n x y z - kNum n x y z = 4 * x := by
  simp only [hNum, iNum, jNum, kNum]
  ring

theorem numerator_hadamard_y (n x y z : ℤ) :
    hNum n x y z - iNum n x y z + jNum n x y z - kNum n x y z = 4 * y := by
  simp only [hNum, iNum, jNum, kNum]
  ring

theorem numerator_hadamard_z (n x y z : ℤ) :
    hNum n x y z - iNum n x y z - jNum n x y z + kNum n x y z = 4 * z := by
  simp only [hNum, iNum, jNum, kNum]
  ring

theorem numerator_norm (n x y z : ℤ) :
    hNum n x y z ^ 2 + iNum n x y z ^ 2 +
        jNum n x y z ^ 2 + kNum n x y z ^ 2 =
      4 * (n ^ 2 + x ^ 2 + y ^ 2 + z ^ 2) := by
  simp only [hNum, iNum, jNum, kNum]
  ring

end A354766
