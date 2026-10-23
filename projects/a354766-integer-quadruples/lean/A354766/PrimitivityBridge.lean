import A354766.OddCountingBridge
import Mathlib.RingTheory.Int.Basic

/-!
# Primitivity across the odd-level Hadamard map

The main lemma works prime by prime.  A common prime divisor of the transformed
triple divides the level, and then the inverse Hadamard identities force it to
divide all four quad coordinates.
-/

namespace A354766

theorem prime_ne_two_of_dvd_odd_int {p : ℕ} {a : ℤ}
    (hp : p.Prime) (ha : Odd a) (hpa : (p : ℤ) ∣ a) :
    p ≠ 2 := by
  intro hp2
  subst p
  exact (Int.not_even_iff_odd.mpr ha) (even_iff_two_dvd.mpr hpa)

theorem prime_dvd_level_of_dvd_three_square_coordinates
    {p n : ℕ} {u : Triple}
    (hp : p.Prime)
    (hu : IsThreeSquare (3 * n ^ 2) u)
    (hpx : (p : ℤ) ∣ u.1)
    (hpy : (p : ℤ) ∣ u.2.1)
    (hpz : (p : ℤ) ∣ u.2.2) :
    (p : ℤ) ∣ (n : ℤ) := by
  have hpx2 : (p : ℤ) ^ 2 ∣ u.1 ^ 2 := pow_dvd_pow_of_dvd hpx 2
  have hpy2 : (p : ℤ) ^ 2 ∣ u.2.1 ^ 2 := pow_dvd_pow_of_dvd hpy 2
  have hpz2 : (p : ℤ) ^ 2 ∣ u.2.2 ^ 2 := pow_dvd_pow_of_dvd hpz 2
  have hu' := hu
  unfold IsThreeSquare at hu'
  norm_num [Nat.cast_mul, Nat.cast_pow] at hu'
  have hpSq :
      (p : ℤ) ^ 2 ∣ 3 * (n : ℤ) ^ 2 := by
    rw [← hu']
    exact dvd_add (dvd_add hpx2 hpy2) hpz2
  have hpOne : (p : ℤ) ∣ 3 * (n : ℤ) ^ 2 :=
    dvd_trans (dvd_pow_self (p : ℤ) (by decide)) hpSq
  rcases Int.Prime.dvd_mul' hp hpOne with hp3 | hpnSq
  · have hpNat3 : p ∣ 3 := by
      simpa using (Int.natCast_dvd.mp hp3)
    have hpeq3 : p = 3 :=
      (Nat.dvd_prime Nat.prime_three).mp hpNat3 |>.resolve_left hp.ne_one
    subst p
    obtain ⟨c, hc⟩ := hpSq
    have hcancel :
        (3 : ℤ) * (n : ℤ) ^ 2 = 3 * (3 * c) := by
      calc
        (3 : ℤ) * (n : ℤ) ^ 2 = (3 : ℤ) ^ 2 * c := hc
        _ = 3 * (3 * c) := by ring
    have hnSq : (3 : ℤ) ∣ (n : ℤ) ^ 2 := by
      refine ⟨c, ?_⟩
      exact mul_left_cancel₀ (by norm_num : (3 : ℤ) ≠ 0) hcancel
    exact Int.Prime.dvd_pow' Nat.prime_three hnSq
  · exact Int.Prime.dvd_pow' hp hpnSq

theorem prime_dvd_four_implies_eq_two {p : ℕ}
    (hp : p.Prime) (hp4 : (p : ℤ) ∣ 4) :
    p = 2 := by
  have hp4Nat : p ∣ 4 := (Int.natCast_dvd.mp hp4)
  have hp2 : p ∣ 2 := by
    apply hp.dvd_of_dvd_pow
    have hfour : 4 = 2 ^ 2 := by norm_num
    rwa [← hfour]
  exact (Nat.dvd_prime Nat.prime_two).mp hp2 |>.resolve_left hp.ne_one

theorem prime_dvd_quad_coordinates_of_dvd_forward
    {p n : ℕ} {q : QuadCoords}
    (hp : p.Prime) (hn : Odd n)
    (hq : IsQuad (n : ℤ) q)
    (hpx : (p : ℤ) ∣ x q)
    (hpy : (p : ℤ) ∣ y q)
    (hpz : (p : ℤ) ∣ z q) :
    (p : ℤ) ∣ q.h ∧ (p : ℤ) ∣ q.i ∧
      (p : ℤ) ∣ q.j ∧ (p : ℤ) ∣ q.k := by
  have hu : IsThreeSquare (3 * n ^ 2) (forwardTriple q) :=
    forwardTriple_isThreeSquare hq
  have hpn := prime_dvd_level_of_dvd_three_square_coordinates
    hp hu hpx hpy hpz
  have hodd := odd_threeSquare_coordinates hn hu
  have hpne2 := prime_ne_two_of_dvd_odd_int hp hodd.1 hpx
  have hdvdCoord (a : ℤ) (ha : (p : ℤ) ∣ 4 * a) :
      (p : ℤ) ∣ a := by
    rcases Int.Prime.dvd_mul' hp ha with hp4 | hpa
    · exact (hpne2 (prime_dvd_four_implies_eq_two hp hp4)).elim
    · exact hpa
  have hhEq := inverse_h q
  have hiEq := inverse_i q
  have hjEq := inverse_j q
  have hkEq := inverse_k q
  rw [hq.1] at hhEq hiEq hjEq hkEq
  refine ⟨hdvdCoord q.h ?_, hdvdCoord q.i ?_,
    hdvdCoord q.j ?_, hdvdCoord q.k ?_⟩
  · rw [← hhEq]
    exact dvd_add (dvd_add (dvd_add hpn hpx) hpy) hpz
  · rw [← hiEq]
    exact dvd_sub (dvd_sub (dvd_add hpn hpx) hpy) hpz
  · rw [← hjEq]
    exact dvd_sub (dvd_add (dvd_sub hpn hpx) hpy) hpz
  · rw [← hkEq]
    exact dvd_add (dvd_sub (dvd_sub hpn hpx) hpy) hpz

theorem quadContent_eq_one_iff_forward_tripleContent_eq_one
    {n : ℕ} {q : QuadCoords} (hn : Odd n)
    (hq : IsQuad (n : ℤ) q) :
    quadContent q = 1 ↔ tripleContent (forwardTriple q) = 1 := by
  constructor
  · intro hqPrimitive
    apply Nat.eq_one_iff_not_exists_prime_dvd.mpr
    intro p hp hpTriple
    have hpCoords :
        p ∣ (x q).natAbs ∧ p ∣ (y q).natAbs ∧ p ∣ (z q).natAbs := by
      have hpYZ : p ∣ Nat.gcd (y q).natAbs (z q).natAbs :=
        hpTriple.trans (Nat.gcd_dvd_right _ _)
      exact ⟨hpTriple.trans (Nat.gcd_dvd_left _ _),
        hpYZ.trans (Nat.gcd_dvd_left _ _),
        hpYZ.trans (Nat.gcd_dvd_right _ _)⟩
    have hpCoordsInt :
        (p : ℤ) ∣ x q ∧ (p : ℤ) ∣ y q ∧ (p : ℤ) ∣ z q := by
      simpa [Int.natCast_dvd] using hpCoords
    have hpQuad := prime_dvd_quad_coordinates_of_dvd_forward
      hp hn hq hpCoordsInt.1 hpCoordsInt.2.1 hpCoordsInt.2.2
    have hpQuadNat :
        p ∣ q.h.natAbs ∧ p ∣ q.i.natAbs ∧
          p ∣ q.j.natAbs ∧ p ∣ q.k.natAbs := by
      simpa [Int.natCast_dvd] using hpQuad
    have : p ∣ quadContent q := by
      exact Nat.dvd_gcd hpQuadNat.1
        (Nat.dvd_gcd hpQuadNat.2.1
          (Nat.dvd_gcd hpQuadNat.2.2.1 hpQuadNat.2.2.2))
    rw [hqPrimitive] at this
    exact hp.not_dvd_one this
  · intro htriplePrimitive
    apply Nat.eq_one_iff_not_exists_prime_dvd.mpr
    intro p hp hpQuad
    have hpQuadCoords :
        p ∣ q.h.natAbs ∧ p ∣ q.i.natAbs ∧
          p ∣ q.j.natAbs ∧ p ∣ q.k.natAbs := by
      have hpIJK :
          p ∣ Nat.gcd q.i.natAbs
            (Nat.gcd q.j.natAbs q.k.natAbs) :=
        hpQuad.trans (Nat.gcd_dvd_right _ _)
      have hpJK : p ∣ Nat.gcd q.j.natAbs q.k.natAbs :=
        hpIJK.trans (Nat.gcd_dvd_right _ _)
      exact ⟨hpQuad.trans (Nat.gcd_dvd_left _ _),
        hpIJK.trans (Nat.gcd_dvd_left _ _),
        hpJK.trans (Nat.gcd_dvd_left _ _),
        hpJK.trans (Nat.gcd_dvd_right _ _)⟩
    have hpQuadInt :
        (p : ℤ) ∣ q.h ∧ (p : ℤ) ∣ q.i ∧
          (p : ℤ) ∣ q.j ∧ (p : ℤ) ∣ q.k := by
      simpa [Int.natCast_dvd] using hpQuadCoords
    have hpx : (p : ℤ) ∣ x q := by
      exact dvd_sub (dvd_sub (dvd_add hpQuadInt.1 hpQuadInt.2.1)
        hpQuadInt.2.2.1) hpQuadInt.2.2.2
    have hpy : (p : ℤ) ∣ y q := by
      exact dvd_sub (dvd_add (dvd_sub hpQuadInt.1 hpQuadInt.2.1)
        hpQuadInt.2.2.1) hpQuadInt.2.2.2
    have hpz : (p : ℤ) ∣ z q := by
      exact dvd_add (dvd_sub (dvd_sub hpQuadInt.1 hpQuadInt.2.1)
        hpQuadInt.2.2.1) hpQuadInt.2.2.2
    have hpTriple : p ∣ tripleContent (forwardTriple q) := by
      have hpTripleNat :
          p ∣ (x q).natAbs ∧ p ∣ (y q).natAbs ∧
            p ∣ (z q).natAbs := by
        simpa [Int.natCast_dvd] using And.intro hpx (And.intro hpy hpz)
      exact Nat.dvd_gcd hpTripleNat.1
        (Nat.dvd_gcd hpTripleNat.2.1 hpTripleNat.2.2)
    rw [htriplePrimitive] at hpTriple
    exact hp.not_dvd_one hpTriple

end A354766
