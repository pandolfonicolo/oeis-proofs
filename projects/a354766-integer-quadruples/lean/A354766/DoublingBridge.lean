import A354766.PrimitiveOddCounting

/-!
# Primitive quads at `m` and `2m` for odd `m`

For odd `m`, complementation followed by doubling gives a direct bijection
between primitive quads at levels `m` and `2m`:

`r ↦ (m - 2r.h, m - 2r.i, m - 2r.j, m - 2r.k)`.
-/

namespace A354766

/-- The mod-four parity classification for quads at twice an odd level. -/
theorem zmod4_twice_odd_quad_parity :
    ∀ m h i j k : ZMod 4,
      ZMod.castHom (by decide : 2 ∣ 4) (ZMod 2) m = 1 →
      h + i + j + k = 2 * m →
      h ^ 2 + i ^ 2 + j ^ 2 + k ^ 2 = (2 * m) ^ 2 →
      ((ZMod.castHom (by decide : 2 ∣ 4) (ZMod 2) h = 0 ∧
        ZMod.castHom (by decide : 2 ∣ 4) (ZMod 2) i = 0 ∧
        ZMod.castHom (by decide : 2 ∣ 4) (ZMod 2) j = 0 ∧
        ZMod.castHom (by decide : 2 ∣ 4) (ZMod 2) k = 0) ∨
       (ZMod.castHom (by decide : 2 ∣ 4) (ZMod 2) h = 1 ∧
        ZMod.castHom (by decide : 2 ∣ 4) (ZMod 2) i = 1 ∧
        ZMod.castHom (by decide : 2 ∣ 4) (ZMod 2) j = 1 ∧
        ZMod.castHom (by decide : 2 ∣ 4) (ZMod 2) k = 1)) := by
  decide

theorem primitive_quad_coordinates_odd_at_twice_odd
    {m : ℕ} {q : QuadCoords} (hm : Odd m)
    (hq : IsQuad (2 * (m : ℤ)) q) (hcontent : quadContent q = 1) :
    Odd q.h ∧ Odd q.i ∧ Odd q.j ∧ Odd q.k := by
  have hmInt : Odd (m : ℤ) := by exact_mod_cast hm
  have hm2 :
      ZMod.castHom (by decide : 2 ∣ 4) (ZMod 2) (m : ZMod 4) = 1 := by
    simpa using hmInt.intCast_zmod_two
  have hsum4 :
      (q.h : ZMod 4) + (q.i : ZMod 4) +
          (q.j : ZMod 4) + (q.k : ZMod 4) =
        2 * (m : ZMod 4) := by
    have hc := congrArg (Int.castRingHom (ZMod 4)) hq.1
    norm_num at hc ⊢
    simpa using hc
  have hnorm4 :
      (q.h : ZMod 4) ^ 2 + (q.i : ZMod 4) ^ 2 +
          (q.j : ZMod 4) ^ 2 + (q.k : ZMod 4) ^ 2 =
        (2 * (m : ZMod 4)) ^ 2 := by
    have hc := congrArg (Int.castRingHom (ZMod 4)) hq.2
    norm_num at hc ⊢
    simpa using hc
  have hp := zmod4_twice_odd_quad_parity
    (m : ZMod 4) (q.h : ZMod 4) (q.i : ZMod 4)
      (q.j : ZMod 4) (q.k : ZMod 4) hm2 hsum4 hnorm4
  rcases hp with heven | hodd
  · have hh : 2 ∣ q.h.natAbs :=
      even_iff_two_dvd.mp (Int.natAbs_even.mpr
        (ZMod.intCast_eq_zero_iff_even.mp (by simpa using heven.1)))
    have hi : 2 ∣ q.i.natAbs :=
      even_iff_two_dvd.mp (Int.natAbs_even.mpr
        (ZMod.intCast_eq_zero_iff_even.mp (by simpa using heven.2.1)))
    have hj : 2 ∣ q.j.natAbs :=
      even_iff_two_dvd.mp (Int.natAbs_even.mpr
        (ZMod.intCast_eq_zero_iff_even.mp (by simpa using heven.2.2.1)))
    have hk : 2 ∣ q.k.natAbs :=
      even_iff_two_dvd.mp (Int.natAbs_even.mpr
        (ZMod.intCast_eq_zero_iff_even.mp (by simpa using heven.2.2.2)))
    have htwo : 2 ∣ quadContent q :=
      Nat.dvd_gcd hh (Nat.dvd_gcd hi (Nat.dvd_gcd hj hk))
    rw [hcontent] at htwo
    norm_num at htwo
  · exact ⟨ZMod.intCast_eq_one_iff_odd.mp (by simpa using hodd.1),
      ZMod.intCast_eq_one_iff_odd.mp (by simpa using hodd.2.1),
      ZMod.intCast_eq_one_iff_odd.mp (by simpa using hodd.2.2.1),
      ZMod.intCast_eq_one_iff_odd.mp (by simpa using hodd.2.2.2)⟩

def doubleComplementQuad (m : ℤ) (q : QuadCoords) : QuadCoords where
  h := m - 2 * q.h
  i := m - 2 * q.i
  j := m - 2 * q.j
  k := m - 2 * q.k

def halfComplementQuad (m : ℤ) (q : QuadCoords) : QuadCoords where
  h := (m - q.h) / 2
  i := (m - q.i) / 2
  j := (m - q.j) / 2
  k := (m - q.k) / 2

theorem doubleComplementQuad_isQuad {m : ℕ} {q : QuadCoords}
    (hq : IsQuad (m : ℤ) q) :
    IsQuad (2 * (m : ℤ)) (doubleComplementQuad (m : ℤ) q) := by
  rcases hq with ⟨hsum, hnorm⟩
  constructor
  · simp only [doubleComplementQuad]
    linarith
  · simp only [doubleComplementQuad]
    nlinarith

theorem halfComplementQuad_twice_eq {m : ℤ} {q : QuadCoords}
    (hodd : Odd q.h ∧ Odd q.i ∧ Odd q.j ∧ Odd q.k)
    (hm : Odd m) :
    2 * (halfComplementQuad m q).h = m - q.h ∧
    2 * (halfComplementQuad m q).i = m - q.i ∧
    2 * (halfComplementQuad m q).j = m - q.j ∧
    2 * (halfComplementQuad m q).k = m - q.k := by
  have hdiv (a : ℤ) (ha : Odd a) : (2 : ℤ) ∣ m - a := by
    exact even_iff_two_dvd.mp ((Int.even_sub').mpr
      ⟨fun _ => ha, fun _ => hm⟩)
  refine ⟨?_, ?_, ?_, ?_⟩
  · simpa [halfComplementQuad, mul_comm] using
      Int.ediv_mul_cancel (hdiv q.h hodd.1)
  · simpa [halfComplementQuad, mul_comm] using
      Int.ediv_mul_cancel (hdiv q.i hodd.2.1)
  · simpa [halfComplementQuad, mul_comm] using
      Int.ediv_mul_cancel (hdiv q.j hodd.2.2.1)
  · simpa [halfComplementQuad, mul_comm] using
      Int.ediv_mul_cancel (hdiv q.k hodd.2.2.2)

theorem halfComplementQuad_isQuad {m : ℕ} {q : QuadCoords}
    (hm : Odd m) (hq : IsQuad (2 * (m : ℤ)) q)
    (hodd : Odd q.h ∧ Odd q.i ∧ Odd q.j ∧ Odd q.k) :
    IsQuad (m : ℤ) (halfComplementQuad (m : ℤ) q) := by
  have hmInt : Odd (m : ℤ) := by exact_mod_cast hm
  have htwice := halfComplementQuad_twice_eq hodd hmInt
  constructor
  · have hsum := hq.1
    simp only at htwice
    linarith
  · have hnorm := hq.2
    have hh :
        q.h = (m : ℤ) - 2 * (halfComplementQuad (m : ℤ) q).h := by
      linarith [htwice.1]
    have hi :
        q.i = (m : ℤ) - 2 * (halfComplementQuad (m : ℤ) q).i := by
      linarith [htwice.2.1]
    have hj :
        q.j = (m : ℤ) - 2 * (halfComplementQuad (m : ℤ) q).j := by
      linarith [htwice.2.2.1]
    have hk :
        q.k = (m : ℤ) - 2 * (halfComplementQuad (m : ℤ) q).k := by
      linarith [htwice.2.2.2]
    have hsumR :
        (halfComplementQuad (m : ℤ) q).h +
          (halfComplementQuad (m : ℤ) q).i +
          (halfComplementQuad (m : ℤ) q).j +
          (halfComplementQuad (m : ℤ) q).k = (m : ℤ) := by
      linarith [hq.1, htwice.1, htwice.2.1,
        htwice.2.2.1, htwice.2.2.2]
    rw [hh, hi, hj, hk] at hnorm
    ring_nf at hnorm
    have hnormR :
        (halfComplementQuad (m : ℤ) q).h ^ 2 +
            (halfComplementQuad (m : ℤ) q).i ^ 2 +
            (halfComplementQuad (m : ℤ) q).j ^ 2 +
            (halfComplementQuad (m : ℤ) q).k ^ 2 =
          (m : ℤ) *
            ((halfComplementQuad (m : ℤ) q).h +
              (halfComplementQuad (m : ℤ) q).i +
              (halfComplementQuad (m : ℤ) q).j +
              (halfComplementQuad (m : ℤ) q).k) := by
      nlinarith [hnorm]
    rw [hsumR] at hnormR
    simpa [pow_two] using hnormR

@[simp] theorem half_doubleComplementQuad {m : ℕ} {q : QuadCoords} :
    halfComplementQuad (m : ℤ)
      (doubleComplementQuad (m : ℤ) q) = q := by
  apply quadCoords_ext <;>
    simp [halfComplementQuad, doubleComplementQuad]

theorem double_halfComplementQuad {m : ℕ} {q : QuadCoords}
    (hm : Odd m)
    (hodd : Odd q.h ∧ Odd q.i ∧ Odd q.j ∧ Odd q.k) :
    doubleComplementQuad (m : ℤ)
      (halfComplementQuad (m : ℤ) q) = q := by
  have hmInt : Odd (m : ℤ) := by exact_mod_cast hm
  have htwice := halfComplementQuad_twice_eq hodd hmInt
  apply quadCoords_ext <;>
    simp only [doubleComplementQuad] <;>
    linarith

theorem doubleComplementQuad_primitive {m : ℕ} {q : QuadCoords}
    (hm : Odd m) (hq : IsQuad (m : ℤ) q) (hprimitive : quadContent q = 1) :
    quadContent (doubleComplementQuad (m : ℤ) q) = 1 := by
  apply Nat.eq_one_iff_not_exists_prime_dvd.mpr
  intro p hp hpContent
  have hpCoords :
      p ∣ (doubleComplementQuad (m : ℤ) q).h.natAbs ∧
      p ∣ (doubleComplementQuad (m : ℤ) q).i.natAbs ∧
      p ∣ (doubleComplementQuad (m : ℤ) q).j.natAbs ∧
      p ∣ (doubleComplementQuad (m : ℤ) q).k.natAbs := by
    have hpIJK := hpContent.trans (Nat.gcd_dvd_right _ _)
    have hpJK := hpIJK.trans (Nat.gcd_dvd_right _ _)
    exact ⟨hpContent.trans (Nat.gcd_dvd_left _ _),
      hpIJK.trans (Nat.gcd_dvd_left _ _),
      hpJK.trans (Nat.gcd_dvd_left _ _),
      hpJK.trans (Nat.gcd_dvd_right _ _)⟩
  have hpCoordsInt :
      (p : ℤ) ∣ (doubleComplementQuad (m : ℤ) q).h ∧
      (p : ℤ) ∣ (doubleComplementQuad (m : ℤ) q).i ∧
      (p : ℤ) ∣ (doubleComplementQuad (m : ℤ) q).j ∧
      (p : ℤ) ∣ (doubleComplementQuad (m : ℤ) q).k := by
    simpa [Int.natCast_dvd] using hpCoords
  have hpTwoM : (p : ℤ) ∣ 2 * (m : ℤ) := by
    have hsum := (doubleComplementQuad_isQuad hq).1
    rw [← hsum]
    exact dvd_add (dvd_add (dvd_add hpCoordsInt.1 hpCoordsInt.2.1)
      hpCoordsInt.2.2.1) hpCoordsInt.2.2.2
  have hpne2 : p ≠ 2 := by
    intro hp2
    subst p
    have hmInt : Odd (m : ℤ) := by exact_mod_cast hm
    have hqOdd : Odd (doubleComplementQuad (m : ℤ) q).h := by
      simp [doubleComplementQuad, Int.odd_sub, hmInt]
    exact (Int.not_even_iff_odd.mpr hqOdd)
      (even_iff_two_dvd.mpr hpCoordsInt.1)
  have hpM : (p : ℤ) ∣ (m : ℤ) := by
    rcases Int.Prime.dvd_mul' hp hpTwoM with hp2 | hpm
    · exact (hpne2 (prime_dvd_four_implies_eq_two hp
        (hp2.trans (by norm_num : (2 : ℤ) ∣ 4)))).elim
    · exact hpm
  have hpQInt :
      (p : ℤ) ∣ q.h ∧ (p : ℤ) ∣ q.i ∧
      (p : ℤ) ∣ q.j ∧ (p : ℤ) ∣ q.k := by
    have get (a : ℤ) (ha : (p : ℤ) ∣ (m : ℤ) - 2 * a) :
        (p : ℤ) ∣ a := by
      have hp2a : (p : ℤ) ∣ 2 * a := by
        convert dvd_sub hpM ha using 1
        ring
      rcases Int.Prime.dvd_mul' hp hp2a with hp2 | hpa
      · exact (hpne2 (prime_dvd_four_implies_eq_two hp
          (hp2.trans (by norm_num : (2 : ℤ) ∣ 4)))).elim
      · exact hpa
    exact ⟨get q.h hpCoordsInt.1, get q.i hpCoordsInt.2.1,
      get q.j hpCoordsInt.2.2.1, get q.k hpCoordsInt.2.2.2⟩
  have hpQNat :
      p ∣ q.h.natAbs ∧ p ∣ q.i.natAbs ∧
      p ∣ q.j.natAbs ∧ p ∣ q.k.natAbs := by
    simpa [Int.natCast_dvd] using hpQInt
  have hpQContent : p ∣ quadContent q :=
    Nat.dvd_gcd hpQNat.1 (Nat.dvd_gcd hpQNat.2.1
      (Nat.dvd_gcd hpQNat.2.2.1 hpQNat.2.2.2))
  rw [hprimitive] at hpQContent
  exact hp.not_dvd_one hpQContent

theorem halfComplementQuad_primitive {m : ℕ} {q : QuadCoords}
    (hm : Odd m) (hq : IsQuad (2 * (m : ℤ)) q)
    (hprimitive : quadContent q = 1) :
    quadContent (halfComplementQuad (m : ℤ) q) = 1 := by
  have hodd := primitive_quad_coordinates_odd_at_twice_odd hm hq hprimitive
  have hrQuad := halfComplementQuad_isQuad hm hq hodd
  by_contra hrNot
  have hrNe : quadContent (halfComplementQuad (m : ℤ) q) ≠ 1 := hrNot
  obtain ⟨p, hp, hpContent⟩ := Nat.exists_prime_and_dvd hrNe
  have hpCoords :
      p ∣ (halfComplementQuad (m : ℤ) q).h.natAbs ∧
      p ∣ (halfComplementQuad (m : ℤ) q).i.natAbs ∧
      p ∣ (halfComplementQuad (m : ℤ) q).j.natAbs ∧
      p ∣ (halfComplementQuad (m : ℤ) q).k.natAbs := by
    have hpIJK := hpContent.trans (Nat.gcd_dvd_right _ _)
    have hpJK := hpIJK.trans (Nat.gcd_dvd_right _ _)
    exact ⟨hpContent.trans (Nat.gcd_dvd_left _ _),
      hpIJK.trans (Nat.gcd_dvd_left _ _),
      hpJK.trans (Nat.gcd_dvd_left _ _),
      hpJK.trans (Nat.gcd_dvd_right _ _)⟩
  have hpCoordsInt :
      (p : ℤ) ∣ (halfComplementQuad (m : ℤ) q).h ∧
      (p : ℤ) ∣ (halfComplementQuad (m : ℤ) q).i ∧
      (p : ℤ) ∣ (halfComplementQuad (m : ℤ) q).j ∧
      (p : ℤ) ∣ (halfComplementQuad (m : ℤ) q).k := by
    simpa [Int.natCast_dvd] using hpCoords
  have hpM : (p : ℤ) ∣ (m : ℤ) := by
    rw [← hrQuad.1]
    exact dvd_add (dvd_add (dvd_add hpCoordsInt.1 hpCoordsInt.2.1)
      hpCoordsInt.2.2.1) hpCoordsInt.2.2.2
  have hpQInt :
      (p : ℤ) ∣ q.h ∧ (p : ℤ) ∣ q.i ∧
      (p : ℤ) ∣ q.j ∧ (p : ℤ) ∣ q.k := by
    have htwice := halfComplementQuad_twice_eq hodd
      (by exact_mod_cast hm : Odd (m : ℤ))
    have get (a r : ℤ) (hr : 2 * r = (m : ℤ) - a)
        (hpr : (p : ℤ) ∣ r) : (p : ℤ) ∣ a := by
      have hp2r : (p : ℤ) ∣ 2 * r := by
        simpa [mul_comm] using dvd_mul_of_dvd_right hpr 2
      have hpm2r : (p : ℤ) ∣ (m : ℤ) - 2 * r := dvd_sub hpM hp2r
      convert hpm2r using 1
      linarith
    exact ⟨get q.h _ htwice.1 hpCoordsInt.1,
      get q.i _ htwice.2.1 hpCoordsInt.2.1,
      get q.j _ htwice.2.2.1 hpCoordsInt.2.2.1,
      get q.k _ htwice.2.2.2 hpCoordsInt.2.2.2⟩
  have hpQNat :
      p ∣ q.h.natAbs ∧ p ∣ q.i.natAbs ∧
      p ∣ q.j.natAbs ∧ p ∣ q.k.natAbs := by
    simpa [Int.natCast_dvd] using hpQInt
  have hpQContent : p ∣ quadContent q :=
    Nat.dvd_gcd hpQNat.1 (Nat.dvd_gcd hpQNat.2.1
      (Nat.dvd_gcd hpQNat.2.2.1 hpQNat.2.2.2))
  rw [hprimitive] at hpQContent
  exact hp.not_dvd_one hpQContent

theorem primitiveQuad_card_twice_odd {m : ℕ} (hm : Odd m) :
    (primitiveQuadFinset (2 * m)).card =
      (primitiveQuadFinset m).card := by
  symm
  apply Finset.card_nbij'
    (doubleComplementQuad (m : ℤ))
    (halfComplementQuad (m : ℤ))
  · intro q hq
    have hdata := mem_primitiveQuadFinset.mp hq
    exact mem_primitiveQuadFinset.mpr
      ⟨by simpa [Nat.cast_mul] using doubleComplementQuad_isQuad hdata.1,
        doubleComplementQuad_primitive hm hdata.1 hdata.2⟩
  · intro q hq
    have hdata := mem_primitiveQuadFinset.mp hq
    have hquad : IsQuad (2 * (m : ℤ)) q := by
      simpa [Nat.cast_mul] using hdata.1
    exact mem_primitiveQuadFinset.mpr
      ⟨halfComplementQuad_isQuad hm hquad
          (primitive_quad_coordinates_odd_at_twice_odd hm hquad hdata.2),
        halfComplementQuad_primitive hm hquad hdata.2⟩
  · intro q _
    exact half_doubleComplementQuad
  · intro q hq
    have hdata := mem_primitiveQuadFinset.mp hq
    have hquad : IsQuad (2 * (m : ℤ)) q := by
      simpa [Nat.cast_mul] using hdata.1
    exact double_halfComplementQuad hm
      (primitive_quad_coordinates_odd_at_twice_odd hm hquad hdata.2)

theorem pqFinite_twice_odd {m : ℕ} (hm : Odd m) :
    pqFinite (2 * m) = pqFinite m := by
  exact primitiveQuad_card_twice_odd hm

theorem pqFinite_mod_four_eq_two {n : ℕ} (hn : n % 4 = 2) :
    pqFinite n =
      r3PrimitiveFinite (3 * (n / 2) ^ 2) / 2 := by
  have hnEq : n = 2 * (n / 2) := by omega
  have hmOdd : Odd (n / 2) := by
    rw [Nat.odd_iff]
    omega
  calc
    pqFinite n = pqFinite (2 * (n / 2)) := by rw [← hnEq]
    _ = pqFinite (n / 2) := pqFinite_twice_odd hmOdd
    _ = r3PrimitiveFinite (3 * (n / 2) ^ 2) / 2 :=
      pqFinite_eq_r3PrimitiveFinite_div_two_of_odd hmOdd

end A354766
