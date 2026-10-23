import A354766.HadamardBridge

/-!
# Parity and admissibility for the Hadamard counting bridge

The statements in this file are closed congruence arguments plus their lifts
to integer triples.  They isolate the parity part of the odd-level bijection.
-/

namespace A354766

/-- The square-residue form of the fact that three squares equal to three
times an odd square modulo eight must all be odd squares. -/
theorem squareResidue8_three_eq_three_odd :
    ∀ a b c n : SquareResidue8,
      n.parity = 1 →
      a.value + b.value + c.value = 3 * n.value →
      a.parity = 1 ∧ b.parity = 1 ∧ c.parity = 1 := by
  decide

/-- At odd level, every coordinate in a three-square representation of
`3 * n^2` is odd. -/
theorem odd_threeSquare_coordinates {n : ℕ} {u : Triple}
    (hn : Odd n) (hu : IsThreeSquare (3 * n ^ 2) u) :
    Odd u.1 ∧ Odd u.2.1 ∧ Odd u.2.2 := by
  have hnInt : Odd (n : ℤ) := by exact_mod_cast hn
  have hmod8 :
      (u.1 : ZMod 8) ^ 2 + (u.2.1 : ZMod 8) ^ 2 +
          (u.2.2 : ZMod 8) ^ 2 =
        3 * (n : ZMod 8) ^ 2 := by
    have hc := congrArg (Int.castRingHom (ZMod 8)) hu
    norm_num [IsThreeSquare, Nat.cast_mul, Nat.cast_pow] at hc ⊢
    simpa using hc
  obtain ⟨rx, hxSq, hxParity⟩ := zmod8_square_class (u.1 : ZMod 8)
  obtain ⟨ry, hySq, hyParity⟩ := zmod8_square_class (u.2.1 : ZMod 8)
  obtain ⟨rz, hzSq, hzParity⟩ := zmod8_square_class (u.2.2 : ZMod 8)
  obtain ⟨rn, hnSq, hnParity⟩ := zmod8_square_class (n : ZMod 8)
  have hnClass : rn.parity = 1 := by
    rw [← hnParity]
    simpa using hnInt.intCast_zmod_two
  have hclasses :
      rx.value + ry.value + rz.value = 3 * rn.value := by
    simpa [hxSq, hySq, hzSq, hnSq] using hmod8
  have hp := squareResidue8_three_eq_three_odd rx ry rz rn hnClass hclasses
  have hxMod2 : (u.1 : ZMod 2) = 1 := by
    simpa using hxParity.trans hp.1
  have hyMod2 : (u.2.1 : ZMod 2) = 1 := by
    simpa using hyParity.trans hp.2.1
  have hzMod2 : (u.2.2 : ZMod 2) = 1 := by
    simpa using hzParity.trans hp.2.2
  exact ⟨ZMod.intCast_eq_one_iff_odd.mp hxMod2,
    ZMod.intCast_eq_one_iff_odd.mp hyMod2,
    ZMod.intCast_eq_one_iff_odd.mp hzMod2⟩

/-- For four odd residues modulo four, divisibility of the first inverse
numerator forces divisibility of all four. -/
theorem zmod4_all_inverse_numerators_zero
    (n x y z : ZMod 4)
    (hn : ZMod.castHom (by decide : 2 ∣ 4) (ZMod 2) n = 1)
    (hx : ZMod.castHom (by decide : 2 ∣ 4) (ZMod 2) x = 1)
    (hy : ZMod.castHom (by decide : 2 ∣ 4) (ZMod 2) y = 1)
    (hz : ZMod.castHom (by decide : 2 ∣ 4) (ZMod 2) z = 1)
    (hh : n + x + y + z = 0) :
    n + x - y - z = 0 ∧
    n - x + y - z = 0 ∧
    n - x - y + z = 0 := by
  revert n x y z
  decide

/-- For four odd residues modulo four, exactly one of a triple and its
simultaneous negative satisfies the first inverse congruence. -/
theorem zmod4_exactly_one_sign_admissible
    (n x y z : ZMod 4)
    (hn : ZMod.castHom (by decide : 2 ∣ 4) (ZMod 2) n = 1)
    (hx : ZMod.castHom (by decide : 2 ∣ 4) (ZMod 2) x = 1)
    (hy : ZMod.castHom (by decide : 2 ∣ 4) (ZMod 2) y = 1)
    (hz : ZMod.castHom (by decide : 2 ∣ 4) (ZMod 2) z = 1) :
    ((n + x + y + z = 0) ∧ ¬(n - x - y - z = 0)) ∨
    (¬(n + x + y + z = 0) ∧ (n - x - y - z = 0)) := by
  revert n x y z
  decide

def OddTripleAdmissible (n : ℤ) (u : Triple) : Prop :=
  (4 : ℤ) ∣ hNum n u.1 u.2.1 u.2.2

instance (n : ℤ) (u : Triple) : Decidable (OddTripleAdmissible n u) := by
  unfold OddTripleAdmissible
  infer_instance

/-- For odd data, the single admissibility congruence implies divisibility of
all four inverse numerators. -/
theorem inverseNumeratorsDivisible_of_odd_admissible
    {n : ℤ} {u : Triple}
    (hn : Odd n) (hu : Odd u.1 ∧ Odd u.2.1 ∧ Odd u.2.2)
    (hadm : OddTripleAdmissible n u) :
    InverseNumeratorsDivisible n u := by
  have hn2 : ZMod.castHom (by decide : 2 ∣ 4) (ZMod 2) (n : ZMod 4) = 1 := by
    simpa using hn.intCast_zmod_two
  have hx2 : ZMod.castHom (by decide : 2 ∣ 4) (ZMod 2) (u.1 : ZMod 4) = 1 := by
    simpa using hu.1.intCast_zmod_two
  have hy2 : ZMod.castHom (by decide : 2 ∣ 4) (ZMod 2) (u.2.1 : ZMod 4) = 1 := by
    simpa using hu.2.1.intCast_zmod_two
  have hz2 : ZMod.castHom (by decide : 2 ∣ 4) (ZMod 2) (u.2.2 : ZMod 4) = 1 := by
    simpa using hu.2.2.intCast_zmod_two
  have hh4 :
      (n : ZMod 4) + (u.1 : ZMod 4) +
          (u.2.1 : ZMod 4) + (u.2.2 : ZMod 4) = 0 := by
    simpa [OddTripleAdmissible, hNum,
      ZMod.intCast_zmod_eq_zero_iff_dvd] using
        (ZMod.intCast_zmod_eq_zero_iff_dvd
          (hNum n u.1 u.2.1 u.2.2) 4).2 hadm
  have hall := zmod4_all_inverse_numerators_zero
    (n : ZMod 4) (u.1 : ZMod 4) (u.2.1 : ZMod 4) (u.2.2 : ZMod 4)
    hn2 hx2 hy2 hz2 hh4
  refine ⟨hadm, ?_, ?_, ?_⟩
  · exact (ZMod.intCast_zmod_eq_zero_iff_dvd
      (iNum n u.1 u.2.1 u.2.2) 4).1 (by
        simpa [iNum] using hall.1)
  · exact (ZMod.intCast_zmod_eq_zero_iff_dvd
      (jNum n u.1 u.2.1 u.2.2) 4).1 (by
        simpa [jNum] using hall.2.1)
  · exact (ZMod.intCast_zmod_eq_zero_iff_dvd
      (kNum n u.1 u.2.1 u.2.2) 4).1 (by
        simpa [kNum] using hall.2.2)

/-- At odd level, simultaneous negation toggles admissibility. -/
theorem exactly_one_sign_oddTripleAdmissible
    {n : ℤ} {u : Triple}
    (hn : Odd n) (hu : Odd u.1 ∧ Odd u.2.1 ∧ Odd u.2.2) :
    (OddTripleAdmissible n u ∧
        ¬OddTripleAdmissible n (negateTriple u)) ∨
      (¬OddTripleAdmissible n u ∧
        OddTripleAdmissible n (negateTriple u)) := by
  have hn2 : ZMod.castHom (by decide : 2 ∣ 4) (ZMod 2) (n : ZMod 4) = 1 := by
    simpa using hn.intCast_zmod_two
  have hx2 : ZMod.castHom (by decide : 2 ∣ 4) (ZMod 2) (u.1 : ZMod 4) = 1 := by
    simpa using hu.1.intCast_zmod_two
  have hy2 : ZMod.castHom (by decide : 2 ∣ 4) (ZMod 2) (u.2.1 : ZMod 4) = 1 := by
    simpa using hu.2.1.intCast_zmod_two
  have hz2 : ZMod.castHom (by decide : 2 ∣ 4) (ZMod 2) (u.2.2 : ZMod 4) = 1 := by
    simpa using hu.2.2.intCast_zmod_two
  have hx := zmod4_exactly_one_sign_admissible
    (n : ZMod 4) (u.1 : ZMod 4) (u.2.1 : ZMod 4) (u.2.2 : ZMod 4)
    hn2 hx2 hy2 hz2
  have hx' :
      (((hNum n u.1 u.2.1 u.2.2 : ℤ) : ZMod 4) = 0 ∧
          ¬(((hNum n (negateTriple u).1 (negateTriple u).2.1
            (negateTriple u).2.2 : ℤ) : ZMod 4) = 0)) ∨
        (¬(((hNum n u.1 u.2.1 u.2.2 : ℤ) : ZMod 4) = 0) ∧
          ((hNum n (negateTriple u).1 (negateTriple u).2.1
            (negateTriple u).2.2 : ℤ) : ZMod 4) = 0) := by
    simpa [negateTriple, hNum, sub_eq_add_neg] using hx
  have hpos :
      OddTripleAdmissible n u ↔
        ((hNum n u.1 u.2.1 u.2.2 : ℤ) : ZMod 4) = 0 := by
    exact (ZMod.intCast_zmod_eq_zero_iff_dvd
      (hNum n u.1 u.2.1 u.2.2) 4).symm
  have hneg :
      OddTripleAdmissible n (negateTriple u) ↔
        ((hNum n (negateTriple u).1 (negateTriple u).2.1
          (negateTriple u).2.2 : ℤ) : ZMod 4) = 0 := by
    exact (ZMod.intCast_zmod_eq_zero_iff_dvd
      (hNum n (negateTriple u).1 (negateTriple u).2.1
        (negateTriple u).2.2) 4).symm
  rw [hpos, hneg]
  exact hx'

end A354766
