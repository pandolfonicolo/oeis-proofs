import A354766.PrimitivityBridge

/-!
# Primitive odd-level counting bridge

This file restricts the raw odd-level bijections to content one, using the
prime-by-prime content equivalence from `PrimitivityBridge`.
-/

namespace A354766

def primitiveOddAdmissibleFinset (n : ℕ) : Finset Triple :=
  (primitiveThreeSquareFinset (3 * n ^ 2)).filter
    (OddTripleAdmissible (n : ℤ))

def primitiveOddInadmissibleFinset (n : ℕ) : Finset Triple :=
  (primitiveThreeSquareFinset (3 * n ^ 2)).filter
    fun u => ¬OddTripleAdmissible (n : ℤ) u

@[simp] theorem mem_primitiveOddAdmissibleFinset {n : ℕ} {u : Triple} :
    u ∈ primitiveOddAdmissibleFinset n ↔
      IsThreeSquare (3 * n ^ 2) u ∧ tripleContent u = 1 ∧
        OddTripleAdmissible (n : ℤ) u := by
  simp [primitiveOddAdmissibleFinset, and_assoc]

@[simp] theorem mem_primitiveOddInadmissibleFinset {n : ℕ} {u : Triple} :
    u ∈ primitiveOddInadmissibleFinset n ↔
      IsThreeSquare (3 * n ^ 2) u ∧ tripleContent u = 1 ∧
        ¬OddTripleAdmissible (n : ℤ) u := by
  simp [primitiveOddInadmissibleFinset, and_assoc]

@[simp] theorem tripleContent_negateTriple (u : Triple) :
    tripleContent (negateTriple u) = tripleContent u := by
  rcases u with ⟨x, y, z⟩
  simp [tripleContent, negateTriple]

theorem primitiveQuad_card_eq_primitiveOddAdmissible_card
    {n : ℕ} (hn : Odd n) :
    (primitiveQuadFinset n).card =
      (primitiveOddAdmissibleFinset n).card := by
  apply Finset.card_nbij'
    forwardTriple
    (inverseQuad (n : ℤ))
  · intro q hq
    have hdata := mem_primitiveQuadFinset.mp hq
    exact mem_primitiveOddAdmissibleFinset.mpr
      ⟨forwardTriple_isThreeSquare hdata.1,
        (quadContent_eq_one_iff_forward_tripleContent_eq_one
          hn hdata.1).mp hdata.2,
        (inverseNumeratorsDivisible_forwardTriple hdata.1).1⟩
  · intro u hu
    have hdata := mem_primitiveOddAdmissibleFinset.mp hu
    have hnInt : Odd (n : ℤ) := by exact_mod_cast hn
    have huOdd := odd_threeSquare_coordinates hn hdata.1
    have hdiv := inverseNumeratorsDivisible_of_odd_admissible
      hnInt huOdd hdata.2.2
    have hquad := inverseQuad_isQuad hdata.1 hdiv
    have hcontent :
        quadContent (inverseQuad (n : ℤ) u) = 1 := by
      apply (quadContent_eq_one_iff_forward_tripleContent_eq_one
        hn hquad).mpr
      rw [forwardTriple_inverseQuad hdiv]
      exact hdata.2.1
    exact mem_primitiveQuadFinset.mpr ⟨hquad, hcontent⟩
  · intro q hq
    exact inverseQuad_forwardTriple (mem_primitiveQuadFinset.mp hq).1
  · intro u hu
    have hdata := mem_primitiveOddAdmissibleFinset.mp hu
    have hnInt : Odd (n : ℤ) := by exact_mod_cast hn
    have huOdd := odd_threeSquare_coordinates hn hdata.1
    exact forwardTriple_inverseQuad
      (inverseNumeratorsDivisible_of_odd_admissible hnInt huOdd hdata.2.2)

theorem primitiveOddAdmissible_card_eq_inadmissible_card
    {n : ℕ} (hn : Odd n) :
    (primitiveOddAdmissibleFinset n).card =
      (primitiveOddInadmissibleFinset n).card := by
  apply Finset.card_nbij' negateTriple negateTriple
  · intro u hu
    have hdata := mem_primitiveOddAdmissibleFinset.mp hu
    have huOdd := odd_threeSquare_coordinates hn hdata.1
    have hnInt : Odd (n : ℤ) := by exact_mod_cast hn
    have htoggle :=
      exactly_one_sign_oddTripleAdmissible hnInt huOdd
    have hnot : ¬OddTripleAdmissible (n : ℤ) (negateTriple u) := by
      rcases htoggle with hgood | hgood
      · exact hgood.2
      · exact (hgood.1 hdata.2.2).elim
    exact mem_primitiveOddInadmissibleFinset.mpr
      ⟨negateTriple_isThreeSquare hdata.1,
        by simpa using hdata.2.1, hnot⟩
  · intro u hu
    have hdata := mem_primitiveOddInadmissibleFinset.mp hu
    have huOdd := odd_threeSquare_coordinates hn hdata.1
    have hnInt : Odd (n : ℤ) := by exact_mod_cast hn
    have htoggle :=
      exactly_one_sign_oddTripleAdmissible hnInt huOdd
    have hadm : OddTripleAdmissible (n : ℤ) (negateTriple u) := by
      rcases htoggle with hgood | hgood
      · exact (hdata.2.2 hgood.1).elim
      · exact hgood.2
    exact mem_primitiveOddAdmissibleFinset.mpr
      ⟨negateTriple_isThreeSquare hdata.1,
        by simpa using hdata.2.1, hadm⟩
  · intro u _
    exact negateTriple_involutive u
  · intro u _
    exact negateTriple_involutive u

theorem primitiveThreeSquare_card_eq_two_mul_primitiveOddAdmissible_card
    {n : ℕ} (hn : Odd n) :
    (primitiveThreeSquareFinset (3 * n ^ 2)).card =
      2 * (primitiveOddAdmissibleFinset n).card := by
  have hpartition := Finset.card_filter_add_card_filter_not
    (s := primitiveThreeSquareFinset (3 * n ^ 2))
    (p := OddTripleAdmissible (n : ℤ))
  have heq := primitiveOddAdmissible_card_eq_inadmissible_card hn
  change (primitiveOddAdmissibleFinset n).card +
      (primitiveOddInadmissibleFinset n).card =
      (primitiveThreeSquareFinset (3 * n ^ 2)).card at hpartition
  omega

/-- The fully primitive odd-level bridge, without division. -/
theorem r3PrimitiveFinite_eq_two_mul_pqFinite_of_odd
    {n : ℕ} (hn : Odd n) :
    r3PrimitiveFinite (3 * n ^ 2) = 2 * pqFinite n := by
  rw [r3PrimitiveFinite, pqFinite,
    primitiveThreeSquare_card_eq_two_mul_primitiveOddAdmissible_card hn,
    primitiveQuad_card_eq_primitiveOddAdmissible_card hn]

/-- Division form used in the OEIS statement. -/
theorem pqFinite_eq_r3PrimitiveFinite_div_two_of_odd
    {n : ℕ} (hn : Odd n) :
    pqFinite n = r3PrimitiveFinite (3 * n ^ 2) / 2 := by
  rw [r3PrimitiveFinite_eq_two_mul_pqFinite_of_odd hn]
  omega

end A354766
