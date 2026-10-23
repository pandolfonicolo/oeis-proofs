import A354766.ParityBridge

/-!
# The non-primitive odd-level counting bridge

This file proves the exact bijection between quads at an odd level and the
admissible half of the corresponding three-square representations, and proves
that simultaneous negation pairs the admissible and inadmissible halves.
-/

namespace A354766

def oddAdmissibleThreeSquareFinset (n : ℕ) : Finset Triple :=
  (threeSquareFinset (3 * n ^ 2)).filter
    (OddTripleAdmissible (n : ℤ))

def oddInadmissibleThreeSquareFinset (n : ℕ) : Finset Triple :=
  (threeSquareFinset (3 * n ^ 2)).filter
    fun u => ¬OddTripleAdmissible (n : ℤ) u

@[simp] theorem mem_oddAdmissibleThreeSquareFinset {n : ℕ} {u : Triple} :
    u ∈ oddAdmissibleThreeSquareFinset n ↔
      IsThreeSquare (3 * n ^ 2) u ∧ OddTripleAdmissible (n : ℤ) u := by
  simp [oddAdmissibleThreeSquareFinset]

@[simp] theorem mem_oddInadmissibleThreeSquareFinset {n : ℕ} {u : Triple} :
    u ∈ oddInadmissibleThreeSquareFinset n ↔
      IsThreeSquare (3 * n ^ 2) u ∧ ¬OddTripleAdmissible (n : ℤ) u := by
  simp [oddInadmissibleThreeSquareFinset]

theorem negateTriple_isThreeSquare {N : ℕ} {u : Triple}
    (hu : IsThreeSquare N u) :
    IsThreeSquare N (negateTriple u) := by
  rcases u with ⟨x, y, z⟩
  simpa [IsThreeSquare, negateTriple, pow_two] using hu

/-- At odd level, forward Hadamard and exact inverse division give a bijection
between all quads and the admissible three-square triples. -/
theorem quadFinset_card_eq_oddAdmissible_card
    {n : ℕ} (hn : Odd n) :
    (quadFinset n).card = (oddAdmissibleThreeSquareFinset n).card := by
  apply Finset.card_nbij'
    (forwardTriple)
    (inverseQuad (n : ℤ))
  · intro q hq
    have hquad : IsQuad (n : ℤ) q := mem_quadFinset.mp hq
    exact mem_oddAdmissibleThreeSquareFinset.mpr
      ⟨forwardTriple_isThreeSquare hquad,
        (inverseNumeratorsDivisible_forwardTriple hquad).1⟩
  · intro u hu
    have hdata := mem_oddAdmissibleThreeSquareFinset.mp hu
    have hnInt : Odd (n : ℤ) := by exact_mod_cast hn
    have huOdd := odd_threeSquare_coordinates hn hdata.1
    have hdiv := inverseNumeratorsDivisible_of_odd_admissible
      hnInt huOdd hdata.2
    exact mem_quadFinset.mpr (inverseQuad_isQuad hdata.1 hdiv)
  · intro q hq
    exact inverseQuad_forwardTriple (mem_quadFinset.mp hq)
  · intro u hu
    have hdata := mem_oddAdmissibleThreeSquareFinset.mp hu
    have hnInt : Odd (n : ℤ) := by exact_mod_cast hn
    have huOdd := odd_threeSquare_coordinates hn hdata.1
    exact forwardTriple_inverseQuad
      (inverseNumeratorsDivisible_of_odd_admissible hnInt huOdd hdata.2)

theorem oddAdmissible_card_eq_inadmissible_card
    {n : ℕ} (hn : Odd n) :
    (oddAdmissibleThreeSquareFinset n).card =
      (oddInadmissibleThreeSquareFinset n).card := by
  apply Finset.card_nbij' negateTriple negateTriple
  · intro u hu
    have hdata := mem_oddAdmissibleThreeSquareFinset.mp hu
    have huOdd := odd_threeSquare_coordinates hn hdata.1
    have hnInt : Odd (n : ℤ) := by exact_mod_cast hn
    have htoggle :=
      exactly_one_sign_oddTripleAdmissible hnInt huOdd
    have hnot : ¬OddTripleAdmissible (n : ℤ) (negateTriple u) := by
      rcases htoggle with hgood | hgood
      · exact hgood.2
      · exact (hgood.1 hdata.2).elim
    exact mem_oddInadmissibleThreeSquareFinset.mpr
      ⟨negateTriple_isThreeSquare hdata.1, hnot⟩
  · intro u hu
    have hdata := mem_oddInadmissibleThreeSquareFinset.mp hu
    have huOdd := odd_threeSquare_coordinates hn hdata.1
    have hnInt : Odd (n : ℤ) := by exact_mod_cast hn
    have htoggle :=
      exactly_one_sign_oddTripleAdmissible hnInt huOdd
    have hadm : OddTripleAdmissible (n : ℤ) (negateTriple u) := by
      rcases htoggle with hgood | hgood
      · exact (hdata.2 hgood.1).elim
      · exact hgood.2
    exact mem_oddAdmissibleThreeSquareFinset.mpr
      ⟨negateTriple_isThreeSquare hdata.1, hadm⟩
  · intro u _
    exact negateTriple_involutive u
  · intro u _
    exact negateTriple_involutive u

theorem threeSquare_card_eq_two_mul_oddAdmissible_card
    {n : ℕ} (hn : Odd n) :
    (threeSquareFinset (3 * n ^ 2)).card =
      2 * (oddAdmissibleThreeSquareFinset n).card := by
  have hpartition := Finset.card_filter_add_card_filter_not
    (s := threeSquareFinset (3 * n ^ 2))
    (p := OddTripleAdmissible (n : ℤ))
  have heq := oddAdmissible_card_eq_inadmissible_card hn
  change (oddAdmissibleThreeSquareFinset n).card +
      (oddInadmissibleThreeSquareFinset n).card =
      (threeSquareFinset (3 * n ^ 2)).card at hpartition
  omega

/-- Exact raw-count bridge at odd levels. -/
theorem r3Finite_eq_two_mul_tqFinite_of_odd
    {n : ℕ} (hn : Odd n) :
    r3Finite (3 * n ^ 2) = 2 * tqFinite n := by
  rw [r3Finite, tqFinite,
    threeSquare_card_eq_two_mul_oddAdmissible_card hn,
    quadFinset_card_eq_oddAdmissible_card hn]

end A354766
