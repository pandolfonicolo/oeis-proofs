import A354766.PrimitiveOddCounting
import A354766.DoublingBridge

/-!
# Sign orbits and divisibility by four

At an odd three-square level all three coordinates are odd, hence nonzero.
Independent sign changes therefore split the primitive representations into
eight equipotent octants.  Combined with the factor-two Hadamard bridge, this
proves that every primitive quad count is divisible by four.
-/

namespace A354766

def flipX (u : Triple) : Triple := (-u.1, u.2.1, u.2.2)
def flipY (u : Triple) : Triple := (u.1, -u.2.1, u.2.2)
def flipZ (u : Triple) : Triple := (u.1, u.2.1, -u.2.2)

@[simp] theorem flipX_involutive (u : Triple) : flipX (flipX u) = u := by
  rcases u with ⟨x, y, z⟩
  simp [flipX]

@[simp] theorem flipY_involutive (u : Triple) : flipY (flipY u) = u := by
  rcases u with ⟨x, y, z⟩
  simp [flipY]

@[simp] theorem flipZ_involutive (u : Triple) : flipZ (flipZ u) = u := by
  rcases u with ⟨x, y, z⟩
  simp [flipZ]

@[simp] theorem isThreeSquare_flipX {N : ℕ} {u : Triple} :
    IsThreeSquare N (flipX u) ↔ IsThreeSquare N u := by
  rcases u with ⟨x, y, z⟩
  simp [IsThreeSquare, flipX]

@[simp] theorem isThreeSquare_flipY {N : ℕ} {u : Triple} :
    IsThreeSquare N (flipY u) ↔ IsThreeSquare N u := by
  rcases u with ⟨x, y, z⟩
  simp [IsThreeSquare, flipY]

@[simp] theorem isThreeSquare_flipZ {N : ℕ} {u : Triple} :
    IsThreeSquare N (flipZ u) ↔ IsThreeSquare N u := by
  rcases u with ⟨x, y, z⟩
  simp [IsThreeSquare, flipZ]

@[simp] theorem tripleContent_flipX (u : Triple) :
    tripleContent (flipX u) = tripleContent u := by
  rcases u with ⟨x, y, z⟩
  simp [tripleContent, flipX]

@[simp] theorem tripleContent_flipY (u : Triple) :
    tripleContent (flipY u) = tripleContent u := by
  rcases u with ⟨x, y, z⟩
  simp [tripleContent, flipY]

@[simp] theorem tripleContent_flipZ (u : Triple) :
    tripleContent (flipZ u) = tripleContent u := by
  rcases u with ⟨x, y, z⟩
  simp [tripleContent, flipZ]

theorem card_eq_two_mul_card_filter_pos
    {α : Type*} [DecidableEq α]
    (s : Finset α) (coord : α → ℤ) (flip : α → α)
    (hmem : ∀ a, a ∈ s → flip a ∈ s)
    (hinv : ∀ a, flip (flip a) = a)
    (hneg : ∀ a, coord (flip a) = -coord a)
    (hne : ∀ a, a ∈ s → coord a ≠ 0) :
    s.card = 2 * (s.filter fun a => 0 < coord a).card := by
  have heq :
      (s.filter fun a => 0 < coord a).card =
        (s.filter fun a => ¬0 < coord a).card := by
    apply Finset.card_nbij' flip flip
    · intro a ha
      have ha' : a ∈ s ∧ 0 < coord a := by simpa using ha
      have hout : flip a ∈ s ∧ ¬0 < coord (flip a) :=
        ⟨hmem a ha'.1, by rw [hneg]; omega⟩
      simpa using hout
    · intro a ha
      have ha' : a ∈ s ∧ ¬0 < coord a := by simpa using ha
      have haNeg : coord a < 0 := by
        have := hne a ha'.1
        omega
      have hout : flip a ∈ s ∧ 0 < coord (flip a) :=
        ⟨hmem a ha'.1, by rw [hneg]; omega⟩
      simpa using hout
    · intro a _
      exact hinv a
    · intro a _
      exact hinv a
  have hpartition := Finset.card_filter_add_card_filter_not
    (s := s) (p := fun a => 0 < coord a)
  omega

def primitiveXPositiveFinset (m : ℕ) : Finset Triple :=
  (primitiveThreeSquareFinset (3 * m ^ 2)).filter fun u => 0 < u.1

def primitiveXYPositiveFinset (m : ℕ) : Finset Triple :=
  (primitiveXPositiveFinset m).filter fun u => 0 < u.2.1

def primitiveXYZPositiveFinset (m : ℕ) : Finset Triple :=
  (primitiveXYPositiveFinset m).filter fun u => 0 < u.2.2

theorem primitiveThreeSquare_card_eq_eight_mul_positive
    {m : ℕ} (hm : Odd m) :
    (primitiveThreeSquareFinset (3 * m ^ 2)).card =
      8 * (primitiveXYZPositiveFinset m).card := by
  let s0 := primitiveThreeSquareFinset (3 * m ^ 2)
  have hx : s0.card = 2 * (primitiveXPositiveFinset m).card := by
    change s0.card = 2 * (s0.filter fun u => 0 < u.1).card
    apply card_eq_two_mul_card_filter_pos s0 (fun u => u.1) flipX
    · intro u hu
      rw [mem_primitiveThreeSquareFinset] at hu ⊢
      exact ⟨isThreeSquare_flipX.mpr hu.1, by simpa using hu.2⟩
    · exact flipX_involutive
    · intro u
      rfl
    · intro u hu
      have hdata := mem_primitiveThreeSquareFinset.mp hu
      have hodd := (odd_threeSquare_coordinates hm hdata.1).1
      intro hzero
      simp [hzero] at hodd
  have hy :
      (primitiveXPositiveFinset m).card =
        2 * (primitiveXYPositiveFinset m).card := by
    change (primitiveXPositiveFinset m).card =
      2 * ((primitiveXPositiveFinset m).filter fun u => 0 < u.2.1).card
    apply card_eq_two_mul_card_filter_pos
      (primitiveXPositiveFinset m) (fun u => u.2.1) flipY
    · intro u hu
      simp only [primitiveXPositiveFinset, Finset.mem_filter] at hu ⊢
      rw [mem_primitiveThreeSquareFinset] at hu ⊢
      exact ⟨⟨isThreeSquare_flipY.mpr hu.1.1, by simpa using hu.1.2⟩, hu.2⟩
    · exact flipY_involutive
    · intro u
      rfl
    · intro u hu
      have hdata := (mem_primitiveThreeSquareFinset.mp
        (Finset.mem_filter.mp hu).1)
      have hodd := (odd_threeSquare_coordinates hm hdata.1).2.1
      intro hzero
      simp [hzero] at hodd
  have hz :
      (primitiveXYPositiveFinset m).card =
        2 * (primitiveXYZPositiveFinset m).card := by
    change (primitiveXYPositiveFinset m).card =
      2 * ((primitiveXYPositiveFinset m).filter fun u => 0 < u.2.2).card
    apply card_eq_two_mul_card_filter_pos
      (primitiveXYPositiveFinset m) (fun u => u.2.2) flipZ
    · intro u hu
      simp only [primitiveXYPositiveFinset, primitiveXPositiveFinset,
        Finset.mem_filter] at hu ⊢
      rw [mem_primitiveThreeSquareFinset] at hu ⊢
      exact ⟨⟨⟨isThreeSquare_flipZ.mpr hu.1.1.1,
        by simpa using hu.1.1.2⟩, hu.1.2⟩, hu.2⟩
    · exact flipZ_involutive
    · intro u
      rfl
    · intro u hu
      have hdata := (mem_primitiveThreeSquareFinset.mp
        (Finset.mem_filter.mp (Finset.mem_filter.mp hu).1).1)
      have hodd := (odd_threeSquare_coordinates hm hdata.1).2.2
      intro hzero
      simp [hzero] at hodd
  rw [hx, hy, hz]
  omega

theorem four_dvd_pqFinite_of_odd {m : ℕ} (hm : Odd m) :
    4 ∣ pqFinite m := by
  let positiveCount := (primitiveXYZPositiveFinset m).card
  have h8 :
      r3PrimitiveFinite (3 * m ^ 2) = 8 * positiveCount := by
    exact primitiveThreeSquare_card_eq_eight_mul_positive hm
  have h2 := r3PrimitiveFinite_eq_two_mul_pqFinite_of_odd hm
  use positiveCount
  omega

theorem four_dvd_pqFinite (n : ℕ) : 4 ∣ pqFinite n := by
  by_cases hnOdd : Odd n
  · exact four_dvd_pqFinite_of_odd hnOdd
  · have hnEven : n % 2 = 0 := Nat.not_odd_iff.mp hnOdd
    by_cases hnTwo : n % 4 = 2
    · have hmOdd : Odd (n / 2) := by
        rw [Nat.odd_iff]
        omega
      have hnEq : n = 2 * (n / 2) := by omega
      rw [hnEq, pqFinite_twice_odd hmOdd]
      exact four_dvd_pqFinite_of_odd hmOdd
    · have hnFour : 4 ∣ n := by
        rw [Nat.dvd_iff_mod_eq_zero]
        have hlt := Nat.mod_lt n (by omega : 0 < 4)
        omega
      rw [pqFinite_eq_zero_of_four_dvd hnFour]
      exact dvd_zero 4

end A354766
