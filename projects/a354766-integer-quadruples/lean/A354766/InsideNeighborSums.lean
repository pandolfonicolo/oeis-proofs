import A354766.NeighborFiberCounts
import A354766.ShellPartitions
import A354766.NeighborShellCounts

/-!
Global inside counts, obtained by an explicit reordering of the finite
neighbor/vector incidence set. Every fiber coefficient is supplied by the
proved concrete family lemmas; no representation recurrence is assumed.
-/

noncomputable section

open scoped BigOperators

namespace A354766Neighbors

open A354766Research.Neighbor A354766Research.NeighborFamily
open A354766Research.IsotropicLines

/-- Reorder an incidence set without changing any membership condition. -/
def sigmaFiberSwap {A B : Type*} (R : A → B → Prop) :
    (Σ a : A, {b : B // R a b}) ≃ Σ b : B, {a : A // R a b} where
  toFun x := ⟨x.2.val, x.1, x.2.property⟩
  invFun x := ⟨x.2.val, x.1, x.2.property⟩
  left_inv _ := rfl
  right_inv _ := rfl

/-- Count a family from its actual constant vector fibers. -/
theorem sigma_card_from_constant_fibers
    {A B : Type*} [Finite A] [Finite B]
    (T : A → Type*) [∀ a, Finite (T a)] (R : A → B → Prop) (k : ℤ)
    (hT : ∀ a, Nat.card (T a) = Nat.card {b : B // R a b})
    (hR : ∀ b, (Nat.card {a : A // R a b} : ℤ) = k) :
    (Nat.card (Σ a, T a) : ℤ) = k * (Nat.card B : ℤ) := by
  classical
  letI : Fintype A := Fintype.ofFinite A
  letI : Fintype B := Fintype.ofFinite B
  have hcards : Nat.card (Σ a, T a) = Nat.card (Σ a : A, {b : B // R a b}) := by
    rw [Nat.card_sigma, Nat.card_sigma]
    exact Finset.sum_congr rfl (fun a _ => hT a)
  rw [hcards, Nat.card_congr (sigmaFiberSwap R), Nat.card_sigma, Nat.cast_sum]
  calc
    (∑ b : B, (Nat.card {a : A // R a b} : ℤ)) = ∑ _ : B, k :=
      Finset.sum_congr rfl (fun b _ => hR b)
    _ = k * (Nat.card B : ℤ) := by
      simp [Nat.card_eq_fintype_card, mul_comm]

def sumsStandardShellCast (n : ℕ) : PrimitiveVectorShell n →
    AmbientPrimitiveShell standard rationalNorm (n : ℚ) := fun v =>
  ⟨castVec v.val, ⟨v.val, rfl⟩, by
    rw [rationalNorm_castVec, v.property.1]
    simp only [Int.cast_natCast],
    (primitiveIn_standard_castVec_iff v.val).mpr v.property.2⟩

theorem sumsStandardShellCast_bijective (n : ℕ) :
    Function.Bijective (sumsStandardShellCast n) := by
  constructor
  · intro x y h
    exact Subtype.ext (castVec_injective (congrArg Subtype.val h))
  · rintro ⟨x, ⟨v, rfl⟩, hQ, hprim⟩
    have hvQ : vectorNorm v = (n : ℤ) := by
      rw [rationalNorm_castVec] at hQ
      exact_mod_cast hQ
    exact ⟨⟨v, hvQ, (primitiveIn_standard_castVec_iff v).mp hprim⟩, rfl⟩

def sumsStandardShellCastEquiv (n : ℕ) : PrimitiveVectorShell n ≃
    AmbientPrimitiveShell standard rationalNorm (n : ℚ) :=
  Equiv.ofBijective (sumsStandardShellCast n) (sumsStandardShellCast_bijective n)

theorem sums_standard_shell_finite (n : ℕ) :
    Finite (AmbientPrimitiveShell standard rationalNorm (n : ℚ)) :=
  Finite.of_equiv (PrimitiveVectorShell n) (sumsStandardShellCastEquiv n)

abbrev SumsStandardInside (N : Submodule ℤ RatVec) (n : ℕ) :=
  {x : RatVec // x ∈ standard ∧ x ∈ N ∧ rationalNorm x = (n : ℚ) ∧
    PrimitiveIn standard x ∧ PrimitiveIn N x}

def sumsInsideCast (N : Submodule ℤ RatVec) (n : ℕ) :
    {z : PrimitiveVectorShell n // castVec z.val ∈ N ∧ PrimitiveIn N (castVec z.val)} →
      SumsStandardInside N n := fun z =>
  ⟨castVec z.val.val, ⟨z.val.val, rfl⟩, z.property.1, by
    rw [rationalNorm_castVec, z.val.property.1]
    simp only [Int.cast_natCast],
    (primitiveIn_standard_castVec_iff z.val.val).mpr z.val.property.2, z.property.2⟩

theorem sumsInsideCast_bijective (N : Submodule ℤ RatVec) (n : ℕ) :
    Function.Bijective (sumsInsideCast N n) := by
  constructor
  · intro x y h
    apply Subtype.ext
    apply Subtype.ext
    exact castVec_injective (congrArg Subtype.val h)
  · rintro ⟨x, ⟨v, rfl⟩, hvN, hQ, hprim, hprimN⟩
    have hvQ : vectorNorm v = (n : ℤ) := by
      rw [rationalNorm_castVec] at hQ
      exact_mod_cast hQ
    exact ⟨⟨⟨v, hvQ, (primitiveIn_standard_castVec_iff v).mp hprim⟩, hvN, hprimN⟩, rfl⟩

def sumsInsideCastEquiv (N : Submodule ℤ RatVec) (n : ℕ) :
    {z : PrimitiveVectorShell n // castVec z.val ∈ N ∧ PrimitiveIn N (castVec z.val)} ≃
      SumsStandardInside N n :=
  Equiv.ofBijective (sumsInsideCast N n) (sumsInsideCast_bijective N n)

def sumsOutsideCast (N : Submodule ℤ RatVec) (n : ℕ) :
    {z : PrimitiveVectorShell n // castVec z.val ∉ N} →
      OutsidePrimitiveShell N standard rationalNorm (n : ℚ) := fun z =>
  ⟨castVec z.val.val, ⟨z.val.val, rfl⟩, by
    rw [rationalNorm_castVec, z.val.property.1]
    simp only [Int.cast_natCast],
    (primitiveIn_standard_castVec_iff z.val.val).mpr z.val.property.2, z.property⟩

theorem sumsOutsideCast_bijective (N : Submodule ℤ RatVec) (n : ℕ) :
    Function.Bijective (sumsOutsideCast N n) := by
  constructor
  · intro x y h
    apply Subtype.ext
    apply Subtype.ext
    exact castVec_injective (congrArg Subtype.val h)
  · rintro ⟨x, ⟨v, rfl⟩, hQ, hprim, hnot⟩
    have hvQ : vectorNorm v = (n : ℤ) := by
      rw [rationalNorm_castVec] at hQ
      exact_mod_cast hQ
    exact ⟨⟨⟨v, hvQ, (primitiveIn_standard_castVec_iff v).mp hprim⟩, hnot⟩, rfl⟩

def sumsOutsideCastEquiv (N : Submodule ℤ RatVec) (n : ℕ) :
    {z : PrimitiveVectorShell n // castVec z.val ∉ N} ≃
      OutsidePrimitiveShell N standard rationalNorm (n : ℚ) :=
  Equiv.ofBijective (sumsOutsideCast N n) (sumsOutsideCast_bijective N n)

def sumsZeroInsideEquiv (p : ℕ) [Fact p.Prime] (hp2 : p ≠ 2)
    (P : StandardConic (ZMod p)) (n : ℕ) :
    InsidePrimitiveZeroShell standard (family p hp2 P) p rationalNorm (n : ℚ) ≃
      SumsStandardInside (family p hp2 P) n :=
  Equiv.subtypeEquivRight (fun x => by
    constructor
    · rintro ⟨hxL, hxN, hxQ, hprimL, hnot⟩
      refine ⟨hxL, hxN, hxQ, hprimL, ?_⟩
      exact (inside_primitive_iff_not_divisible standard (family p hp2 P)
        (familyMidpoint p hp2 P) p Fact.out (familyMidpoint_le_standard p hp2 P)
        (familyMidpoint_le_family p hp2 P) (family_p_standard p hp2 P)
        (family_p_neighbor p hp2 P) x
        ((family_standard_inf p hp2 P).le ⟨hxL, hxN⟩) hprimL).mpr hnot
    · rintro ⟨hxL, hxN, hxQ, hprimL, hprimN⟩
      exact ⟨hxL, hxN, hxQ, hprimL, hprimN p Fact.out⟩)

theorem sums_inside_nondiv_standard_primitive
    (p m : ℕ) [Fact p.Prime] (hp2 : p ≠ 2) (hpm : ¬ p ∣ m)
    (P : StandardConic (ZMod p)) (x : RatVec)
    (hxL : x ∈ standard) (hxN : x ∈ family p hp2 P)
    (hxQ : rationalNorm x = ((3 * m ^ 2 : ℕ) : ℚ))
    (hx : PrimitiveIn (family p hp2 P) x) : PrimitiveIn standard x := by
  have hnot : ¬ DivisibleIn standard p x :=
    not_divisibleIn_of_norm_three_mul_sq standard p m Fact.out hpm rationalNorm
      (rationalNorm_prime_smul p) (by
        rintro y ⟨z, rfl⟩
        exact ⟨vectorNorm z, rationalNorm_castVec z⟩) x hxQ
  rcases inside_primitive_cases standard (family p hp2 P) (familyMidpoint p hp2 P)
    p Fact.out (familyMidpoint_le_standard p hp2 P) (familyMidpoint_le_family p hp2 P)
    (family_standard_inf p hp2 P).le (family_p_standard p hp2 P)
    (family_p_neighbor p hp2 P) x hxL hxN hx with h | ⟨z, hz, _, heq, _⟩
  · exact h
  · exact False.elim (hnot ⟨z, hz, heq.symm⟩)

def sumsNondivInsideEquiv
    (p m : ℕ) [Fact p.Prime] (hp2 : p ≠ 2) (hpm : ¬ p ∣ m)
    (P : StandardConic (ZMod p)) :
    InsidePrimitiveShell standard (family p hp2 P) rationalNorm ((3 * m ^ 2 : ℕ) : ℚ) ≃
      SumsStandardInside (family p hp2 P) (3 * m ^ 2) :=
  Equiv.subtypeEquivRight (fun x => by
    constructor
    · rintro ⟨hxL, hxN, hxQ, hx⟩
      exact ⟨hxL, hxN, hxQ,
        sums_inside_nondiv_standard_primitive p m hp2 hpm P x hxL hxN hxQ hx, hx⟩
    · rintro ⟨hxL, hxN, hxQ, _, hx⟩
      exact ⟨hxL, hxN, hxQ, hx⟩)

theorem sums_family_shell_finite (p : ℕ) [Fact p.Prime] (hp2 : p ≠ 2)
    (P : StandardConic (ZMod p)) (n : ℕ) :
    Finite (AmbientPrimitiveShell (family p hp2 P) rationalNorm (n : ℚ)) :=
  actual_neighbor_shell_finite p Fact.out (normalizedRepresentative p hp2 P)
    ((reduceVec_ne_zero_iff p _).mp (normalizedRepresentative_ne_zero p hp2 P))
    (normalizedRepresentative_norm p hp2 P) n

theorem inside_family_card_of_not_dvd
    (p m : ℕ) [Fact p.Prime] (hp2 : p ≠ 2) (hpm : ¬ p ∣ m) :
    (Nat.card (Σ P : StandardConic (ZMod p),
      InsidePrimitiveShell standard (family p hp2 P) rationalNorm
        ((3 * m ^ 2 : ℕ) : ℚ)) : ℤ) =
      (A354766Research.residueCharacter p + 1) *
        (A354766.r3PrimitiveFinite (3 * m ^ 2) : ℤ) := by
  classical
  letI (P : StandardConic (ZMod p)) :
      Finite (AmbientPrimitiveShell (family p hp2 P) rationalNorm
        ((3 * m ^ 2 : ℕ) : ℚ)) := sums_family_shell_finite p hp2 P _
  have h := sigma_card_from_constant_fibers
    (fun P : StandardConic (ZMod p) =>
      InsidePrimitiveShell standard (family p hp2 P) rationalNorm ((3 * m ^ 2 : ℕ) : ℚ))
    (fun P (z : PrimitiveVectorShell (3 * m ^ 2)) =>
      castVec z.val ∈ family p hp2 P ∧ PrimitiveIn (family p hp2 P) (castVec z.val))
    (A354766Research.residueCharacter p + 1)
    (fun P => Nat.card_congr ((sumsNondivInsideEquiv p m hp2 hpm P).trans
      (sumsInsideCastEquiv (family p hp2 P) _).symm))
    (fun z => family_inside_zero_nondiv_card_at_level p m hp2 hpm z.val
      z.property.2 z.property.1)
  simpa only [primitiveVectorShell_card] using h

theorem sums_zero_family_card_of_dvd
    (p m : ℕ) [Fact p.Prime] (hp2 : p ≠ 2) (hpm : p ∣ m) :
    (Nat.card (Σ P : StandardConic (ZMod p),
      InsidePrimitiveZeroShell standard (family p hp2 P) p rationalNorm
        ((3 * m ^ 2 : ℕ) : ℚ)) : ℤ) = 0 := by
  classical
  letI : Finite (AmbientPrimitiveShell standard rationalNorm ((3 * m ^ 2 : ℕ) : ℚ)) :=
    sums_standard_shell_finite _
  have h := sigma_card_from_constant_fibers
    (fun P : StandardConic (ZMod p) =>
      InsidePrimitiveZeroShell standard (family p hp2 P) p rationalNorm
        ((3 * m ^ 2 : ℕ) : ℚ))
    (fun P (z : PrimitiveVectorShell (3 * m ^ 2)) =>
      castVec z.val ∈ family p hp2 P ∧ PrimitiveIn (family p hp2 P) (castVec z.val))
    0
    (fun P => Nat.card_congr ((sumsZeroInsideEquiv p hp2 P _).trans
      (sumsInsideCastEquiv (family p hp2 P) _).symm))
    (fun z => by exact_mod_cast
      family_inside_zero_div_card p m hp2 hpm z.val z.property.2 z.property.1)
  simpa only [zero_mul] using h

theorem sums_outside_reverse_family_card
    (p k : ℕ) [Fact p.Prime] (hp2 : p ≠ 2) :
    (Nat.card (Σ P : StandardConic (ZMod p),
      OutsidePrimitiveShell (family p hp2 P) standard rationalNorm
        ((3 * k ^ 2 : ℕ) : ℚ)) : ℤ) =
      ((p : ℤ) - (if p ∣ k then 0 else A354766Research.residueCharacter p)) *
        (A354766.r3PrimitiveFinite (3 * k ^ 2) : ℤ) := by
  classical
  letI : Finite (AmbientPrimitiveShell standard rationalNorm ((3 * k ^ 2 : ℕ) : ℚ)) :=
    sums_standard_shell_finite _
  have h := sigma_card_from_constant_fibers
    (fun P : StandardConic (ZMod p) =>
      OutsidePrimitiveShell (family p hp2 P) standard rationalNorm ((3 * k ^ 2 : ℕ) : ℚ))
    (fun P (z : PrimitiveVectorShell (3 * k ^ 2)) => castVec z.val ∉ family p hp2 P)
    ((p : ℤ) - (if p ∣ k then 0 else A354766Research.residueCharacter p))
    (fun P => Nat.card_congr (sumsOutsideCastEquiv (family p hp2 P) _).symm)
    (fun z => by
      let e := insideOneFiberEquiv standard (family p hp2) (familyMidpoint p hp2)
        p Fact.out (familyMidpoint_le_standard p hp2) (familyMidpoint_le_family p hp2)
        (family_p_standard p hp2) (family_p_neighbor p hp2)
        (prime_smul_ratVec_injective p Fact.out) (castVec z.val) ⟨z.val, rfl⟩
        ((primitiveIn_standard_castVec_iff z.val).mpr z.property.2)
      rw [← Nat.card_congr e]
      simpa only [castVec_smul] using
        family_inside_one_card_at_level p k hp2 z.val z.property.2 z.property.1)
  simpa only [primitiveVectorShell_card] using h

theorem inside_family_card_of_dvd
    (p m : ℕ) [Fact p.Prime] (hp2 : p ≠ 2) (hpm : p ∣ m) :
    (Nat.card (Σ P : StandardConic (ZMod p),
      InsidePrimitiveShell standard (family p hp2 P) rationalNorm
        ((3 * m ^ 2 : ℕ) : ℚ)) : ℤ) =
      ((p : ℤ) - (if p ∣ m / p then 0 else A354766Research.residueCharacter p)) *
        (A354766.r3PrimitiveFinite (3 * (m / p) ^ 2) : ℤ) := by
  classical
  letI : Fintype (StandardConic (ZMod p)) := Fintype.ofFinite _
  have hm : p * (m / p) = m := by
    simpa only [Nat.mul_comm] using Nat.div_mul_cancel hpm
  have hmQ : (m : ℚ) = (p : ℚ) * ((m / p : ℕ) : ℚ) := by exact_mod_cast hm.symm
  have hlevel : ((3 * m ^ 2 : ℕ) : ℚ) =
      (p : ℚ) ^ 2 * ((3 * (m / p) ^ 2 : ℕ) : ℚ) := by
    push_cast
    rw [hmQ]
    ring
  letI : Finite (AmbientPrimitiveShell standard rationalNorm ((3 * m ^ 2 : ℕ) : ℚ)) :=
    sums_standard_shell_finite _
  letI : Finite (AmbientPrimitiveShell standard rationalNorm
      ((3 * (m / p) ^ 2 : ℕ) : ℚ)) := sums_standard_shell_finite _
  letI : Finite (AmbientPrimitiveShell standard rationalNorm
      ((p : ℚ) ^ 2 * ((3 * (m / p) ^ 2 : ℕ) : ℚ))) := by
    rw [← hlevel]
    infer_instance
  letI (P : StandardConic (ZMod p)) :
      Finite (AmbientPrimitiveShell (family p hp2 P) rationalNorm
        ((3 * m ^ 2 : ℕ) : ℚ)) := sums_family_shell_finite p hp2 P _
  have hpart (P : StandardConic (ZMod p)) :
      Nat.card (InsidePrimitiveShell standard (family p hp2 P) rationalNorm
        ((3 * m ^ 2 : ℕ) : ℚ)) =
      Nat.card (InsidePrimitiveZeroShell standard (family p hp2 P) p rationalNorm
        ((3 * m ^ 2 : ℕ) : ℚ)) +
      Nat.card (OutsidePrimitiveShell (family p hp2 P) standard rationalNorm
        ((3 * (m / p) ^ 2 : ℕ) : ℚ)) := by
    rw [hlevel]
    exact insidePrimitiveShell_card_partition
      standard (family p hp2 P) (familyMidpoint p hp2 P) p Fact.out
      (familyMidpoint_le_standard p hp2 P) (familyMidpoint_le_family p hp2 P)
      (family_standard_inf p hp2 P).le (family_p_standard p hp2 P)
      (family_p_neighbor p hp2 P) (prime_smul_ratVec_injective p Fact.out)
      rationalNorm ((p : ℚ) ^ 2) ((3 * (m / p) ^ 2 : ℕ) : ℚ)
      (pow_ne_zero _ (Nat.cast_ne_zero.mpr (Fact.out : p.Prime).ne_zero))
      (rationalNorm_prime_smul p)
  have htotal :
      (Nat.card (Σ P : StandardConic (ZMod p), InsidePrimitiveShell standard (family p hp2 P)
        rationalNorm ((3 * m ^ 2 : ℕ) : ℚ)) : ℤ) =
      (Nat.card (Σ P : StandardConic (ZMod p), InsidePrimitiveZeroShell standard (family p hp2 P)
        p rationalNorm ((3 * m ^ 2 : ℕ) : ℚ)) : ℤ) +
      (Nat.card (Σ P : StandardConic (ZMod p), OutsidePrimitiveShell (family p hp2 P) standard
        rationalNorm ((3 * (m / p) ^ 2 : ℕ) : ℚ)) : ℤ) := by
    rw [Nat.card_sigma, Nat.card_sigma, Nat.card_sigma, Nat.cast_sum, Nat.cast_sum,
      Nat.cast_sum, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro P _
    exact_mod_cast hpart P
  rw [htotal, sums_zero_family_card_of_dvd p m hp2 hpm, zero_add,
    sums_outside_reverse_family_card]

end A354766Neighbors

#print axioms A354766Neighbors.sigma_card_from_constant_fibers
#print axioms A354766Neighbors.inside_family_card_of_not_dvd
#print axioms A354766Neighbors.inside_family_card_of_dvd
