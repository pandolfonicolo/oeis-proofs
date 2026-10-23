import A354766.PrimitiveResidue

/-! The actual exterior primitive-neighbor bijection and its global count. -/

noncomputable section

open scoped BigOperators

namespace A354766Neighbors

open A354766Research.Neighbor A354766Research.NeighborFamily
open A354766Research.IsotropicLines

abbrev DivisibleVectorFiber (N : Submodule ℤ RatVec) (p n : ℕ) :=
  {v : PrimitiveVectorShell n // DivisibleIn N p (castVec v.val)}

def scaledVectorCast (N : Submodule ℤ RatVec) (p n : ℕ) :
    DivisibleVectorFiber N p n → ScaledPrimitiveShell standard N p rationalNorm (n : ℚ) :=
  fun v => ⟨castVec v.val.val, ⟨v.val.val, rfl⟩, by
    rw [rationalNorm_castVec, v.val.property.1]
    simp,
    (primitiveIn_standard_castVec_iff v.val.val).mpr v.val.property.2,
    v.property⟩

theorem scaledVectorCast_bijective (N : Submodule ℤ RatVec) (p n : ℕ) :
    Function.Bijective (scaledVectorCast N p n) := by
  constructor
  · intro v w h
    apply Subtype.ext
    apply Subtype.ext
    exact castVec_injective (congrArg Subtype.val h)
  · intro y
    obtain ⟨v, hv⟩ := y.property.1
    have hQ : vectorNorm v = (n : ℤ) := by
      have hQ' : (vectorNorm v : ℚ) = (n : ℚ) := by
        rw [← rationalNorm_castVec, hv]
        exact y.property.2.1
      exact_mod_cast hQ'
    have hprim : vectorContent v = 1 :=
      (primitiveIn_standard_castVec_iff v).mp (by rw [hv]; exact y.property.2.2.1)
    refine ⟨⟨⟨v, hQ, hprim⟩, ?_⟩, ?_⟩
    · change DivisibleIn N p (castVec v)
      rw [hv]
      exact y.property.2.2.2
    · apply Subtype.ext
      exact hv

def standardScaledVectorEquiv (N : Submodule ℤ RatVec) (p n : ℕ) :
    ScaledPrimitiveShell standard N p rationalNorm (n : ℚ) ≃ DivisibleVectorFiber N p n :=
  (Equiv.ofBijective (scaledVectorCast N p n) (scaledVectorCast_bijective N p n)).symm

theorem divided_family_mem_iff (p : ℕ) [Fact p.Prime] (hp2 : p ≠ 2)
    (P : StandardConic (ZMod p)) (v : IntVec) :
    DivisibleIn (family p hp2 P) p (castVec v) ↔ liftVec p v ∈ family p hp2 P := by
  constructor
  · rintro ⟨y, hy, hpy⟩
    have heq : y = liftVec p v :=
      prime_smul_ratVec_injective p Fact.out
        (hpy.trans (p_smul_liftVec p (Fact.out : p.Prime).ne_zero v).symm)
    rwa [← heq]
  · intro hv
    exact ⟨liftVec p v, hv, p_smul_liftVec p (Fact.out : p.Prime).ne_zero v⟩

def primitiveResidueLine (p : ℕ) [Fact p.Prime] (m : ℕ)
    (v : PrimitiveVectorShell (3 * (p * m) ^ 2)) : StandardConic (ZMod p) := by
  have h := primitive_square_residue_isotropic p m v.val v.property.2 v.property.1
  exact ⟨Projectivization.mk (ZMod p) (reduceVec p v.val) h.1,
    reduceVec p v.val, h.1, rfl, h.2⟩

theorem divisible_family_iff_residue_label (p : ℕ) [Fact p.Prime] (hp2 : p ≠ 2)
    (m : ℕ) (P : StandardConic (ZMod p))
    (v : PrimitiveVectorShell (3 * (p * m) ^ 2)) :
    DivisibleIn (family p hp2 P) p (castVec v.val) ↔ primitiveResidueLine p m v = P := by
  have h := primitive_square_residue_isotropic p m v.val v.property.2 v.property.1
  have hQ : (p : ℤ) ^ 2 ∣ dot3 v.val v.val := by
    have hd : dot3 v.val v.val = vectorNorm v.val := by
      simp only [dot3, vectorNorm, pow_two]
    rw [hd, v.property.1]
    refine ⟨3 * (m : ℤ) ^ 2, ?_⟩
    push_cast
    ring
  rw [divided_family_mem_iff, exterior_mem_family_iff p hp2 P v.val h.1 hQ]
  change Projectivization.mk (ZMod p) (reduceVec p v.val) h.1 = P.val ↔
    primitiveResidueLine p m v = P
  constructor
  · intro heq
    apply Subtype.ext
    exact heq
  · intro heq
    exact congrArg Subtype.val heq

/-- Forgetting the unique projective label is a genuine bijection. -/
def projectiveLabelFiberEquiv (p : ℕ) [Fact p.Prime] (hp2 : p ≠ 2) (m : ℕ) :
    (Σ P : StandardConic (ZMod p), DivisibleVectorFiber (family p hp2 P) p
      (3 * (p * m) ^ 2)) ≃ PrimitiveVectorShell (3 * (p * m) ^ 2) := by
  apply Equiv.ofBijective (fun x => x.2.val)
  constructor
  · rintro ⟨P, v, hv⟩ ⟨Q, w, hw⟩ h
    change v = w at h
    cases h
    have hPQ : P = Q :=
      ((divisible_family_iff_residue_label p hp2 m P v).mp hv).symm.trans
        ((divisible_family_iff_residue_label p hp2 m Q v).mp hw)
    subst Q
    rfl
  · intro v
    exact ⟨⟨primitiveResidueLine p m v,
      ⟨v, (divisible_family_iff_residue_label p hp2 m (primitiveResidueLine p m v) v).mpr rfl⟩⟩,
      rfl⟩

theorem prime_square_level (p m : ℕ) :
    (p : ℚ) ^ 2 * (3 * (m : ℚ) ^ 2) = ((3 * (p * m) ^ 2 : ℕ) : ℚ) := by
  push_cast
  ring

def outsideFamilyScaleEquiv (p : ℕ) [Fact p.Prime] (hp2 : p ≠ 2) (m : ℕ)
    (P : StandardConic (ZMod p)) :
    OutsidePrimitiveShell standard (family p hp2 P) rationalNorm (3 * (m : ℚ) ^ 2) ≃
      ScaledPrimitiveShell standard (family p hp2 P) p rationalNorm
        ((3 * (p * m) ^ 2 : ℕ) : ℚ) := by
  have hscale : (p : ℚ) ^ 2 ≠ 0 :=
    pow_ne_zero 2 (Nat.cast_ne_zero.mpr (Fact.out : p.Prime).ne_zero)
  have e := outsidePrimitiveShellEquiv standard (family p hp2 P) (familyMidpoint p hp2 P)
    p Fact.out (familyMidpoint_le_standard p hp2 P) (familyMidpoint_le_family p hp2 P)
    (family_p_standard p hp2 P) (family_p_neighbor p hp2 P)
    (prime_smul_ratVec_injective p Fact.out) rationalNorm ((p : ℚ) ^ 2)
    (3 * (m : ℚ) ^ 2) hscale (rationalNorm_prime_smul p)
  simpa only [prime_square_level p m] using e

/-- Every primitive vector at the scaled norm appears at exactly one actual
neighbor, with inverse obtained by division by p. -/
def outside_family_equiv (p : ℕ) [Fact p.Prime] (hp2 : p ≠ 2) (m : ℕ) :
    (Σ P : StandardConic (ZMod p),
      OutsidePrimitiveShell standard (family p hp2 P) rationalNorm (3 * (m : ℚ) ^ 2)) ≃
        PrimitiveVectorShell (3 * (p * m) ^ 2) :=
  (Equiv.sigmaCongrRight fun P =>
    (outsideFamilyScaleEquiv p hp2 m P).trans
      (standardScaledVectorEquiv (family p hp2 P) p (3 * (p * m) ^ 2))).trans
    (projectiveLabelFiberEquiv p hp2 m)

theorem outside_family_card (p : ℕ) [Fact p.Prime] (hp2 : p ≠ 2) (m : ℕ) :
    Nat.card (Σ P : StandardConic (ZMod p),
      OutsidePrimitiveShell standard (family p hp2 P) rationalNorm (3 * (m : ℚ) ^ 2)) =
        A354766.r3PrimitiveFinite (3 * (p * m) ^ 2) :=
  (Nat.card_congr (outside_family_equiv p hp2 m)).trans
    (primitiveVectorShell_card (3 * (p * m) ^ 2))

theorem outside_family_sum_card (p : ℕ) [Fact p.Prime] (hp2 : p ≠ 2) (m : ℕ)
    [Fintype (StandardConic (ZMod p))] :
    (∑ P : StandardConic (ZMod p),
      Nat.card (OutsidePrimitiveShell standard (family p hp2 P) rationalNorm
        (3 * (m : ℚ) ^ 2))) = A354766.r3PrimitiveFinite (3 * (p * m) ^ 2) := by
  let S := Σ P : StandardConic (ZMod p),
    OutsidePrimitiveShell standard (family p hp2 P) rationalNorm (3 * (m : ℚ) ^ 2)
  letI : Finite S := Finite.of_equiv (PrimitiveVectorShell (3 * (p * m) ^ 2))
    (outside_family_equiv p hp2 m).symm
  haveI (P : StandardConic (ZMod p)) :
      Finite (OutsidePrimitiveShell standard (family p hp2 P) rationalNorm
        (3 * (m : ℚ) ^ 2)) :=
    Finite.of_injective (fun x => (⟨P, x⟩ : S)) (by intro x y h; cases h; rfl)
  rw [← Nat.card_sigma]
  exact outside_family_card p hp2 m

end A354766Neighbors

#print axioms A354766Neighbors.scaledVectorCast_bijective
#print axioms A354766Neighbors.divisible_family_iff_residue_label
#print axioms A354766Neighbors.outside_family_equiv
#print axioms A354766Neighbors.outside_family_card
#print axioms A354766Neighbors.outside_family_sum_card
