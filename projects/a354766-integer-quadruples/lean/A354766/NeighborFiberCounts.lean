import A354766.PrimitiveNeighborAlgebra
import A354766.IsotropicLines
import A354766.NormalizedNeighborFamily
import A354766.PrimitiveResidue
import A354766.CharacterScaling

/-!
# The concrete primitive-neighbor double count

The algebraic primitive-vector lemmas are in `PrimitiveNeighborAlgebra`.
This file connects the proved normalized projective neighbor family with the
finite conic counts and the norm-preserving integer shell model. No recurrence
or representation formula is assumed as an input.
-/

namespace A354766Neighbors

open A354766Research.Neighbor A354766Research.NeighborFamily
open A354766Research.IsotropicLines

noncomputable def familyMembershipEquiv (p : ℕ) [Fact p.Prime] (hp2 : p ≠ 2)
    (z : IntVec) :
    {P : StandardConic (ZMod p) // castVec z ∈ family p hp2 P} ≃
      StandardPerpConic (ZMod p) (reduceVec p z) :=
  Equiv.subtypeEquivRight (fun P => inside_mem_family_iff p hp2 P z)

theorem family_membership_card (p : ℕ) [Fact p.Prime] (hp2 : p ≠ 2)
    (z : IntVec) (hz : reduceVec p z ≠ 0) :
    (Nat.card {P : StandardConic (ZMod p) // castVec z ∈ family p hp2 P} : ℤ) =
      quadraticChar (ZMod p) (-standardNorm (ZMod p) (reduceVec p z)) + 1 := by
  rw [Nat.card_congr (familyMembershipEquiv p hp2 z)]
  exact card_standardPerpConic_zmod p hp2 (reduceVec p z) hz

/-- The exact content-p fiber, using the actual constructed projective family. -/
theorem family_inside_one_card (p : ℕ) [Fact p.Prime] (hp2 : p ≠ 2)
    (z : IntVec) (hz : vectorContent z = 1) :
    (Nat.card {P : StandardConic (ZMod p) //
      castVec ((p : ℤ) • z) ∈ family p hp2 P ∧
        PrimitiveIn (family p hp2 P) (castVec ((p : ℤ) • z))} : ℤ) =
      (p : ℤ) - quadraticChar (ZMod p) (-standardNorm (ZMod p) (reduceVec p z)) := by
  classical
  let N := family p hp2
  let M := familyMidpoint p hp2
  have hg := card_inside_one_fiber standard N M p (Fact.out : p.Prime)
    (familyMidpoint_le_standard p hp2) (familyMidpoint_le_family p hp2)
    (family_p_standard p hp2) (family_p_neighbor p hp2)
    (prime_smul_ratVec_injective p Fact.out) (castVec z) ⟨z, rfl⟩
    ((primitiveIn_standard_castVec_iff z).mpr hz)
  rw [← castVec_smul] at hg
  have hle : Nat.card {P : StandardConic (ZMod p) // castVec z ∈ N P} ≤
      Nat.card (StandardConic (ZMod p)) :=
    Nat.card_le_card_of_injective Subtype.val Subtype.val_injective
  have hsum : Nat.card {P : StandardConic (ZMod p) //
      castVec ((p : ℤ) • z) ∈ N P ∧ PrimitiveIn (N P) (castVec ((p : ℤ) • z))} +
      Nat.card {P : StandardConic (ZMod p) // castVec z ∈ N P} = p + 1 := by
    rw [hg, Nat.sub_add_cancel hle, card_standardConic_zmod p hp2]
  have hsumZ : (Nat.card {P : StandardConic (ZMod p) //
      castVec ((p : ℤ) • z) ∈ N P ∧ PrimitiveIn (N P) (castVec ((p : ℤ) • z))} : ℤ) +
      (Nat.card {P : StandardConic (ZMod p) // castVec z ∈ N P} : ℤ) = (p : ℤ) + 1 := by
    exact_mod_cast hsum
  have hm := family_membership_card p hp2 z (primitive_reduction_ne_zero p Fact.out z hz)
  change (Nat.card {P : StandardConic (ZMod p) //
      castVec ((p : ℤ) • z) ∈ N P ∧ PrimitiveIn (N P) (castVec ((p : ℤ) • z))} : ℤ) = _
  linear_combination hsumZ - hm

def isotropicPoint (F : Type*) [Field F] (x : Ternary F) (hx : x ≠ 0)
    (hQ : standardNorm F x = 0) : StandardConic F :=
  ⟨Projectivization.mk F x hx, x, hx, rfl, hQ⟩

theorem isotropicPoint_perp_self (F : Type*) [Field F] (x : Ternary F) (hx : x ≠ 0)
    (hQ : standardNorm F x = 0) :
    (isotropicPoint F x hx hQ).val.submodule ≤ (standardDot F x).ker := by
  change (Projectivization.mk F x hx).submodule ≤ (standardDot F x).ker
  rw [Projectivization.submodule_mk, Submodule.span_singleton_le_iff_mem, LinearMap.mem_ker]
  simpa only [standardDot, standardNorm, LinearMap.coe_mk, AddHom.coe_mk, pow_two] using hQ

theorem unique_isotropic_perp (p : ℕ) [Fact p.Prime] (hp2 : p ≠ 2)
    (x : Ternary (ZMod p)) (hx : x ≠ 0) (hQ : standardNorm (ZMod p) x = 0)
    (P : StandardConic (ZMod p))
    (hP : P.val.submodule ≤ (standardDot (ZMod p) x).ker) :
    P.val = Projectivization.mk (ZMod p) x hx := by
  classical
  have hcZ := card_standardPerpConic_zmod p hp2 x hx
  rw [hQ, neg_zero, quadraticChar_zero, zero_add] at hcZ
  have hc : Nat.card (StandardPerpConic (ZMod p) x) = 1 := by exact_mod_cast hcZ
  have hs : Subsingleton (StandardPerpConic (ZMod p) x) :=
    (Nat.card_eq_one_iff_unique.mp hc).1
  have he := hs.elim (⟨P, hP⟩ : StandardPerpConic (ZMod p) x)
    ⟨isotropicPoint (ZMod p) x hx hQ, isotropicPoint_perp_self (ZMod p) x hx hQ⟩
  exact congrArg (fun q : StandardPerpConic (ZMod p) x => q.val.val) he

theorem dot3_int_eq_vectorNorm (z : IntVec) : dot3 z z = vectorNorm z := by
  simp only [dot3, vectorNorm, pow_two]

/-- At level 3*m² with p|m, an inside standard-primitive vector is never
primitive in a neighbor. Its unique perpendicular isotropic line forces
actual p-division, using the proved exterior membership theorem at norm p². -/
theorem family_inside_zero_div_not_primitive
    (p m : ℕ) [Fact p.Prime] (hp2 : p ≠ 2) (hpm : p ∣ m)
    (z : IntVec) (hz : vectorContent z = 1)
    (hzQ : vectorNorm z = ((3 * m ^ 2 : ℕ) : ℤ))
    (P : StandardConic (ZMod p)) (hzN : castVec z ∈ family p hp2 P) :
    ¬ PrimitiveIn (family p hp2 P) (castVec z) := by
  have hred := primitive_reduction_ne_zero p Fact.out z hz
  have hQp2 : (p : ℤ) ^ 2 ∣ dot3 z z := by
    obtain ⟨k, hk⟩ := hpm
    rw [dot3_int_eq_vectorNorm, hzQ, hk]
    refine ⟨3 * (k : ℤ) ^ 2, ?_⟩
    push_cast
    ring
  have hQp : (p : ℤ) ∣ dot3 z z :=
    (dvd_pow_self (p : ℤ) (by decide : (2 : ℕ) ≠ 0)).trans hQp2
  have hQred : standardNorm (ZMod p) (reduceVec p z) = 0 := by
    rw [reduceVec_norm]
    exact (ZMod.intCast_zmod_eq_zero_iff_dvd (dot3 z z) p).mpr hQp
  have hproj : P.val = Projectivization.mk (ZMod p) (reduceVec p z) hred :=
    unique_isotropic_perp p hp2 (reduceVec p z) hred hQred P
      ((inside_mem_family_iff p hp2 P z).mp hzN)
  have hyN : liftVec p z ∈ family p hp2 P :=
    (exterior_mem_family_iff p hp2 P z hred hQp2).mpr hproj.symm
  intro hprim
  exact hprim p Fact.out ⟨liftVec p z, hyN, p_smul_liftVec p (Fact.out : p.Prime).ne_zero z⟩

theorem family_inside_zero_div_card
    (p m : ℕ) [Fact p.Prime] (hp2 : p ≠ 2) (hpm : p ∣ m)
    (z : IntVec) (hz : vectorContent z = 1)
    (hzQ : vectorNorm z = ((3 * m ^ 2 : ℕ) : ℤ)) :
    Nat.card {P : StandardConic (ZMod p) // castVec z ∈ family p hp2 P ∧
      PrimitiveIn (family p hp2 P) (castVec z)} = 0 := by
  letI : IsEmpty {P : StandardConic (ZMod p) // castVec z ∈ family p hp2 P ∧
      PrimitiveIn (family p hp2 P) (castVec z)} :=
    ⟨fun P => family_inside_zero_div_not_primitive p m hp2 hpm z hz hzQ P.val
      P.property.1 P.property.2⟩
  exact Nat.card_of_isEmpty

/-- The content-one fiber for p∤m, including p=3. -/
theorem family_inside_zero_nondiv_card
    (p m : ℕ) [Fact p.Prime] (hp2 : p ≠ 2) (hpm : ¬ p ∣ m)
    (z : IntVec) (hz : vectorContent z = 1)
    (hzQ : vectorNorm z = ((3 * m ^ 2 : ℕ) : ℤ)) :
    (Nat.card {P : StandardConic (ZMod p) // castVec z ∈ family p hp2 P ∧
      PrimitiveIn (family p hp2 P) (castVec z)} : ℤ) =
      quadraticChar (ZMod p) (-standardNorm (ZMod p) (reduceVec p z)) + 1 := by
  have hzQrat : rationalNorm (castVec z) = ((3 * m ^ 2 : ℕ) : ℚ) := by
    rw [rationalNorm_castVec, hzQ]
    simp only [Int.cast_natCast]
  let e := insideZeroNondivFiberEquiv standard (family p hp2) (familyMidpoint p hp2)
    p m (Fact.out : p.Prime) hpm (familyMidpoint_le_standard p hp2)
    (familyMidpoint_le_family p hp2) (fun P => (family_standard_inf p hp2 P).le)
    (family_p_standard p hp2) (family_p_neighbor p hp2)
    rationalNorm (rationalNorm_prime_smul p) (family_norm_integral p hp2)
    (castVec z) ⟨z, rfl⟩ ((primitiveIn_standard_castVec_iff z).mpr hz) hzQrat
  rw [Nat.card_congr e]
  exact family_membership_card p hp2 z (primitive_reduction_ne_zero p Fact.out z hz)

theorem character_of_vector_norm (p k : ℕ) [Fact p.Prime]
    (z : IntVec) (hzQ : vectorNorm z = ((3 * k ^ 2 : ℕ) : ℤ)) :
    quadraticChar (ZMod p) (-standardNorm (ZMod p) (reduceVec p z)) =
      legendreSym p (-3 * (k : ℤ) ^ 2) := by
  have harg : -standardNorm (ZMod p) (reduceVec p z) =
      ((-3 * (k : ℤ) ^ 2 : ℤ) : ZMod p) := by
    rw [reduceVec_norm, dot3_int_eq_vectorNorm, hzQ]
    push_cast
    ring
  exact congrArg (quadraticChar (ZMod p)) harg

theorem family_inside_one_card_at_level (p k : ℕ) [Fact p.Prime] (hp2 : p ≠ 2)
    (z : IntVec) (hz : vectorContent z = 1)
    (hzQ : vectorNorm z = ((3 * k ^ 2 : ℕ) : ℤ)) :
    (Nat.card {P : StandardConic (ZMod p) //
      castVec ((p : ℤ) • z) ∈ family p hp2 P ∧
        PrimitiveIn (family p hp2 P) (castVec ((p : ℤ) • z))} : ℤ) =
      (p : ℤ) - (if p ∣ k then 0 else A354766Research.residueCharacter p) := by
  rw [family_inside_one_card p hp2 z hz, character_of_vector_norm p k z hzQ,
    A354766Research.legendre_neg_three_mul_square p hp2 k]

theorem family_inside_zero_nondiv_card_at_level
    (p m : ℕ) [Fact p.Prime] (hp2 : p ≠ 2) (hpm : ¬ p ∣ m)
    (z : IntVec) (hz : vectorContent z = 1)
    (hzQ : vectorNorm z = ((3 * m ^ 2 : ℕ) : ℤ)) :
    (Nat.card {P : StandardConic (ZMod p) // castVec z ∈ family p hp2 P ∧
      PrimitiveIn (family p hp2 P) (castVec z)} : ℤ) =
      A354766Research.residueCharacter p + 1 := by
  rw [family_inside_zero_nondiv_card p m hp2 hpm z hz hzQ,
    character_of_vector_norm p m z hzQ,
    A354766Research.legendre_neg_three_mul_square p hp2 m, if_neg hpm]

end A354766Neighbors

#print axioms A354766Neighbors.family_inside_one_card
#print axioms A354766Neighbors.family_inside_zero_div_card
#print axioms A354766Neighbors.family_inside_one_card_at_level
#print axioms A354766Neighbors.family_inside_zero_nondiv_card_at_level

