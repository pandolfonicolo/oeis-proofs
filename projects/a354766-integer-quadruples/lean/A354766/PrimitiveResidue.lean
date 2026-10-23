import A354766.PrimitiveNeighborAlgebra
import A354766.PrimitiveVectorModel
import A354766.NormalizedNeighborFamily

/-! Primitive standard vectors and their nonzero projective residues. -/

namespace A354766Neighbors

open A354766Research.Neighbor A354766Research.NeighborFamily
open A354766Research.IsotropicLines

theorem divisibleIn_standard_castVec_iff (q : ℕ) (v : IntVec) :
    DivisibleIn standard q (castVec v) ↔ ∃ w : IntVec, (q : ℤ) • w = v := by
  constructor
  · rintro ⟨y, ⟨w, rfl⟩, hwy⟩
    refine ⟨w, castVec_injective ?_⟩
    rw [castVec_smul]
    exact hwy
  · rintro ⟨w, hwy⟩
    refine ⟨castVec w, ⟨w, rfl⟩, ?_⟩
    rw [← castVec_smul, hwy]

theorem divisibleIn_standard_castVec_iff_coordinates (q : ℕ) (v : IntVec) :
    DivisibleIn standard q (castVec v) ↔
      (q : ℤ) ∣ v 0 ∧ (q : ℤ) ∣ v 1 ∧ (q : ℤ) ∣ v 2 := by
  rw [divisibleIn_standard_castVec_iff, scalar_divisibility_iff_coordinates]

theorem primitiveIn_standard_castVec_iff (v : IntVec) :
    PrimitiveIn standard (castVec v) ↔ vectorContent v = 1 := by
  rw [vectorContent_eq_one_iff_primitive]
  simp only [PrimitiveIn, divisibleIn_standard_castVec_iff]

theorem primitive_reduction_ne_zero (p : ℕ) (hp : p.Prime)
    (v : IntVec) (hv : vectorContent v = 1) : reduceVec p v ≠ 0 := by
  apply (reduceVec_ne_zero_iff p v).mpr
  by_contra hn
  have hd (i : Fin 3) : (p : ℤ) ∣ v i := by
    by_contra hi
    exact hn ⟨i, hi⟩
  exact ((vectorContent_eq_one_iff v).mp hv p hp) ⟨hd 0, hd 1, hd 2⟩

theorem primitiveIn_standard_reduction_ne_zero (p : ℕ) (hp : p.Prime)
    (v : IntVec) (hv : PrimitiveIn standard (castVec v)) : reduceVec p v ≠ 0 :=
  primitive_reduction_ne_zero p hp v ((primitiveIn_standard_castVec_iff v).mp hv)

/-- A vector of norm 3*(p*m)^2 is isotropic modulo p; primitivity makes its
residue a genuine projective point rather than the zero vector. -/
theorem primitive_square_residue_isotropic (p : ℕ) [Fact p.Prime] (m : ℕ)
    (v : IntVec) (hv : vectorContent v = 1)
    (hQ : vectorNorm v = ((3 * (p * m) ^ 2 : ℕ) : ℤ)) :
    reduceVec p v ≠ 0 ∧ standardNorm (ZMod p) (reduceVec p v) = 0 := by
  refine ⟨primitive_reduction_ne_zero p Fact.out v hv, ?_⟩
  have hdot : dot3 v v = ((3 * (p * m) ^ 2 : ℕ) : ℤ) := by
    simpa only [dot3, vectorNorm, pow_two] using hQ
  rw [reduceVec_norm, hdot]
  simp

theorem primitiveIn_standard_square_residue_isotropic (p : ℕ) [Fact p.Prime] (m : ℕ)
    (v : IntVec) (hv : PrimitiveIn standard (castVec v))
    (hQ : vectorNorm v = ((3 * (p * m) ^ 2 : ℕ) : ℤ)) :
    reduceVec p v ≠ 0 ∧ standardNorm (ZMod p) (reduceVec p v) = 0 :=
  primitive_square_residue_isotropic p m v ((primitiveIn_standard_castVec_iff v).mp hv) hQ

def rationalNorm (x : RatVec) : ℚ := dot3 x x

theorem rationalNorm_prime_smul (p : ℕ) (x : RatVec) :
    rationalNorm ((p : ℤ) • x) = (p : ℚ) ^ 2 * rationalNorm x := by
  simp only [rationalNorm, dot3, Pi.smul_apply, zsmul_eq_mul, Int.cast_natCast, Pi.mul_apply, Pi.intCast_def, Pi.natCast_def]
  ring

theorem rationalNorm_castVec (v : IntVec) :
    rationalNorm (castVec v) = (vectorNorm v : ℚ) := by
  simp [rationalNorm, dot3, castVec, vectorNorm, pow_two]

theorem prime_smul_ratVec_injective (p : ℕ) (hp : p.Prime) :
    Function.Injective (fun z : RatVec => (p : ℤ) • z) := by
  intro x y h
  funext i
  have hi := congrFun h i
  change (p : ℚ) * x i = (p : ℚ) * y i at hi
  exact mul_left_cancel₀ (Nat.cast_ne_zero.mpr hp.ne_zero) hi

noncomputable def familyMidpoint (p : ℕ) [Fact p.Prime] (hp2 : p ≠ 2)
    (P : StandardConic (ZMod p)) : Submodule ℤ RatVec :=
  midpoint p (normalizedRepresentative p hp2 P)

theorem familyMidpoint_le_standard (p : ℕ) [Fact p.Prime] (hp2 : p ≠ 2)
    (P : StandardConic (ZMod p)) : familyMidpoint p hp2 P ≤ standard :=
  midpoint_le_standard p _

theorem familyMidpoint_le_family (p : ℕ) [Fact p.Prime] (hp2 : p ≠ 2)
    (P : StandardConic (ZMod p)) : familyMidpoint p hp2 P ≤ family p hp2 P :=
  midpoint_le_neighbor p _

theorem family_standard_inf (p : ℕ) [Fact p.Prime] (hp2 : p ≠ 2)
    (P : StandardConic (ZMod p)) :
    standard ⊓ family p hp2 P = familyMidpoint p hp2 P := by
  apply standard_inf_neighbor p Fact.out
  · exact (reduceVec_ne_zero_iff p _).mp (normalizedRepresentative_ne_zero p hp2 P)
  · exact (dvd_pow_self (p : ℤ) (by decide : (2 : ℕ) ≠ 0)).trans
      (normalizedRepresentative_norm p hp2 P)

theorem family_p_standard (p : ℕ) [Fact p.Prime] (hp2 : p ≠ 2)
    (P : StandardConic (ZMod p)) (z : RatVec) (hz : z ∈ standard) :
    (p : ℤ) • z ∈ familyMidpoint p hp2 P :=
  p_smul_standard_mem_midpoint p _ z hz

theorem family_p_neighbor (p : ℕ) [Fact p.Prime] (hp2 : p ≠ 2)
    (P : StandardConic (ZMod p)) (z : RatVec) (hz : z ∈ family p hp2 P) :
    (p : ℤ) • z ∈ familyMidpoint p hp2 P := by
  apply p_smul_neighbor_mem_midpoint p (Fact.out : p.Prime).ne_zero _ _ z hz
  exact (dvd_pow_self (p : ℤ) (by decide : (2 : ℕ) ≠ 0)).trans
    (normalizedRepresentative_norm p hp2 P)

theorem family_norm_integral (p : ℕ) [Fact p.Prime] (hp2 : p ≠ 2)
    (P : StandardConic (ZMod p)) (z : RatVec) (hz : z ∈ family p hp2 P) :
    ∃ k : ℤ, rationalNorm z = (k : ℚ) :=
  neighbor_integral p (Fact.out : p.Prime).ne_zero _
    (normalizedRepresentative_norm p hp2 P) z z hz hz


end A354766Neighbors

#print axioms A354766Neighbors.divisibleIn_standard_castVec_iff_coordinates
#print axioms A354766Neighbors.primitiveIn_standard_castVec_iff
#print axioms A354766Neighbors.primitive_reduction_ne_zero
#print axioms A354766Neighbors.primitive_square_residue_isotropic

#print axioms A354766Neighbors.rationalNorm_prime_smul
#print axioms A354766Neighbors.family_standard_inf
#print axioms A354766Neighbors.family_norm_integral
