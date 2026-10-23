import Mathlib.Algebra.Module.ZLattice.Covolume

/-!
Topological and covolume consequences of the explicit neighbor inclusions.
The quotient indices themselves are supplied by the concrete construction.
-/

noncomputable section

open MeasureTheory

namespace A354766Neighbors

section Topological

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem natReal_smul_eq_natInt_smul (p : ℕ) (x : E) :
    (p : ℝ) • x = (p : ℤ) • x := by
  simpa only [Int.cast_natCast] using (Int.cast_smul_eq_zsmul ℝ (p : ℤ) x)

theorem discrete_of_prime_multiple_inclusion
    (L N : Submodule ℤ E) [DiscreteTopology L]
    (p : ℕ) (hp : p ≠ 0)
    (hpN : ∀ x ∈ N, (p : ℤ) • x ∈ L) : DiscreteTopology N := by
  have hpR : (p : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hp
  let f : N → L := fun x => ⟨(p : ℝ) • (x : E), by
    rw [natReal_smul_eq_natInt_smul]
    exact hpN x.1 x.property⟩
  have hf : Continuous f := by
    exact (continuous_const.smul continuous_subtype_val).subtype_mk _
  have hinj : Function.Injective f := by
    intro x y h
    apply Subtype.ext
    have hval := congrArg (fun z : L => (z : E)) h
    change (p : ℝ) • (x : E) = (p : ℝ) • (y : E) at hval
    calc
      (x : E) = (p : ℝ)⁻¹ • ((p : ℝ) • (x : E)) := by simp [smul_smul, hpR]
      _ = (p : ℝ)⁻¹ • ((p : ℝ) • (y : E)) := by rw [hval]
      _ = (y : E) := by simp [smul_smul, hpR]
  exact DiscreteTopology.of_continuous_injective hf hinj

theorem span_top_of_prime_multiple_inclusion
    (L N : Submodule ℤ E) [DiscreteTopology L] [IsZLattice ℝ L]
    (p : ℕ) (hp : p ≠ 0)
    (hpL : ∀ x ∈ L, (p : ℤ) • x ∈ N) :
    Submodule.span ℝ (N : Set E) = ⊤ := by
  have hpR : (p : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hp
  let S := Submodule.span ℝ (N : Set E)
  have hsub : (L : Set E) ⊆ S := by
    intro x hx
    have hpx : (p : ℝ) • x ∈ S := by
      rw [natReal_smul_eq_natInt_smul]
      exact Submodule.subset_span (hpL x hx)
    have h := S.smul_mem ((p : ℝ)⁻¹) hpx
    simpa [smul_smul, hpR] using h
  have hspan : Submodule.span ℝ (L : Set E) ≤ S := Submodule.span_le.mpr hsub
  rw [IsZLattice.span_top (K := ℝ)] at hspan
  exact top_unique hspan

theorem isZLattice_of_prime_multiple_inclusion
    (L N : Submodule ℤ E) [DiscreteTopology L] [IsZLattice ℝ L] [DiscreteTopology N]
    (p : ℕ) (hp : p ≠ 0)
    (hpL : ∀ x ∈ L, (p : ℤ) • x ∈ N) : IsZLattice ℝ N :=
  ⟨span_top_of_prime_multiple_inclusion L N p hp hpL⟩

end Topological

section Covolume

variable {E : Type*} [NormedAddCommGroup E]
  [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]

/-- Equal indices above a common full lattice force equal covolumes. -/
theorem covolume_eq_of_common_index
    (M L N : Submodule ℤ E)
    [DiscreteTopology M] [IsZLattice ℝ M]
    [DiscreteTopology L] [IsZLattice ℝ L]
    [DiscreteTopology N] [IsZLattice ℝ N]
    (hML : M ≤ L) (hMN : M ≤ N)
    (hindex : M.toAddSubgroup.relIndex L.toAddSubgroup =
      M.toAddSubgroup.relIndex N.toAddSubgroup) :
    ZLattice.covolume L = ZLattice.covolume N := by
  have hMLr := ZLattice.covolume_div_covolume_eq_relIndex' M L hML
  have hMNr := ZLattice.covolume_div_covolume_eq_relIndex' M N hMN
  have hratio : ZLattice.covolume M / ZLattice.covolume L =
      ZLattice.covolume M / ZLattice.covolume N := by
    rw [hMLr, hMNr, hindex]
  have hMpos := ZLattice.covolume_pos M volume
  have hLpos := ZLattice.covolume_pos L volume
  have hNpos := ZLattice.covolume_pos N volume
  have hmul := (div_eq_div_iff hLpos.ne' hNpos.ne').mp hratio
  exact (mul_left_cancel₀ hMpos.ne' hmul).symm

end Covolume
end A354766Neighbors

#print axioms A354766Neighbors.discrete_of_prime_multiple_inclusion
#print axioms A354766Neighbors.isZLattice_of_prime_multiple_inclusion
#print axioms A354766Neighbors.covolume_eq_of_common_index
