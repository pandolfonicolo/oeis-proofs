import Mathlib.Algebra.Module.ZLattice.Covolume
import Mathlib.MeasureTheory.Group.GeometryOfNumbers
import Mathlib.MeasureTheory.Measure.Lebesgue.VolumeOfBalls
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.LinearAlgebra.Basis.Prod
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Lean.Elab.Tactic.Omega

/-!
The short-vector step for integral unimodular lattices of rank at most three.
The covolume and integrality hypotheses below are the actual hypotheses of
the small-lattice theorem; no lattice classification is assumed.
-/

noncomputable section

open MeasureTheory Metric Module Set
open scoped RealInnerProductSpace

namespace SmallIntegralLattices

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

/-- Integrality of every lattice inner product, including squared norms. -/
def Integral (L : Submodule ℤ E) : Prop :=
  ∀ x ∈ L, ∀ y ∈ L, ∃ z : ℤ, ⟪x, y⟫ = (z : ℝ)

private theorem ball_four_thirds_large
    (hr : 1 ≤ finrank ℝ E) (hr' : finrank ℝ E ≤ 3) :
    (2 : ENNReal) ^ finrank ℝ E < volume (ball (0 : E) (4 / 3 : ℝ)) := by
  haveI : Nontrivial E := Module.nontrivial_of_finrank_pos (R := ℝ) (by omega)
  have hcases : finrank ℝ E = 1 ∨ finrank ℝ E = 2 ∨ finrank ℝ E = 3 := by omega
  rcases hcases with hd | hd | hd
  · rw [InnerProductSpace.volume_ball_of_dim_odd (k := 0) (by omega)]
    apply (ENNReal.toReal_lt_toReal (by finiteness) (by finiteness)).mp
    simp only [ENNReal.toReal_pow, ENNReal.toReal_mul, ENNReal.toReal_ofNat]
    rw [ENNReal.toReal_ofReal (by norm_num), ENNReal.toReal_ofReal (by positivity)]
    norm_num [hd]
  · rw [InnerProductSpace.volume_ball_of_dim_even (k := 1) (by omega)]
    apply (ENNReal.toReal_lt_toReal (by finiteness) (by finiteness)).mp
    simp only [ENNReal.toReal_pow, ENNReal.toReal_mul, ENNReal.toReal_ofNat]
    rw [ENNReal.toReal_ofReal (by norm_num), ENNReal.toReal_ofReal (by positivity)]
    norm_num [hd]
    nlinarith [Real.pi_gt_three]
  · rw [InnerProductSpace.volume_ball_of_dim_odd (k := 1) (by omega)]
    apply (ENNReal.toReal_lt_toReal (by finiteness) (by finiteness)).mp
    simp only [ENNReal.toReal_pow, ENNReal.toReal_mul, ENNReal.toReal_ofNat]
    rw [ENNReal.toReal_ofReal (by norm_num), ENNReal.toReal_ofReal (by positivity)]
    norm_num [hd]
    nlinarith [Real.pi_gt_three]

/-- A genuine Minkowski consequence: every integral covolume-one lattice
of rank one, two, or three contains a vector of squared norm one. -/
theorem exists_unit_vector (L : Submodule ℤ E) [DiscreteTopology L] [IsZLattice ℝ L]
    (hL : Integral L) (hvol : ZLattice.covolume L = 1)
    (hr : 1 ≤ finrank ℝ E) (hr' : finrank ℝ E ≤ 3) :
    ∃ u : E, u ∈ L ∧ ⟪u, u⟫ = 1 := by
  let b := Module.Free.chooseBasis ℤ L
  let F := ZSpan.fundamentalDomain (b.ofZLatticeBasis ℝ)
  have hfund : IsAddFundamentalDomain L F volume :=
    ZLattice.isAddFundamentalDomain b volume
  have hFreal : volume.real F = 1 := by
    rw [← ZLattice.covolume_eq_measure_fundamentalDomain L volume hfund]
    exact hvol
  have hFfinite : volume F ≠ ⊤ := by
    exact ne_of_lt ((ZSpan.fundamentalDomain_isBounded _).measure_lt_top)
  have hF : volume F = 1 := by
    apply (ENNReal.toReal_eq_toReal_iff' hFfinite ENNReal.one_ne_top).mp
    simpa only [ENNReal.toReal_one] using hFreal
  have hlarge : volume F * 2 ^ finrank ℝ E < volume (ball (0 : E) (4 / 3 : ℝ)) := by
    rw [hF, one_mul]
    exact ball_four_thirds_large hr hr'
  letI : Countable L.toAddSubgroup := inferInstanceAs (Countable L)
  obtain ⟨u, hu0, hu⟩ :=
    exists_ne_zero_mem_lattice_of_measure_mul_two_pow_lt_measure
      (L := L.toAddSubgroup) hfund
      (fun x hx => by simpa only [mem_ball_zero_iff, norm_neg] using hx)
      (convex_ball (0 : E) (4 / 3 : ℝ)) hlarge
  have hu0' : (u : E) ≠ 0 := by
    intro h
    exact hu0 (Subtype.ext h)
  have hnorm : ‖(u : E)‖ < (4 / 3 : ℝ) := by
    simpa only [mem_ball_zero_iff] using hu
  obtain ⟨z, hz⟩ := hL (u : E) u.property (u : E) u.property
  have hzpos : (0 : ℝ) < (z : ℝ) := by
    rw [← hz, real_inner_self_eq_norm_sq]
    exact sq_pos_of_pos (norm_pos_iff.mpr hu0')
  have hzlt : (z : ℝ) < 2 := by
    rw [← hz, real_inner_self_eq_norm_sq]
    nlinarith [norm_nonneg (u : E)]
  have hzpos' : (0 : ℤ) < z := by exact_mod_cast hzpos
  have hzlt' : z < (2 : ℤ) := by exact_mod_cast hzlt
  have hz1 : z = 1 := by omega
  exact ⟨u, u.property, by simpa only [hz1, Int.cast_one] using hz⟩

/-- Subtracting the integral coordinate along a unit lattice vector stays
inside the lattice and is orthogonal to that vector. -/
theorem exists_integral_orthogonal_remainder
    (L : Submodule ℤ E) (hL : Integral L) {u x : E}
    (hu : u ∈ L) (hu1 : ⟪u, u⟫ = 1) (hx : x ∈ L) :
    ∃ n : ℤ, x - (n : ℝ) • u ∈ L ∧ ⟪x - (n : ℝ) • u, u⟫ = 0 := by
  obtain ⟨n, hn⟩ := hL x hx u hu
  refine ⟨n, ?_, ?_⟩
  · apply L.sub_mem hx
    simpa only [Int.cast_smul_eq_zsmul] using L.smul_mem n hu
  · rw [inner_sub_left, inner_smul_left, hu1, hn]
    simp

/-- The part of a lattice orthogonal to a specified vector, still regarded
as an integral submodule of the original Euclidean space. -/
def orthogonalSlice (L : Submodule ℤ E) (u : E) : Submodule ℤ E where
  carrier := {x | x ∈ L ∧ ⟪x, u⟫ = 0}
  zero_mem' := by simp
  add_mem' := by
    intro x y hx hy
    exact ⟨L.add_mem hx.1 hy.1, by simp [inner_add_left, hx.2, hy.2]⟩
  smul_mem' := by
    intro n x hx
    refine ⟨L.smul_mem n hx.1, ?_⟩
    rw [← Int.cast_smul_eq_zsmul ℝ, inner_smul_left, hx.2, mul_zero]

@[simp] theorem mem_orthogonalSlice (L : Submodule ℤ E) (u x : E) :
    x ∈ orthogonalSlice L u ↔ x ∈ L ∧ ⟪x, u⟫ = 0 := Iff.rfl

theorem orthogonalSlice_integral (L : Submodule ℤ E) (hL : Integral L) (u : E) :
    Integral (orthogonalSlice L u) := by
  intro x hx y hy
  exact hL x hx.1 y hy.1

/-- The unit direction and its integral orthogonal slice generate the whole
lattice. This is the algebraic direct-sum step of the classification. -/
theorem span_unit_sup_orthogonalSlice
    (L : Submodule ℤ E) (hL : Integral L) {u : E}
    (hu : u ∈ L) (hu1 : ⟪u, u⟫ = 1) :
    Submodule.span ℤ {u} ⊔ orthogonalSlice L u = L := by
  apply le_antisymm
  · apply sup_le
    · exact Submodule.span_le.mpr (by simpa using hu)
    · exact fun x hx => hx.1
  · intro x hx
    obtain ⟨n, hmem, horth⟩ := exists_integral_orthogonal_remainder L hL hu hu1 hx
    have hnu : (n : ℝ) • u ∈ Submodule.span ℤ ({u} : Set E) := by
      simpa only [Int.cast_smul_eq_zsmul] using
        (Submodule.span ℤ ({u} : Set E)).smul_mem n
          (Submodule.subset_span (Set.mem_singleton u))
    exact Submodule.mem_sup.mpr ⟨(n : ℝ) • u, hnu, x - (n : ℝ) • u,
      ⟨hmem, horth⟩, by simp⟩

/-- A unit direction intersects its orthogonal slice trivially. -/
theorem span_unit_inf_orthogonalSlice
    (L : Submodule ℤ E) {u : E} (hu1 : ⟪u, u⟫ = 1) :
    Submodule.span ℤ {u} ⊓ orthogonalSlice L u = ⊥ := by
  apply eq_bot_iff.mpr
  intro x hx
  obtain ⟨n, hn⟩ := Submodule.mem_span_singleton.mp hx.1
  have hzero := hx.2.2
  rw [← hn, ← Int.cast_smul_eq_zsmul ℝ, inner_smul_left, hu1] at hzero
  have hn0 : n = 0 := by exact_mod_cast (by simpa using hzero : (n : ℝ) = 0)
  simpa [hn0] using hn.symm

/-- The explicit integral splitting map along a unit lattice direction. -/
def unitSplitMap (L : Submodule ℤ E) {u : E} (hu : u ∈ L) :
    ℤ × orthogonalSlice L u →ₗ[ℤ] L where
  toFun v := ⟨v.1 • u + (v.2 : E), L.add_mem (L.smul_mem v.1 hu) v.2.property.1⟩
  map_add' := by
    intro v w
    ext
    simp [add_smul, add_add_add_comm]
  map_smul' := by
    intro a v
    ext
    simp [smul_add, mul_smul]

theorem unitSplitMap_bijective (L : Submodule ℤ E) (hL : Integral L)
    {u : E} (hu : u ∈ L) (hu1 : ⟪u, u⟫ = 1) :
    Function.Bijective (unitSplitMap L hu) := by
  constructor
  · intro v w h
    have hv : ⟪((unitSplitMap L hu v : L) : E), u⟫ = (v.1 : ℝ) := by
      change ⟪v.1 • u + (v.2 : E), u⟫ = (v.1 : ℝ)
      rw [inner_add_left, ← Int.cast_smul_eq_zsmul ℝ, inner_smul_left,
        hu1, v.2.property.2]
      simp
    have hw : ⟪((unitSplitMap L hu w : L) : E), u⟫ = (w.1 : ℝ) := by
      change ⟪w.1 • u + (w.2 : E), u⟫ = (w.1 : ℝ)
      rw [inner_add_left, ← Int.cast_smul_eq_zsmul ℝ, inner_smul_left,
        hu1, w.2.property.2]
      simp
    have hfst : v.1 = w.1 := by
      apply Int.cast_injective (α := ℝ)
      rw [← hv, ← hw, h]
    have hval : v.1 • u + (v.2 : E) = w.1 • u + (w.2 : E) :=
      congrArg (fun x : L => (x : E)) h
    have hsnd : v.2 = w.2 := by
      apply Subtype.ext
      rw [hfst] at hval
      exact add_left_cancel hval
    exact Prod.ext hfst hsnd
  · intro x
    obtain ⟨n, hmem, horth⟩ :=
      exists_integral_orthogonal_remainder L hL hu hu1 x.property
    refine ⟨(n, ⟨(x : E) - (n : ℝ) • u, hmem, horth⟩), ?_⟩
    apply Subtype.ext
    change n • u + ((x : E) - (n : ℝ) • u) = (x : E)
    rw [Int.cast_smul_eq_zsmul]
    simp

/-- The lattice is integrally isomorphic to a copy of `ℤ` and its orthogonal
slice. This constructs the basis-splitting equivalence, rather than assuming
that a unit vector has already been extended to an integral basis. -/
def unitSplitEquiv (L : Submodule ℤ E) (hL : Integral L)
    {u : E} (hu : u ∈ L) (hu1 : ⟪u, u⟫ = 1) :
    (ℤ × orthogonalSlice L u) ≃ₗ[ℤ] L :=
  LinearEquiv.ofBijective (unitSplitMap L hu) (unitSplitMap_bijective L hL hu hu1)

/-- Extending a basis of the integral orthogonal slice by the chosen unit
vector, through the explicit integral splitting equivalence. -/
def unitExtensionBasis {ι : Type*} (L : Submodule ℤ E) (hL : Integral L)
    {u : E} (hu : u ∈ L) (hu1 : ⟪u, u⟫ = 1)
    (c : Basis ι ℤ (orthogonalSlice L u)) : Basis (Unit ⊕ ι) ℤ L :=
  ((Basis.singleton Unit ℤ).prod c).map (unitSplitEquiv L hL hu hu1)

@[simp] theorem unitExtensionBasis_inl {ι : Type*} (L : Submodule ℤ E)
    (hL : Integral L) {u : E} (hu : u ∈ L) (hu1 : ⟪u, u⟫ = 1)
    (c : Basis ι ℤ (orthogonalSlice L u)) (a : Unit) :
    ((unitExtensionBasis L hL hu hu1 c (.inl a) : L) : E) = u := by
  simp [unitExtensionBasis, Basis.prod_apply, unitSplitEquiv, unitSplitMap]

@[simp] theorem unitExtensionBasis_inr {ι : Type*} (L : Submodule ℤ E)
    (hL : Integral L) {u : E} (hu : u ∈ L) (hu1 : ⟪u, u⟫ = 1)
    (c : Basis ι ℤ (orthogonalSlice L u)) (i : ι) :
    ((unitExtensionBasis L hL hu hu1 c (.inr i) : L) : E) = (c i : E) := by
  simp [unitExtensionBasis, Basis.prod_apply, unitSplitEquiv, unitSplitMap]

/-- The real orthogonal complement, as a genuine lower-dimensional
Euclidean ambient space. -/
def unitPerp (u : E) : Submodule ℝ E := (innerSL ℝ u).ker

/-- The orthogonal slice, now viewed as a lattice inside its own real span. -/
def perpendicularLattice (L : Submodule ℤ E) (u : E) : Submodule ℤ (unitPerp u) :=
  L.comap ((unitPerp u).subtype.restrictScalars ℤ)

/-- Orthogonal projection off a unit direction, with its range restricted
to the real orthogonal complement. -/
def unitPerpMap {u : E} (hu1 : ⟪u, u⟫ = 1) : E →ₗ[ℝ] unitPerp u where
  toFun x := ⟨x - ⟪u, x⟫ • u, by
    change ⟪u, x - ⟪u, x⟫ • u⟫ = 0
    rw [inner_sub_right, inner_smul_right, hu1]
    simp⟩
  map_add' := by
    intro x y
    apply Subtype.ext
    simp [inner_add_right, add_smul, add_sub_add_comm]
  map_smul' := by
    intro c x
    apply Subtype.ext
    simp [inner_smul_right, smul_sub, smul_smul, mul_comm]

@[simp] theorem unitPerpMap_apply_perp {u : E} (hu1 : ⟪u, u⟫ = 1)
    (x : unitPerp u) : unitPerpMap hu1 (x : E) = x := by
  apply Subtype.ext
  have hx : ⟪u, (x : E)⟫ = 0 := x.property
  simp [unitPerpMap, hx]

theorem unitPerpMap_mem_lattice (L : Submodule ℤ E) (hL : Integral L)
    {u : E} (hu : u ∈ L) (hu1 : ⟪u, u⟫ = 1) {x : E} (hx : x ∈ L) :
    unitPerpMap hu1 x ∈ perpendicularLattice L u := by
  obtain ⟨n, hn⟩ := hL u hu x hx
  change x - ⟪u, x⟫ • u ∈ L
  rw [hn]
  apply L.sub_mem hx
  simpa only [Int.cast_smul_eq_zsmul] using L.smul_mem n hu

instance perpendicularLattice_discrete (L : Submodule ℤ E) [DiscreteTopology L] (u : E) :
    DiscreteTopology (perpendicularLattice L u) := by
  let f : perpendicularLattice L u → L := fun x => ⟨((x : unitPerp u) : E), x.property⟩
  have hf : Continuous f := by
    exact (continuous_subtype_val.comp continuous_subtype_val).subtype_mk _
  have hinj : Function.Injective f := by
    intro x y h
    apply Subtype.ext
    apply Subtype.ext
    exact congrArg (fun z : L => (z : E)) h
  exact DiscreteTopology.of_continuous_injective hf hinj

theorem perpendicularLattice_isZLattice (L : Submodule ℤ E)
    [DiscreteTopology L] [IsZLattice ℝ L] (hL : Integral L)
    {u : E} (hu : u ∈ L) (hu1 : ⟪u, u⟫ = 1) :
    IsZLattice ℝ (perpendicularLattice L u) := by
  constructor
  let P := Submodule.span ℝ (perpendicularLattice L u : Set (unitPerp u))
  have hspan : Submodule.span ℝ (L : Set E) ≤ P.comap (unitPerpMap hu1) := by
    apply Submodule.span_le.mpr
    intro x hx
    exact Submodule.subset_span (unitPerpMap_mem_lattice L hL hu hu1 hx)
  apply top_unique
  intro x hx
  have hx' : (x : E) ∈ Submodule.span ℝ (L : Set E) := by
    rw [IsZLattice.span_top (K := ℝ)]
    trivial
  have h := hspan hx'
  simpa only [Submodule.mem_comap, unitPerpMap_apply_perp] using h

theorem perpendicularLattice_integral (L : Submodule ℤ E) (hL : Integral L) (u : E) :
    Integral (perpendicularLattice L u) := by
  intro x hx y hy
  exact hL (x : E) hx (y : E) hy

/-- Changing only the ambient subtype does not change the integral slice. -/
def perpendicularEquivSlice (L : Submodule ℤ E) (u : E) :
    perpendicularLattice L u ≃ₗ[ℤ] orthogonalSlice L u where
  toFun x := ⟨((x : unitPerp u) : E), x.property, by
    have h : ⟪u, ((x : unitPerp u) : E)⟫ = 0 := (x : unitPerp u).property
    simpa only [real_inner_comm] using h⟩
  invFun x := ⟨⟨(x : E), by
    change ⟪u, (x : E)⟫ = 0
    simpa only [real_inner_comm] using x.property.2⟩, x.property.1⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- An orthonormal real coordinate basis with the same index as an arbitrary
integral basis. The matching cardinality follows from the lattice spanning
the real ambient space. -/
def orthonormalCoordinates {ι : Type*} [Fintype ι]
    (L : Submodule ℤ E) [DiscreteTopology L] [IsZLattice ℝ L]
    (b : Basis ι ℤ L) : OrthonormalBasis ι ℝ E :=
  (stdOrthonormalBasis ℝ E).reindex (Fintype.equivOfCardEq (by
    rw [Fintype.card_fin, finrank_eq_card_basis (b.ofZLatticeBasis ℝ)]))

/-- The square of a Euclidean lattice's covolume is the determinant of its
Gram matrix. The orthonormal coordinate basis is arbitrary. This identity
is the volume bridge needed after splitting off an integral unit vector. -/
theorem covolume_sq_eq_gram_det
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (L : Submodule ℤ E) [DiscreteTopology L] [IsZLattice ℝ L]
    (b : Basis ι ℤ L) (o : OrthonormalBasis ι ℝ E) :
    ZLattice.covolume L ^ 2 =
      (Matrix.of fun i j => ⟪(b i : E), (b j : E)⟫).det := by
  let A : Matrix ι ι ℝ := fun i j => o.repr (b j : E) i
  have hfund : volume.real (ZSpan.fundamentalDomain o.toBasis) = 1 := by
    rw [measureReal_congr (ZSpan.fundamentalDomain_ae_parallelepiped o.toBasis volume),
      measureReal_def, OrthonormalBasis.coe_toBasis, o.volume_parallelepiped]
    rfl
  have hcov : ZLattice.covolume L = |A.det| := by
    rw [ZLattice.covolume_eq_det_mul_measureReal L volume b o.toBasis, hfund, mul_one,
      Basis.det_apply]
    congr 2
  have hgram : (Matrix.of fun i j => ⟪(b i : E), (b j : E)⟫) = A.transpose * A := by
    ext i j
    simp only [Matrix.of_apply, Matrix.mul_apply, Matrix.transpose_apply, A]
    symm
    simpa only [o.repr_apply_apply, real_inner_comm (b i : E)] using
      o.sum_inner_mul_inner (b i : E) (b j : E)
  rw [hcov, hgram, Matrix.det_mul, Matrix.det_transpose, sq_abs, pow_two]

/-- Complete classification in rank one: the lattice consists exactly of
integer multiples of a unit vector. -/
theorem rank_one_classification
    (L : Submodule ℤ E) [DiscreteTopology L] [IsZLattice ℝ L]
    (hL : Integral L) (hvol : ZLattice.covolume L = 1)
    (hr : finrank ℝ E = 1) :
    ∃ u : E, ⟪u, u⟫ = 1 ∧ L = Submodule.span ℤ {u} := by
  obtain ⟨u, hu, hu1⟩ := exists_unit_vector L hL hvol (by omega) (by omega)
  have hu0 : u ≠ 0 := by
    intro h
    simp [h] at hu1
  refine ⟨u, hu1, le_antisymm ?_ ?_⟩
  · intro x hx
    obtain ⟨c, hc⟩ := (finrank_eq_one_iff_of_nonzero' (K := ℝ) u hu0).mp hr x
    obtain ⟨n, hn⟩ := hL x hx u hu
    have hcn : c = (n : ℝ) := by
      simpa only [← hc, real_inner_smul_left, hu1, mul_one] using hn
    apply Submodule.mem_span_singleton.mpr
    exact ⟨n, by simpa only [hcn, Int.cast_smul_eq_zsmul] using hc⟩
  · exact Submodule.span_le.mpr (by simpa using hu)

/-- An orthogonal unit extension preserves covolume one. Here `b` is the
actual extended integral basis and `c` is the basis of its orthogonal part;
the hypotheses record their concrete Gram entries, rather than assume a
classification or a covolume conclusion. -/
theorem orthogonal_extension_covolume_one
    {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F]
    [FiniteDimensional ℝ F] [MeasurableSpace F] [BorelSpace F]
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (L : Submodule ℤ E) [DiscreteTopology L] [IsZLattice ℝ L]
    (K : Submodule ℤ F) [DiscreteTopology K] [IsZLattice ℝ K]
    (b : Basis (Unit ⊕ ι) ℤ L) (c : Basis ι ℤ K)
    (o : OrthonormalBasis (Unit ⊕ ι) ℝ E) (p : OrthonormalBasis ι ℝ F)
    (hunit : ⟪(b (.inl ()) : E), (b (.inl ()) : E)⟫ = 1)
    (horth : ∀ i, ⟪(b (.inl ()) : E), (b (.inr i) : E)⟫ = 0)
    (hgram : ∀ i j, ⟪(b (.inr i) : E), (b (.inr j) : E)⟫ =
      ⟪(c i : F), (c j : F)⟫)
    (hvol : ZLattice.covolume L = 1) : ZLattice.covolume K = 1 := by
  have hblock : (Matrix.of fun i j => ⟪(b i : E), (b j : E)⟫) =
      Matrix.fromBlocks (fun _ _ : Unit => (1 : ℝ)) 0 0
        (Matrix.of fun i j => ⟪(c i : F), (c j : F)⟫) := by
    ext i j
    rcases i with ⟨⟩ | i <;> rcases j with ⟨⟩ | j
    · simpa using hunit
    · simpa using horth j
    · simpa only [Matrix.of_apply, Matrix.fromBlocks_apply₂₁, Matrix.zero_apply,
        real_inner_comm] using horth i
    · simpa using hgram i j
  have hsqL := covolume_sq_eq_gram_det L b o
  have hsqK := covolume_sq_eq_gram_det K c p
  rw [hblock, Matrix.det_fromBlocks_zero₂₁, Matrix.det_unique] at hsqL
  norm_num only [one_mul, hvol, one_pow] at hsqL
  have hpos := ZLattice.covolume_pos K volume
  nlinarith

/-- Splitting off a unit direction preserves the covolume of the actual
orthogonal lattice. This discharges the volume step needed for recursion. -/
theorem perpendicularLattice_covolume_one
    (L : Submodule ℤ E) [DiscreteTopology L] [IsZLattice ℝ L]
    (hL : Integral L) (hvol : ZLattice.covolume L = 1)
    {u : E} (hu : u ∈ L) (hu1 : ⟪u, u⟫ = 1) :
    ZLattice.covolume (perpendicularLattice L u) = 1 := by
  let K := perpendicularLattice L u
  letI : IsZLattice ℝ K := perpendicularLattice_isZLattice L hL hu hu1
  let c := Module.Free.chooseBasis ℤ K
  let b := unitExtensionBasis L hL hu hu1 (c.map (perpendicularEquivSlice L u))
  apply orthogonal_extension_covolume_one L K b c
    (orthonormalCoordinates L b) (orthonormalCoordinates K c)
  · simpa only [b, unitExtensionBasis_inl] using hu1
  · intro i
    simp only [b, unitExtensionBasis_inl, unitExtensionBasis_inr, Basis.map_apply]
    exact (c i : unitPerp u).property
  · intro i j
    simp only [b, unitExtensionBasis_inr, Basis.map_apply]
    rfl
  · exact hvol

theorem unitPerp_finrank {u : E} (hu1 : ⟪u, u⟫ = 1) :
    finrank ℝ (unitPerp u) + 1 = finrank ℝ E := by
  have hsurj : Function.Surjective ((innerSL ℝ u).toLinearMap) := by
    intro r
    refine ⟨r • u, ?_⟩
    change ⟪u, r • u⟫ = r
    rw [inner_smul_right, hu1, mul_one]
  have h := (innerSL ℝ u).toLinearMap.finrank_range_add_finrank_ker
  rw [LinearMap.range_eq_top.mpr hsurj, finrank_top, finrank_self] at h
  change 1 + finrank ℝ (unitPerp u) = finrank ℝ E at h
  omega

theorem unitExtensionBasis_orthonormal
    {ι : Type*} [DecidableEq ι]
    (L : Submodule ℤ E) (hL : Integral L)
    {u : E} (hu : u ∈ L) (hu1 : ⟪u, u⟫ = 1)
    (c : Basis ι ℤ (orthogonalSlice L u))
    (hc : Orthonormal ℝ (fun i => (c i : E))) :
    Orthonormal ℝ (fun i => ((unitExtensionBasis L hL hu hu1 c i : L) : E)) := by
  classical
  rw [orthonormal_iff_ite] at hc ⊢
  intro i j
  rcases i with ⟨⟩ | i <;> rcases j with ⟨⟩ | j
  · simp only [unitExtensionBasis_inl, hu1, ↓reduceIte]
  · have h := (c j).property.2
    simp only [unitExtensionBasis_inl, unitExtensionBasis_inr, Sum.inl_ne_inr,
      ↓reduceIte]
    rw [real_inner_comm]
    exact h
  · simpa only [unitExtensionBasis_inl, unitExtensionBasis_inr, Sum.inr_ne_inl,
      ↓reduceIte] using (c i).property.2
  · simpa only [unitExtensionBasis_inr, Sum.inr.injEq] using hc i j

/-- Integral positive-definite Euclidean lattices of rank at most three and
covolume one admit an orthonormal integral basis. The proof constructs the
orthogonal sublattice and its covolume before invoking induction. -/
theorem classification_rank
    (n : ℕ) (L : Submodule ℤ E) [DiscreteTopology L] [IsZLattice ℝ L]
    (hL : Integral L) (hvol : ZLattice.covolume L = 1)
    (hn : finrank ℝ E = n) (hn3 : n ≤ 3) :
    ∃ b : Basis (Fin n) ℤ L, Orthonormal ℝ (fun i => (b i : E)) := by
  classical
  induction n using Nat.strong_induction_on generalizing E with
  | h n ih =>
    rcases Nat.eq_zero_or_pos n with rfl | hnpos
    · haveI : Subsingleton E := (Module.finrank_zero_iff (R := ℝ) (M := E)).mp hn
      refine ⟨Basis.empty L, ?_⟩
      rw [orthonormal_iff_ite]
      intro i
      exact Fin.elim0 i
    · obtain ⟨u, hu, hu1⟩ := exists_unit_vector L hL hvol (by omega) (by omega)
      let K := perpendicularLattice L u
      letI : IsZLattice ℝ K := perpendicularLattice_isZLattice L hL hu hu1
      have hKvol : ZLattice.covolume K = 1 := perpendicularLattice_covolume_one L hL hvol hu hu1
      have hKrank : finrank ℝ (unitPerp u) = n - 1 := by
        have h := unitPerp_finrank hu1
        omega
      obtain ⟨c, hc⟩ := ih (n - 1) (by omega) K
        (perpendicularLattice_integral L hL u) hKvol hKrank (by omega)
      let cs := c.map (perpendicularEquivSlice L u)
      have hcs : Orthonormal ℝ (fun i => (cs i : E)) := by
        rw [orthonormal_iff_ite] at hc ⊢
        intro i j
        exact hc i j
      let b := unitExtensionBasis L hL hu hu1 cs
      have hb : Orthonormal ℝ (fun i => (b i : E)) :=
        unitExtensionBasis_orthonormal L hL hu hu1 cs hcs
      let e : Unit ⊕ Fin (n - 1) ≃ Fin n := Fintype.equivOfCardEq (by simp; omega)
      refine ⟨b.reindex e, ?_⟩
      simpa only [Basis.reindex_apply, Function.comp_apply] using
        hb.comp e.symm e.symm.injective

theorem classification
    (L : Submodule ℤ E) [DiscreteTopology L] [IsZLattice ℝ L]
    (hL : Integral L) (hvol : ZLattice.covolume L = 1)
    (hr : finrank ℝ E ≤ 3) :
    ∃ b : Basis (Fin (finrank ℝ E)) ℤ L, Orthonormal ℝ (fun i => (b i : E)) :=
  classification_rank (finrank ℝ E) L hL hvol rfl hr

/-- Parseval's identity in the integer coordinates of an orthonormal
integral basis. This is the concrete norm identity used by primitive-shell
equivalences. -/
theorem orthonormal_integral_coordinates_norm
    {ι : Type*} [Fintype ι]
    (L : Submodule ℤ E) [DiscreteTopology L] [IsZLattice ℝ L]
    (b : Basis ι ℤ L) (hb : Orthonormal ℝ (fun i => (b i : E))) (x : L) :
    ∑ i, ((b.equivFun x i : ℤ) : ℝ) ^ 2 = ‖(x : E)‖ ^ 2 := by
  let bR := b.ofZLatticeBasis ℝ
  have hbR : Orthonormal ℝ (fun i => bR i) := by
    simpa only [bR, Basis.ofZLatticeBasis_apply] using hb
  let o := bR.toOrthonormalBasis hbR
  have hcoords (i : ι) : ⟪o i, (x : E)⟫ = ((b.equivFun x i : ℤ) : ℝ) := by
    rw [← o.repr_apply_apply, ← o.coe_toBasis_repr_apply]
    dsimp only [o]
    rw [Basis.toBasis_toOrthonormalBasis]
    simpa only [bR, Basis.equivFun_apply] using
      b.ofZLatticeBasis_repr_apply ℝ L x i
  simpa only [hcoords] using o.sum_sq_inner_right (x : E)

/-- A concrete integral linear equivalence to the standard integer lattice,
preserving squared Euclidean norm, for every integral unimodular lattice of
rank at most three. No isometry/classification is supplied as a hypothesis. -/
theorem exists_norm_preserving_integral_coordinates
    (L : Submodule ℤ E) [DiscreteTopology L] [IsZLattice ℝ L]
    (hL : Integral L) (hvol : ZLattice.covolume L = 1)
    (hr : finrank ℝ E ≤ 3) :
    ∃ e : L ≃ₗ[ℤ] (Fin (finrank ℝ E) → ℤ),
      ∀ x : L, ∑ i, ((e x i : ℤ) : ℝ) ^ 2 = ‖(x : E)‖ ^ 2 := by
  obtain ⟨b, hb⟩ := classification L hL hvol hr
  exact ⟨b.equivFun, orthonormal_integral_coordinates_norm L b hb⟩

end SmallIntegralLattices

#print axioms SmallIntegralLattices.exists_unit_vector
#print axioms SmallIntegralLattices.perpendicularLattice_covolume_one
#print axioms SmallIntegralLattices.classification
#print axioms SmallIntegralLattices.exists_norm_preserving_integral_coordinates
