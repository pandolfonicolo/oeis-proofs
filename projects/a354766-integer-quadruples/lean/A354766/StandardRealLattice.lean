import A354766.SmallIntegralLattices
import A354766.NeighborRealification
import A354766.NeighborTopology
import A354766.NeighborConstruction

/-!
The standard rational lattice really becomes the standard Euclidean integer
lattice. Its covolume is proved to be one, rather than supplied as a hypothesis.
The actual index-p neighbor construction then has covolume one and admits the
integral norm-preserving coordinates furnished by small-lattice classification.
-/

noncomputable section

open Module MeasureTheory Set
open scoped RealInnerProductSpace

namespace A354766Neighbors

open A354766Research.Neighbor

theorem realify_standard_eq_zspan :
    realify standard = Submodule.span ℤ
      (Set.range (EuclideanSpace.basisFun (Fin 3) ℝ).toBasis) := by
  ext x
  constructor
  · rintro ⟨v, ⟨m, rfl⟩, rfl⟩
    apply ((EuclideanSpace.basisFun (Fin 3) ℝ).toBasis.mem_span_iff_repr_mem ℤ _).mpr
    intro i
    refine ⟨m i, ?_⟩
    simp [castVec, OrthonormalBasis.coe_toBasis_repr_apply]
  · intro hx
    have hcoords :=
      ((EuclideanSpace.basisFun (Fin 3) ℝ).toBasis.mem_span_iff_repr_mem ℤ x).mp hx
    choose m hm using hcoords
    refine ⟨castVec m, ⟨m, rfl⟩, ?_⟩
    ext i
    simpa [castVec, OrthonormalBasis.coe_toBasis_repr_apply] using hm i

instance realify_standard_discrete : DiscreteTopology (realify standard) := by
  rw [realify_standard_eq_zspan]
  infer_instance

instance realify_standard_isZLattice : IsZLattice ℝ (realify standard) := by
  constructor
  rw [realify_standard_eq_zspan]
  exact ZSpan.span_top (EuclideanSpace.basisFun (Fin 3) ℝ).toBasis

theorem realify_standard_covolume_one : ZLattice.covolume (realify standard) = 1 := by
  rw [realify_standard_eq_zspan]
  let b := (EuclideanSpace.basisFun (Fin 3) ℝ).toBasis
  have hfund := ZSpan.isAddFundamentalDomain b volume
  rw [ZLattice.covolume_eq_measure_fundamentalDomain _ volume hfund,
    measureReal_congr (ZSpan.fundamentalDomain_ae_parallelepiped b volume), measureReal_def]
  change (volume (parallelepiped (EuclideanSpace.basisFun (Fin 3) ℝ))).toReal = 1
  rw [(EuclideanSpace.basisFun (Fin 3) ℝ).volume_parallelepiped]
  rfl

theorem realify_mono {L N : Submodule ℤ RationalVector} (h : L ≤ N) :
    realify L ≤ realify N := by
  rintro x ⟨v, hv, rfl⟩
  exact ⟨v, h hv, rfl⟩

theorem realify_smul_inclusion (L N : Submodule ℤ RationalVector) (p : ℕ)
    (h : ∀ x ∈ L, (p : ℤ) • x ∈ N) :
    ∀ x ∈ realify L, (p : ℤ) • x ∈ realify N := by
  rintro x ⟨v, hv, rfl⟩
  exact ⟨(p : ℤ) • v, h v hv, rationalToReal.map_smul (p : ℤ) v⟩

theorem realify_relIndex (M L : Submodule ℤ RationalVector) :
    (realify M).toAddSubgroup.relIndex (realify L).toAddSubgroup =
      M.toAddSubgroup.relIndex L.toAddSubgroup := by
  change (M.toAddSubgroup.map rationalToReal.toAddMonoidHom).relIndex
    (L.toAddSubgroup.map rationalToReal.toAddMonoidHom) = _
  exact AddSubgroup.relIndex_map_map_of_injective M.toAddSubgroup L.toAddSubgroup
    rationalToReal_injective

theorem realified_neighbor_geometry
    (p : ℕ) (hp : p.Prime) (u : IntVec)
    (hu : ∃ i : Fin 3, ¬(p : ℤ) ∣ u i)
    (hQ : (p : ℤ) ^ 2 ∣ dot3 u u) :
    ∃ hdisc : DiscreteTopology (realify (neighbor p u)),
      letI : DiscreteTopology (realify (neighbor p u)) := hdisc
      IsZLattice ℝ (realify (neighbor p u)) ∧
        SmallIntegralLattices.Integral (realify (neighbor p u)) ∧
        ZLattice.covolume (realify (neighbor p u)) = 1 := by
  let L := realify standard
  let M := realify (midpoint p u)
  let N := realify (neighbor p u)
  have hQ' : (p : ℤ) ∣ dot3 u u := by
    apply dvd_trans (dvd_mul_right (p : ℤ) (p : ℤ))
    simpa only [pow_two] using hQ
  have hML : M ≤ L := realify_mono (midpoint_le_standard p u)
  have hMN : M ≤ N := realify_mono (midpoint_le_neighbor p u)
  have hpLM : ∀ x ∈ L, (p : ℤ) • x ∈ M :=
    realify_smul_inclusion standard (midpoint p u) p
      (p_smul_standard_mem_midpoint p u)
  have hpNM : ∀ x ∈ N, (p : ℤ) • x ∈ M :=
    realify_smul_inclusion (neighbor p u) (midpoint p u) p
      (p_smul_neighbor_mem_midpoint p hp.ne_zero u hQ')
  letI : DiscreteTopology M := discrete_of_prime_multiple_inclusion L M 1 (by decide)
    (fun x hx => by simpa only [Nat.cast_one, one_smul] using hML hx)
  letI : IsZLattice ℝ M := isZLattice_of_prime_multiple_inclusion L M p hp.ne_zero hpLM
  letI : DiscreteTopology N := discrete_of_prime_multiple_inclusion L N p hp.ne_zero
    (fun x hx => hML (hpNM x hx))
  letI : IsZLattice ℝ N := isZLattice_of_prime_multiple_inclusion L N p hp.ne_zero
    (fun x hx => hMN (hpLM x hx))
  have hindex : M.toAddSubgroup.relIndex L.toAddSubgroup =
      M.toAddSubgroup.relIndex N.toAddSubgroup := by
    dsimp only [M, L, N]
    rw [realify_relIndex, realify_relIndex, midpoint_relIndex_standard p hp u hu,
      midpoint_relIndex_neighbor p hp u hu hQ']
  have hvol : ZLattice.covolume N = 1 :=
    (covolume_eq_of_common_index M L N hML hMN hindex).symm.trans
      realify_standard_covolume_one
  have hint : SmallIntegralLattices.Integral N := by
    apply realify_integral
    intro x hx y hy
    exact neighbor_integral p hp.ne_zero u hQ x y hx hy
  exact ⟨inferInstance, inferInstance, hint, hvol⟩

/-- Each concrete normalized p-neighbor is integrally isometric to the
standard ternary lattice; the conclusion includes the explicit quadratic
form identity needed to compare primitive representation counts. -/
theorem neighbor_integral_coordinates
    (p : ℕ) (hp : p.Prime) (u : IntVec)
    (hu : ∃ i : Fin 3, ¬(p : ℤ) ∣ u i)
    (hQ : (p : ℤ) ^ 2 ∣ dot3 u u) :
    ∃ e : neighbor p u ≃ₗ[ℤ] (Fin 3 → ℤ),
      ∀ x : neighbor p u,
        ∑ i, ((e x i : ℤ) : ℝ) ^ 2 = ((dot3 (x : RatVec) (x : RatVec) : ℚ) : ℝ) := by
  obtain ⟨hdisc, hlat, hint, hvol⟩ := realified_neighbor_geometry p hp u hu hQ
  letI := hdisc
  letI := hlat
  obtain ⟨b, hb⟩ := SmallIntegralLattices.classification_rank 3
    (realify (neighbor p u)) hint hvol (by simp [RealTernarySpace]) (by decide)
  let eR : realify (neighbor p u) ≃ₗ[ℤ] (Fin 3 → ℤ) := b.equivFun
  have heR (x : realify (neighbor p u)) :
      ∑ i, ((eR x i : ℤ) : ℝ) ^ 2 = ‖(x : RealTernarySpace)‖ ^ 2 :=
    SmallIntegralLattices.orthonormal_integral_coordinates_norm _ b hb x
  refine ⟨(realifyEquiv (neighbor p u)).trans eR, ?_⟩
  intro x
  rw [LinearEquiv.trans_apply, heR]
  change ‖rationalToReal (x : RatVec)‖ ^ 2 = ((dot3 (x : RatVec) (x : RatVec) : ℚ) : ℝ)
  rw [← real_inner_self_eq_norm_sq, inner_rationalToReal]
  rfl

end A354766Neighbors

#print axioms A354766Neighbors.realify_standard_covolume_one
#print axioms A354766Neighbors.realified_neighbor_geometry
#print axioms A354766Neighbors.neighbor_integral_coordinates
