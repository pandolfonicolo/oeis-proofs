import A354766.IsotropicLift
import A354766.NeighborConstruction
import A354766.IsotropicLines

/-!
# A chosen normalized neighbor for each isotropic projective line

This file is proof text prepared against the checked prerequisite modules.
Its own compilation and axiom audit are separate obligations until recorded.
-/

namespace A354766Research.NeighborFamily

open Neighbor IsotropicLines

def reduceVec (p : ℕ) (u : IntVec) : Ternary (ZMod p) := fun i => (u i : ZMod p)

theorem reduceVec_ne_zero_iff (p : ℕ) (u : IntVec) :
    reduceVec p u ≠ 0 ↔ ∃ i : Fin 3, ¬(p : ℤ) ∣ u i := by
  classical
  constructor
  · intro h
    by_contra hn
    apply h
    funext i
    apply (ZMod.intCast_zmod_eq_zero_iff_dvd (u i) p).mpr
    by_contra hi
    exact hn ⟨i, hi⟩
  · rintro ⟨i, hi⟩ h
    apply hi
    apply (ZMod.intCast_zmod_eq_zero_iff_dvd (u i) p).mp
    exact congrFun h i

theorem reduceVec_norm (p : ℕ) [Fact p.Prime] (u : IntVec) :
    standardNorm (ZMod p) (reduceVec p u) = ((dot3 u u : ℤ) : ZMod p) := by
  simp [standardNorm, reduceVec, dot3, pow_two]

theorem reduceVec_dot (p : ℕ) [Fact p.Prime] (u v : IntVec) :
    standardDot (ZMod p) (reduceVec p u) (reduceVec p v) =
      ((dot3 u v : ℤ) : ZMod p) := by
  simp [standardDot, reduceVec, dot3]

theorem reduceVec_eq_of_congr (p : ℕ) (u v : IntVec)
    (h : ∀ i : Fin 3, (p : ℤ) ∣ u i - v i) : reduceVec p u = reduceVec p v := by
  funext i
  apply sub_eq_zero.mp
  have hz := (ZMod.intCast_zmod_eq_zero_iff_dvd (u i - v i) p).mpr (h i)
  simpa only [Int.cast_sub] using hz

theorem exists_normalized_vector_lift (p : ℕ) (hp : p.Prime) (hp2 : p ≠ 2)
    (u : IntVec) (hu : ∃ i : Fin 3, ¬(p : ℤ) ∣ u i) (hQ : (p : ℤ) ∣ dot3 u u) :
    ∃ v : IntVec, (∀ i : Fin 3, (p : ℤ) ∣ v i - u i) ∧
      (p : ℤ) ^ 2 ∣ dot3 v v ∧ (∃ i : Fin 3, ¬(p : ℤ) ∣ v i) := by
  have ht : tripleNonzeroMod p (u 0, u 1, u 2) := by
    rintro ⟨h0, h1, h2⟩
    obtain ⟨i, hi⟩ := hu
    fin_cases i
    · exact hi h0
    · exact hi h1
    · exact hi h2
  have hQt : (p : ℤ) ∣ tripleNormSq (u 0, u 1, u 2) := by
    simpa only [tripleNormSq, dot3, pow_two] using hQ
  obtain ⟨t, hc, hQt', hnt⟩ := exists_normalized_isotropic_lift p hp hp2 (u 0, u 1, u 2) ht hQt
  let v : IntVec := ![t.1, t.2.1, t.2.2]
  have hnv : ¬((p : ℤ) ∣ v 0 ∧ (p : ℤ) ∣ v 1 ∧ (p : ℤ) ∣ v 2) := by
    simpa [v, tripleNonzeroMod] using hnt
  refine ⟨v, ?_, ?_, ?_⟩
  · rcases hc with ⟨h0, h1, h2⟩
    intro i
    fin_cases i
    · simpa [v] using h0
    · simpa [v] using h1
    · simpa [v] using h2
  · simpa [v, dot3, tripleNormSq, pow_two] using hQt'
  · by_cases h0 : (p : ℤ) ∣ v 0
    · by_cases h1 : (p : ℤ) ∣ v 1
      · exact ⟨2, fun h2 => hnv ⟨h0, h1, h2⟩⟩
      · exact ⟨1, h1⟩
    · exact ⟨0, h0⟩

theorem exists_normalized_representative (p : ℕ) [Fact p.Prime] (hp2 : p ≠ 2)
    (P : StandardConic (ZMod p)) :
    ∃ u : IntVec, (p : ℤ) ^ 2 ∣ dot3 u u ∧
      ∃ hu : reduceVec p u ≠ 0, Projectivization.mk (ZMod p) (reduceVec p u) hu = P.val := by
  letI : NeZero p := ⟨(Fact.out : p.Prime).ne_zero⟩
  rcases P.property with ⟨x, hx, hP, hQx⟩
  let z : IntVec := fun i => ((x i).val : ℤ)
  have hRz : reduceVec p z = x := by
    funext i
    simp [reduceVec, z, ZMod.natCast_zmod_val]
  have hz : ∃ i : Fin 3, ¬(p : ℤ) ∣ z i :=
    (reduceVec_ne_zero_iff p z).mp (by rw [hRz]; exact hx)
  have hQz : (p : ℤ) ∣ dot3 z z := by
    apply (ZMod.intCast_zmod_eq_zero_iff_dvd (dot3 z z) p).mp
    rw [← reduceVec_norm, hRz]
    exact hQx
  obtain ⟨u, hcong, hQu, hnu⟩ := exists_normalized_vector_lift p Fact.out hp2 z hz hQz
  have hRu : reduceVec p u = x := (reduceVec_eq_of_congr p u z hcong).trans hRz
  have hnu' : reduceVec p u ≠ 0 := (reduceVec_ne_zero_iff p u).mpr hnu
  refine ⟨u, hQu, hnu', ?_⟩
  simpa only [hRu] using hP

noncomputable def normalizedRepresentative (p : ℕ) [Fact p.Prime] (hp2 : p ≠ 2)
    (P : StandardConic (ZMod p)) : IntVec :=
  (exists_normalized_representative p hp2 P).choose

theorem normalizedRepresentative_norm (p : ℕ) [Fact p.Prime] (hp2 : p ≠ 2)
    (P : StandardConic (ZMod p)) :
    (p : ℤ) ^ 2 ∣ dot3 (normalizedRepresentative p hp2 P) (normalizedRepresentative p hp2 P) :=
  (exists_normalized_representative p hp2 P).choose_spec.1

theorem normalizedRepresentative_ne_zero (p : ℕ) [Fact p.Prime] (hp2 : p ≠ 2)
    (P : StandardConic (ZMod p)) : reduceVec p (normalizedRepresentative p hp2 P) ≠ 0 :=
  (exists_normalized_representative p hp2 P).choose_spec.2.choose

theorem normalizedRepresentative_projective (p : ℕ) [Fact p.Prime] (hp2 : p ≠ 2)
    (P : StandardConic (ZMod p)) :
    Projectivization.mk (ZMod p) (reduceVec p (normalizedRepresentative p hp2 P))
      (normalizedRepresentative_ne_zero p hp2 P) = P.val :=
  (exists_normalized_representative p hp2 P).choose_spec.2.choose_spec

noncomputable def family (p : ℕ) [Fact p.Prime] (hp2 : p ≠ 2)
    (P : StandardConic (ZMod p)) : Submodule ℤ RatVec :=
  neighbor p (normalizedRepresentative p hp2 P)

theorem projective_eq_iff_integer_scalar (p : ℕ) [Fact p.Prime]
    (u v : IntVec) (hu : reduceVec p u ≠ 0) (hv : reduceVec p v ≠ 0) :
    Projectivization.mk (ZMod p) (reduceVec p v) hv =
        Projectivization.mk (ZMod p) (reduceVec p u) hu ↔
      ∃ a : ℤ, ¬(p : ℤ) ∣ a ∧ ∀ i : Fin 3, (p : ℤ) ∣ v i - a * u i := by
  letI : NeZero p := ⟨(Fact.out : p.Prime).ne_zero⟩
  rw [Projectivization.mk_eq_mk_iff']
  constructor
  · rintro ⟨a, hae⟩
    have ha0 : a ≠ 0 := by
      intro h
      apply hv
      rw [← hae, h, zero_smul]
    let az : ℤ := (a.val : ℤ)
    have hcast : (az : ZMod p) = a := by simp [az, ZMod.natCast_zmod_val]
    refine ⟨az, ?_, ?_⟩
    · intro hd
      apply ha0
      rw [← hcast]
      exact (ZMod.intCast_zmod_eq_zero_iff_dvd az p).mpr hd
    · intro i
      apply (ZMod.intCast_zmod_eq_zero_iff_dvd (v i - az * u i) p).mp
      simp only [Int.cast_sub, Int.cast_mul, hcast]
      have hi := congrFun hae i
      change a * (u i : ZMod p) = (v i : ZMod p) at hi
      exact sub_eq_zero.mpr hi.symm
  · rintro ⟨a, ha, hcong⟩
    refine ⟨(a : ZMod p), ?_⟩
    funext i
    change (a : ZMod p) * (u i : ZMod p) = (v i : ZMod p)
    have hz := (ZMod.intCast_zmod_eq_zero_iff_dvd (v i - a * u i) p).mpr (hcong i)
    have hz' : (v i : ZMod p) - (a : ZMod p) * (u i : ZMod p) = 0 := by
      simpa only [Int.cast_sub, Int.cast_mul] using hz
    exact (sub_eq_zero.mp hz').symm

/-- The exact projective membership interface needed for exterior vectors. -/
theorem exterior_mem_family_iff (p : ℕ) [Fact p.Prime] (hp2 : p ≠ 2)
    (P : StandardConic (ZMod p)) (v : IntVec) (hv : reduceVec p v ≠ 0)
    (hQv : (p : ℤ) ^ 2 ∣ dot3 v v) :
    liftVec p v ∈ family p hp2 P ↔
      Projectivization.mk (ZMod p) (reduceVec p v) hv = P.val := by
  rw [family, exterior_neighbor_membership_iff p Fact.out hp2
    (normalizedRepresentative p hp2 P) v ((reduceVec_ne_zero_iff p v).mp hv)
    (normalizedRepresentative_norm p hp2 P) hQv]
  rw [← normalizedRepresentative_projective p hp2 P]
  exact (projective_eq_iff_integer_scalar p (normalizedRepresentative p hp2 P) v
    (normalizedRepresentative_ne_zero p hp2 P) hv).symm

/-- The exact perpendicular-line interface needed for integral vectors. -/
theorem inside_mem_family_iff (p : ℕ) [Fact p.Prime] (hp2 : p ≠ 2)
    (P : StandardConic (ZMod p)) (z : IntVec) :
    castVec z ∈ family p hp2 P ↔
      P.val.submodule ≤ (standardDot (ZMod p) (reduceVec p z)).ker := by
  let u := normalizedRepresentative p hp2 P
  have hu : ∃ i : Fin 3, ¬(p : ℤ) ∣ u i :=
    (reduceVec_ne_zero_iff p u).mp (normalizedRepresentative_ne_zero p hp2 P)
  have hQu : (p : ℤ) ∣ dot3 u u := by
    obtain ⟨k, hk⟩ := normalizedRepresentative_norm p hp2 P
    refine ⟨(p : ℤ) * k, ?_⟩
    change dot3 (normalizedRepresentative p hp2 P) (normalizedRepresentative p hp2 P) = _
    rw [hk]
    ring
  have hmid : castVec z ∈ family p hp2 P ↔ castVec z ∈ midpoint p u := by
    constructor
    · intro hz
      have hi : castVec z ∈ standard ⊓ neighbor p u := ⟨⟨z, rfl⟩, hz⟩
      rw [standard_inf_neighbor p Fact.out u hu hQu] at hi
      exact hi
    · intro hz
      change castVec z ∈ neighbor p u
      exact midpoint_le_neighbor p u hz
  rw [hmid, castVec_mem_midpoint_iff]
  rw [← normalizedRepresentative_projective p hp2 P, Projectivization.submodule_mk,
    Submodule.span_singleton_le_iff_mem, LinearMap.mem_ker, reduceVec_dot]
  rw [ZMod.intCast_zmod_eq_zero_iff_dvd]
  have hc : dot3 z u = dot3 u z := by simp only [dot3]; ring
  rw [hc]

end A354766Research.NeighborFamily

#print axioms A354766Research.NeighborFamily.exists_normalized_representative
#print axioms A354766Research.NeighborFamily.exterior_mem_family_iff
#print axioms A354766Research.NeighborFamily.inside_mem_family_iff
