import Mathlib.LinearAlgebra.Pi
import Mathlib.Data.Rat.Cast.Order
import Mathlib.Data.Nat.Prime.Int
import Mathlib.Algebra.Field.ZMod
import Mathlib.GroupTheory.Index
import Mathlib.LinearAlgebra.Isomorphisms
import Mathlib.LinearAlgebra.Span.Basic
import Mathlib.Tactic.Abel
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

/-!
# The rational p-neighbor construction for the standard ternary lattice

These are concrete integer submodules of `Fin 3 → ℚ`. No classification of
unimodular lattices, representation-count recurrence, or neighbor count is
assumed. The isotropic lift is a separate checked prerequisite.
-/

namespace A354766Research.Neighbor

abbrev IntVec := Fin 3 → ℤ
abbrev RatVec := Fin 3 → ℚ

/-- The standard bilinear form, with its three coordinates made explicit. -/
def dot3 {R : Type*} [CommRing R] (u v : Fin 3 → R) : R :=
  u 0 * v 0 + u 1 * v 1 + u 2 * v 2

theorem dot3_self_eq_sum_squares (u : IntVec) :
    dot3 u u = u 0 ^ 2 + u 1 ^ 2 + u 2 ^ 2 := by
  simp only [dot3, pow_two]

def castVec (u : IntVec) : RatVec := fun i => (u i : ℚ)

def liftVec (p : ℕ) (u : IntVec) : RatVec := fun i => (u i : ℚ) / (p : ℚ)

@[simp] theorem castVec_zero : castVec 0 = 0 := by
  funext i
  simp [castVec]

@[simp] theorem castVec_add (m n : IntVec) :
    castVec (m + n) = castVec m + castVec n := by
  funext i
  simp [castVec]

@[simp] theorem castVec_smul (a : ℤ) (m : IntVec) :
    castVec (a • m) = a • castVec m := by
  funext i
  simp [castVec, Pi.smul_apply, zsmul_eq_mul]

@[simp] theorem castVec_mul (m n : IntVec) :
    castVec (m * n) = castVec m * castVec n := by
  funext i
  simp [castVec]

@[simp] theorem castVec_intCast (a : ℤ) : castVec (a : IntVec) = (a : RatVec) := by
  funext i
  simp [castVec]

@[simp] theorem castVec_natCast (a : ℕ) : castVec (a : IntVec) = (a : RatVec) := by
  funext i
  simp [castVec]

theorem castVec_injective : Function.Injective castVec := by
  intro m n h
  funext i
  have hi := congrFun h i
  change (m i : ℚ) = (n i : ℚ) at hi
  exact_mod_cast hi

@[simp] theorem dot3_zero_right (u : IntVec) : dot3 u 0 = 0 := by
  simp [dot3]

@[simp] theorem dot3_add_right (u m n : IntVec) :
    dot3 u (m + n) = dot3 u m + dot3 u n := by
  simp only [dot3, Pi.add_apply]
  ring

@[simp] theorem dot3_smul_right (u m : IntVec) (a : ℤ) :
    dot3 u (a • m) = a * dot3 u m := by
  simp only [dot3, Pi.smul_apply, Int.zsmul_eq_mul]
  ring

/-- The standard integral lattice inside rational triples. -/
def standard : Submodule ℤ RatVec where
  carrier := {x | ∃ m : IntVec, castVec m = x}
  zero_mem' := ⟨0, castVec_zero⟩
  add_mem' := by
    rintro x y ⟨m, rfl⟩ ⟨n, rfl⟩
    exact ⟨m + n, castVec_add m n⟩
  smul_mem' := by
    rintro a x ⟨m, rfl⟩
    exact ⟨a • m, castVec_smul a m⟩

/-- The index-p candidate M, viewed in the same rational ambient space. -/
def midpoint (p : ℕ) (u : IntVec) : Submodule ℤ RatVec where
  carrier := {x | ∃ m : IntVec, (p : ℤ) ∣ dot3 u m ∧ castVec m = x}
  zero_mem' := ⟨0, by simp, castVec_zero⟩
  add_mem' := by
    rintro x y ⟨m, hm, rfl⟩ ⟨n, hn, rfl⟩
    refine ⟨m + n, ?_, castVec_add m n⟩
    rw [dot3_add_right]
    exact dvd_add hm hn
  smul_mem' := by
    rintro a x ⟨m, hm, rfl⟩
    refine ⟨a • m, ?_, castVec_smul a m⟩
    rw [dot3_smul_right]
    exact dvd_mul_of_dvd_right hm a

/-- The neighbor N=M+ℤ(u/p), with a concrete additive normal form. -/
def neighbor (p : ℕ) (u : IntVec) : Submodule ℤ RatVec where
  carrier := {x | ∃ (m : IntVec) (a : ℤ),
    (p : ℤ) ∣ dot3 u m ∧ castVec m + a • liftVec p u = x}
  zero_mem' := ⟨0, 0, by simp, by simp⟩
  add_mem' := by
    rintro x y ⟨m, a, hm, rfl⟩ ⟨n, b, hn, rfl⟩
    refine ⟨m + n, a + b, ?_, ?_⟩
    · rw [dot3_add_right]
      exact dvd_add hm hn
    · rw [castVec_add, add_smul]
      ac_rfl
  smul_mem' := by
    rintro a x ⟨m, b, hm, rfl⟩
    refine ⟨a • m, a * b, ?_, ?_⟩
    · rw [dot3_smul_right]
      exact dvd_mul_of_dvd_right hm a
    · rw [castVec_smul, mul_smul, smul_add]

@[simp] theorem castVec_mem_midpoint_iff (p : ℕ) (u m : IntVec) :
    castVec m ∈ midpoint p u ↔ (p : ℤ) ∣ dot3 u m := by
  constructor
  · rintro ⟨n, hn, heq⟩
    have hnm : n = m := castVec_injective heq
    simpa only [hnm] using hn
  · intro hm
    exact ⟨m, hm, rfl⟩

theorem midpoint_le_standard (p : ℕ) (u : IntVec) : midpoint p u ≤ standard := by
  rintro x ⟨m, hm, heq⟩
  exact ⟨m, heq⟩

theorem midpoint_le_neighbor (p : ℕ) (u : IntVec) : midpoint p u ≤ neighbor p u := by
  rintro x ⟨m, hm, rfl⟩
  exact ⟨m, 0, hm, by simp⟩

theorem liftVec_mem_neighbor (p : ℕ) (u : IntVec) : liftVec p u ∈ neighbor p u := by
  exact ⟨0, 1, by simp, by simp⟩

theorem p_smul_liftVec (p : ℕ) (hp0 : p ≠ 0) (u : IntVec) :
    (p : ℤ) • liftVec p u = castVec u := by
  have hpq : (p : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr hp0
  funext i
  simp only [Pi.smul_apply, zsmul_eq_mul, liftVec, castVec, Int.cast_natCast]
  field_simp [hpq] <;> ring

/-- Multiplication by p sends the standard lattice into M. -/
theorem p_smul_standard_mem_midpoint (p : ℕ) (u : IntVec) (x : RatVec)
    (hx : x ∈ standard) : (p : ℤ) • x ∈ midpoint p u := by
  rcases hx with ⟨m, rfl⟩
  refine ⟨(p : ℤ) • m, ?_, castVec_smul (p : ℤ) m⟩
  rw [dot3_smul_right]
  exact dvd_mul_right (p : ℤ) (dot3 u m)

/-- Multiplication by p sends N into M whenever p divides Q(u). -/
theorem p_smul_neighbor_mem_midpoint (p : ℕ) (hp0 : p ≠ 0) (u : IntVec)
    (hQ : (p : ℤ) ∣ dot3 u u) (x : RatVec) (hx : x ∈ neighbor p u) :
    (p : ℤ) • x ∈ midpoint p u := by
  rcases hx with ⟨m, a, hm, rfl⟩
  refine ⟨(p : ℤ) • m + a • u, ?_, ?_⟩
  · rw [dot3_add_right, dot3_smul_right, dot3_smul_right]
    exact dvd_add (dvd_mul_right (p : ℤ) (dot3 u m))
      (dvd_mul_of_dvd_right hQ a)
  · calc
      castVec ((p : ℤ) • m + a • u) =
          (p : ℤ) • castVec m + a • castVec u := by simp
      _ = (p : ℤ) • castVec m + a • ((p : ℤ) • liftVec p u) := by
        rw [p_smul_liftVec p hp0 u]
      _ = (p : ℤ) • (castVec m + a • liftVec p u) := by
        rw [smul_add, smul_comm a (p : ℤ)]

private theorem dot3_neighbor_forms (p : ℕ) (u m n : IntVec) (a b : ℤ) :
    dot3 (castVec m + a • liftVec p u) (castVec n + b • liftVec p u) =
      ((dot3 m n : ℤ) : ℚ) + (a : ℚ) / (p : ℚ) * ((dot3 u n : ℤ) : ℚ) +
      (b : ℚ) / (p : ℚ) * ((dot3 u m : ℤ) : ℚ) +
      ((a : ℚ) / (p : ℚ)) * ((b : ℚ) / (p : ℚ)) * ((dot3 u u : ℤ) : ℚ) := by
  simp only [dot3, castVec, liftVec, Pi.add_apply, Pi.smul_apply, zsmul_eq_mul,
    Int.cast_add, Int.cast_mul, Pi.mul_apply, Pi.intCast_def, Pi.natCast_def]
  ring

/-- Every inner product of two vectors in N is an integer. -/
theorem neighbor_integral (p : ℕ) (hp0 : p ≠ 0) (u : IntVec)
    (hQ : (p : ℤ) ^ 2 ∣ dot3 u u) (x y : RatVec)
    (hx : x ∈ neighbor p u) (hy : y ∈ neighbor p u) :
    ∃ k : ℤ, dot3 x y = (k : ℚ) := by
  have hpq : (p : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr hp0
  rcases hx with ⟨m, a, hm, rfl⟩
  rcases hy with ⟨n, b, hn, rfl⟩
  rcases hm with ⟨km, hkm⟩
  rcases hn with ⟨kn, hkn⟩
  rcases hQ with ⟨kQ, hkQ⟩
  have hkm' : ((dot3 u m : ℤ) : ℚ) = (p : ℚ) * (km : ℚ) := by
    exact_mod_cast hkm
  have hkn' : ((dot3 u n : ℤ) : ℚ) = (p : ℚ) * (kn : ℚ) := by
    exact_mod_cast hkn
  have hkQ' : ((dot3 u u : ℤ) : ℚ) = (p : ℚ) ^ 2 * (kQ : ℚ) := by
    exact_mod_cast hkQ
  refine ⟨dot3 m n + a * kn + b * km + a * b * kQ, ?_⟩
  rw [dot3_neighbor_forms, hkm', hkn', hkQ']
  push_cast
  field_simp [hpq] <;> ring

/-- The intersection of the standard lattice and its neighbor is exactly M.
Only primality, nonzero reduction of u, and p | Q(u) are needed here. -/
theorem standard_inf_neighbor (p : ℕ) (hp : p.Prime) (u : IntVec)
    (hu : ∃ i : Fin 3, ¬(p : ℤ) ∣ u i) (hQ : (p : ℤ) ∣ dot3 u u) :
    standard ⊓ neighbor p u = midpoint p u := by
  have hpq : (p : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr hp.ne_zero
  apply le_antisymm
  · intro x hx
    rcases hx.1 with ⟨l, hl⟩
    rcases hx.2 with ⟨m, a, hm, heq⟩
    obtain ⟨i, hui⟩ := hu
    have hcoord : (m i : ℚ) + (a : ℚ) * ((u i : ℚ) / (p : ℚ)) = (l i : ℚ) := by
      simpa only [Pi.add_apply, Pi.smul_apply, zsmul_eq_mul, castVec, liftVec]
        using congrFun (heq.trans hl.symm) i
    have hrelationQ : (p : ℚ) * ((l i : ℚ) - (m i : ℚ)) =
        (a : ℚ) * (u i : ℚ) := by
      rw [← hcoord]
      field_simp [hpq] <;> ring
    have hrelation : (p : ℤ) * (l i - m i) = a * u i := by
      exact_mod_cast hrelationQ
    have hdiv : (p : ℤ) ∣ a * u i := ⟨l i - m i, hrelation.symm⟩
    have ha : (p : ℤ) ∣ a :=
      ((Nat.prime_iff_prime_int.mp hp).dvd_or_dvd hdiv).resolve_right hui
    rcases ha with ⟨b, hb⟩
    refine ⟨m + b • u, ?_, ?_⟩
    · rw [dot3_add_right, dot3_smul_right]
      exact dvd_add hm (dvd_mul_of_dvd_right hQ b)
    · calc
        castVec (m + b • u) = castVec m + b • castVec u := by simp
        _ = castVec m + b • ((p : ℤ) • liftVec p u) := by
          rw [p_smul_liftVec p hp.ne_zero u]
        _ = castVec m + ((p : ℤ) * b) • liftVec p u := by
          rw [smul_smul, mul_comm b (p : ℤ)]
        _ = x := by rw [← hb]; exact heq
  · intro x hx
    exact ⟨midpoint_le_standard p u hx, midpoint_le_neighbor p u hx⟩

/-! The two relative indices, proved by quotient/kernel equivalences. -/

def dotMod (p : ℕ) (u : IntVec) : IntVec →ₗ[ℤ] ZMod p where
  toFun m := ((dot3 u m : ℤ) : ZMod p)
  map_add' := by
    intro m n
    simp only [dot3_add_right, Int.cast_add]
  map_smul' := by
    intro a m
    change ((dot3 u (a • m) : ℤ) : ZMod p) = a • ((dot3 u m : ℤ) : ZMod p)
    rw [dot3_smul_right]
    simp only [Int.cast_mul, zsmul_eq_mul]

@[simp] theorem dotMod_apply (p : ℕ) (u m : IntVec) :
    dotMod p u m = ((dot3 u m : ℤ) : ZMod p) := rfl

theorem dot3_single_right (u : IntVec) (i : Fin 3) (a : ℤ) :
    dot3 u (Pi.single i a) = u i * a := by
  fin_cases i <;> simp [dot3, Pi.single_apply]

theorem dotMod_surjective (p : ℕ) (hp : p.Prime) (u : IntVec)
    (hu : ∃ i : Fin 3, ¬(p : ℤ) ∣ u i) : Function.Surjective (dotMod p u) := by
  letI : Fact p.Prime := ⟨hp⟩
  letI : NeZero p := ⟨hp.ne_zero⟩
  obtain ⟨i, hui⟩ := hu
  have hui' : (u i : ZMod p) ≠ 0 := by
    intro h
    exact hui ((ZMod.intCast_zmod_eq_zero_iff_dvd (u i) p).mp h)
  intro x
  let t : ZMod p := x / (u i : ZMod p)
  refine ⟨Pi.single i (t.val : ℤ), ?_⟩
  rw [dotMod_apply, dot3_single_right]
  simp only [Int.cast_mul, Int.cast_natCast, ZMod.natCast_zmod_val]
  dsimp [t]
  field_simp [hui'] <;> ring

def castStandard : IntVec →ₗ[ℤ] standard where
  toFun m := ⟨castVec m, ⟨m, rfl⟩⟩
  map_add' := by
    intro m n
    apply Subtype.ext
    exact castVec_add m n
  map_smul' := by
    intro a m
    apply Subtype.ext
    exact castVec_smul a m

theorem castStandard_surjective : Function.Surjective castStandard := by
  rintro ⟨x, m, hm⟩
  refine ⟨m, ?_⟩
  apply Subtype.ext
  exact hm

def midpointInStandard (p : ℕ) (u : IntVec) : Submodule ℤ standard :=
  (midpoint p u).comap standard.subtype

def midpointInNeighbor (p : ℕ) (u : IntVec) : Submodule ℤ (neighbor p u) :=
  (midpoint p u).comap (neighbor p u).subtype

/-- The quotient L0/M has precisely p elements. -/
theorem card_standard_quotient_midpoint (p : ℕ) (hp : p.Prime) (u : IntVec)
    (hu : ∃ i : Fin 3, ¬(p : ℤ) ∣ u i) :
    Nat.card (standard ⧸ midpointInStandard p u) = p := by
  letI : NeZero p := ⟨hp.ne_zero⟩
  let g : IntVec →ₗ[ℤ] standard ⧸ midpointInStandard p u :=
    (midpointInStandard p u).mkQ.comp castStandard
  have hg : Function.Surjective g :=
    (midpointInStandard p u).mkQ_surjective.comp castStandard_surjective
  have hker : LinearMap.ker g = LinearMap.ker (dotMod p u) := by
    ext m
    change (Submodule.Quotient.mk (castStandard m) :
      standard ⧸ midpointInStandard p u) = 0 ↔ ((dot3 u m : ℤ) : ZMod p) = 0
    rw [Submodule.Quotient.mk_eq_zero]
    change castVec m ∈ midpoint p u ↔ ((dot3 u m : ℤ) : ZMod p) = 0
    rw [castVec_mem_midpoint_iff, ZMod.intCast_zmod_eq_zero_iff_dvd]
  calc
    Nat.card (standard ⧸ midpointInStandard p u) = Nat.card (IntVec ⧸ LinearMap.ker g) :=
      (Nat.card_congr (g.quotKerEquivOfSurjective hg).toEquiv).symm
    _ = Nat.card (IntVec ⧸ LinearMap.ker (dotMod p u)) :=
      Nat.card_congr (Submodule.quotEquivOfEq _ _ hker).toEquiv
    _ = Nat.card (ZMod p) :=
      Nat.card_congr ((dotMod p u).quotKerEquivOfSurjective
        (dotMod_surjective p hp u hu)).toEquiv
    _ = p := by simp [Nat.card_eq_fintype_card, ZMod.card]

/-- The coefficient of u/p lies in M exactly when it is divisible by p. -/
theorem smul_liftVec_mem_midpoint_iff (p : ℕ) (hp : p.Prime) (u : IntVec)
    (hu : ∃ i : Fin 3, ¬(p : ℤ) ∣ u i) (hQ : (p : ℤ) ∣ dot3 u u) (a : ℤ) :
    a • liftVec p u ∈ midpoint p u ↔ (p : ℤ) ∣ a := by
  have hpq : (p : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr hp.ne_zero
  constructor
  · rintro ⟨m, hm, heq⟩
    obtain ⟨i, hui⟩ := hu
    have hi : (m i : ℚ) = (a : ℚ) * ((u i : ℚ) / (p : ℚ)) := by
      simpa only [castVec, liftVec, Pi.smul_apply, zsmul_eq_mul] using congrFun heq i
    have hrQ : (p : ℚ) * (m i : ℚ) = (a : ℚ) * (u i : ℚ) := by
      rw [hi]
      field_simp [hpq] <;> ring
    have hr : (p : ℤ) * m i = a * u i := by exact_mod_cast hrQ
    have hd : (p : ℤ) ∣ a * u i := ⟨m i, hr.symm⟩
    exact ((Nat.prime_iff_prime_int.mp hp).dvd_or_dvd hd).resolve_right hui
  · rintro ⟨b, rfl⟩
    refine ⟨b • u, ?_, ?_⟩
    · rw [dot3_smul_right]
      exact dvd_mul_of_dvd_right hQ b
    · calc
        castVec (b • u) = b • castVec u := castVec_smul b u
        _ = b • ((p : ℤ) • liftVec p u) := by rw [p_smul_liftVec p hp.ne_zero u]
        _ = ((p : ℤ) * b) • liftVec p u := by rw [smul_smul, mul_comm b (p : ℤ)]

def neighborGenerator (p : ℕ) (u : IntVec) : ℤ →ₗ[ℤ] neighbor p u :=
  LinearMap.toSpanSingleton ℤ (neighbor p u) ⟨liftVec p u, liftVec_mem_neighbor p u⟩

def intCastMod (p : ℕ) : ℤ →ₗ[ℤ] ZMod p where
  toFun a := (a : ZMod p)
  map_add' := by intro a b; simp
  map_smul' := by intro a b; simp [Int.zsmul_eq_mul, zsmul_eq_mul]

theorem intCastMod_surjective (p : ℕ) (hp0 : p ≠ 0) :
    Function.Surjective (intCastMod p) := by
  letI : NeZero p := ⟨hp0⟩
  intro x
  exact ⟨(x.val : ℤ), by simp [intCastMod, ZMod.natCast_zmod_val]⟩

/-- The quotient N/M has precisely p elements. -/
theorem card_neighbor_quotient_midpoint (p : ℕ) (hp : p.Prime) (u : IntVec)
    (hu : ∃ i : Fin 3, ¬(p : ℤ) ∣ u i) (hQ : (p : ℤ) ∣ dot3 u u) :
    Nat.card ((neighbor p u) ⧸ midpointInNeighbor p u) = p := by
  letI : NeZero p := ⟨hp.ne_zero⟩
  let g : ℤ →ₗ[ℤ] (neighbor p u) ⧸ midpointInNeighbor p u :=
    (midpointInNeighbor p u).mkQ.comp (neighborGenerator p u)
  have hg : Function.Surjective g := by
    intro y
    obtain ⟨x, rfl⟩ := (midpointInNeighbor p u).mkQ_surjective y
    rcases x.property with ⟨m, a, hm, heq⟩
    refine ⟨a, ?_⟩
    change (Submodule.Quotient.mk (neighborGenerator p u a) :
      (neighbor p u) ⧸ midpointInNeighbor p u) = Submodule.Quotient.mk x
    rw [Submodule.Quotient.eq]
    change a • liftVec p u - (x : RatVec) ∈ midpoint p u
    have heq' : a • liftVec p u - (x : RatVec) = -castVec m := by
      rw [← heq]
      abel
    rw [heq']
    exact (midpoint p u).neg_mem ⟨m, hm, rfl⟩
  have hker : LinearMap.ker g = LinearMap.ker (intCastMod p) := by
    ext a
    change (Submodule.Quotient.mk (neighborGenerator p u a) :
      (neighbor p u) ⧸ midpointInNeighbor p u) = 0 ↔ (a : ZMod p) = 0
    rw [Submodule.Quotient.mk_eq_zero, ZMod.intCast_zmod_eq_zero_iff_dvd]
    change a • liftVec p u ∈ midpoint p u ↔ (p : ℤ) ∣ a
    exact smul_liftVec_mem_midpoint_iff p hp u hu hQ a
  calc
    Nat.card ((neighbor p u) ⧸ midpointInNeighbor p u) =
        Nat.card (ℤ ⧸ LinearMap.ker g) :=
      (Nat.card_congr (g.quotKerEquivOfSurjective hg).toEquiv).symm
    _ = Nat.card (ℤ ⧸ LinearMap.ker (intCastMod p)) :=
      Nat.card_congr (Submodule.quotEquivOfEq _ _ hker).toEquiv
    _ = Nat.card (ZMod p) :=
      Nat.card_congr ((intCastMod p).quotKerEquivOfSurjective
        (intCastMod_surjective p hp.ne_zero)).toEquiv
    _ = p := by simp [Nat.card_eq_fintype_card, ZMod.card]

theorem midpoint_relIndex_standard (p : ℕ) (hp : p.Prime) (u : IntVec)
    (hu : ∃ i : Fin 3, ¬(p : ℤ) ∣ u i) :
    (midpoint p u).toAddSubgroup.relIndex standard.toAddSubgroup = p := by
  change Nat.card (standard ⧸ midpointInStandard p u) = p
  exact card_standard_quotient_midpoint p hp u hu

theorem midpoint_relIndex_neighbor (p : ℕ) (hp : p.Prime) (u : IntVec)
    (hu : ∃ i : Fin 3, ¬(p : ℤ) ∣ u i) (hQ : (p : ℤ) ∣ dot3 u u) :
    (midpoint p u).toAddSubgroup.relIndex (neighbor p u).toAddSubgroup = p := by
  change Nat.card ((neighbor p u) ⧸ midpointInNeighbor p u) = p
  exact card_neighbor_quotient_midpoint p hp u hu hQ

/-! The exterior-vector membership criterion, before projective quotients. -/

theorem dot3_isotropic_decomposition (p : ℕ) (u m : IntVec) (a : ℤ) :
    dot3 (a • u + (p : ℤ) • m) (a • u + (p : ℤ) • m) =
      a ^ 2 * dot3 u u + 2 * a * (p : ℤ) * dot3 u m +
      (p : ℤ) ^ 2 * dot3 m m := by
  simp only [dot3, Pi.add_apply, Pi.smul_apply, Int.zsmul_eq_mul]
  ring

/-- Isotropy modulo p² forces the correction m into the perpendicular kernel. -/
theorem midpoint_condition_of_isotropic_decomposition
    (p : ℕ) (hp : p.Prime) (hp2 : p ≠ 2) (u m : IntVec) (a : ℤ)
    (ha : ¬(p : ℤ) ∣ a) (hQu : (p : ℤ) ^ 2 ∣ dot3 u u)
    (hQv : (p : ℤ) ^ 2 ∣
      dot3 (a • u + (p : ℤ) • m) (a • u + (p : ℤ) • m)) :
    (p : ℤ) ∣ dot3 u m := by
  have hpz : (p : ℤ) ≠ 0 := Int.natCast_ne_zero.mpr hp.ne_zero
  have hprime : Prime (p : ℤ) := Nat.prime_iff_prime_int.mp hp
  have h2a : ¬(p : ℤ) ∣ 2 * a := by
    intro h
    rcases hprime.dvd_or_dvd h with htwo | ha'
    · have htwo' : p ∣ 2 := Int.natCast_dvd_natCast.mp htwo
      exact hp2 (Nat.le_antisymm (Nat.le_of_dvd (by decide) htwo') hp.two_le)
    · exact ha ha'
  rcases hQu with ⟨ku, hku⟩
  rcases hQv with ⟨kv, hkv⟩
  have hEq : (p : ℤ) ^ 2 * kv =
      a ^ 2 * ((p : ℤ) ^ 2 * ku) + 2 * a * (p : ℤ) * dot3 u m +
        (p : ℤ) ^ 2 * dot3 m m := by
    rw [← hkv, dot3_isotropic_decomposition, hku]
  have hcancel : (p : ℤ) * (2 * a * dot3 u m) =
      (p : ℤ) * ((p : ℤ) * (kv - a ^ 2 * ku - dot3 m m)) := by
    calc
      (p : ℤ) * (2 * a * dot3 u m) =
          (a ^ 2 * ((p : ℤ) ^ 2 * ku) + 2 * a * (p : ℤ) * dot3 u m +
            (p : ℤ) ^ 2 * dot3 m m) - a ^ 2 * ((p : ℤ) ^ 2 * ku) -
              (p : ℤ) ^ 2 * dot3 m m := by ring
      _ = (p : ℤ) ^ 2 * kv - a ^ 2 * ((p : ℤ) ^ 2 * ku) -
          (p : ℤ) ^ 2 * dot3 m m := by rw [← hEq]
      _ = (p : ℤ) * ((p : ℤ) * (kv - a ^ 2 * ku - dot3 m m)) := by ring
  have hdiv : (p : ℤ) ∣ 2 * a * dot3 u m :=
    ⟨kv - a ^ 2 * ku - dot3 m m, mul_left_cancel₀ hpz hcancel⟩
  exact (hprime.dvd_or_dvd hdiv).resolve_left h2a

theorem p_smul_normal_form (p : ℕ) (hp0 : p ≠ 0) (u m : IntVec) (a : ℤ) :
    (p : ℤ) • (castVec m + a • liftVec p u) =
      castVec ((p : ℤ) • m + a • u) := by
  calc
    (p : ℤ) • (castVec m + a • liftVec p u) =
        (p : ℤ) • castVec m + a • ((p : ℤ) • liftVec p u) := by
      rw [smul_add, smul_comm (p : ℤ) a]
    _ = (p : ℤ) • castVec m + a • castVec u := by rw [p_smul_liftVec p hp0 u]
    _ = castVec ((p : ℤ) • m + a • u) := by simp

theorem divided_decomposition_mem_neighbor (p : ℕ) (hp : p.Prime) (hp2 : p ≠ 2)
    (u m : IntVec) (a : ℤ) (ha : ¬(p : ℤ) ∣ a)
    (hQu : (p : ℤ) ^ 2 ∣ dot3 u u)
    (hQv : (p : ℤ) ^ 2 ∣
      dot3 (a • u + (p : ℤ) • m) (a • u + (p : ℤ) • m)) :
    liftVec p (a • u + (p : ℤ) • m) ∈ neighbor p u := by
  have hpq : (p : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr hp.ne_zero
  refine ⟨m, a, midpoint_condition_of_isotropic_decomposition p hp hp2 u m a ha hQu hQv, ?_⟩
  funext i
  simp only [castVec, liftVec, Pi.add_apply, Pi.smul_apply, zsmul_eq_mul,
    Int.cast_add, Int.cast_mul, Int.cast_natCast, Pi.mul_apply, Pi.intCast_def, Pi.natCast_def]
  push_cast
  field_simp [hpq] <;> ring

/-- The concrete normal form of v/p yields v=a*u+p*m over the integers. -/
theorem decomposition_of_divided_mem_neighbor (p : ℕ) (hp0 : p ≠ 0)
    (u v : IntVec) (hv : liftVec p v ∈ neighbor p u) :
    ∃ (a : ℤ) (m : IntVec), (p : ℤ) ∣ dot3 u m ∧ v = a • u + (p : ℤ) • m := by
  rcases hv with ⟨m, a, hm, heq⟩
  have hcasts : castVec ((p : ℤ) • m + a • u) = castVec v := by
    calc
      castVec ((p : ℤ) • m + a • u) =
          (p : ℤ) • (castVec m + a • liftVec p u) := (p_smul_normal_form p hp0 u m a).symm
      _ = (p : ℤ) • liftVec p v := congrArg (fun x : RatVec => (p : ℤ) • x) heq
      _ = castVec v := p_smul_liftVec p hp0 v
  have hInt := castVec_injective hcasts
  refine ⟨a, m, hm, ?_⟩
  rw [add_comm] at hInt
  exact hInt.symm

/-- Exterior vectors belong to the neighbor precisely when their nonzero
reductions lie on the line spanned by the chosen normalized u. -/
theorem exterior_neighbor_membership_iff
    (p : ℕ) (hp : p.Prime) (hp2 : p ≠ 2) (u v : IntVec)
    (hv : ∃ i : Fin 3, ¬(p : ℤ) ∣ v i)
    (hQu : (p : ℤ) ^ 2 ∣ dot3 u u) (hQv : (p : ℤ) ^ 2 ∣ dot3 v v) :
    liftVec p v ∈ neighbor p u ↔
      ∃ a : ℤ, ¬(p : ℤ) ∣ a ∧ ∀ i : Fin 3, (p : ℤ) ∣ v i - a * u i := by
  constructor
  · intro hmem
    obtain ⟨a, m, hm, hveq⟩ := decomposition_of_divided_mem_neighbor p hp.ne_zero u v hmem
    have ha : ¬(p : ℤ) ∣ a := by
      rintro ⟨b, hb⟩
      obtain ⟨i, hvi⟩ := hv
      apply hvi
      refine ⟨b * u i + m i, ?_⟩
      have hi := congrFun hveq i
      simp only [Pi.add_apply, Pi.smul_apply, Int.zsmul_eq_mul] at hi
      rw [hi, hb]
      ring
    refine ⟨a, ha, ?_⟩
    intro i
    refine ⟨m i, ?_⟩
    have hi := congrFun hveq i
    simp only [Pi.add_apply, Pi.smul_apply, Int.zsmul_eq_mul] at hi
    rw [hi]
    ring
  · rintro ⟨a, ha, hcong⟩
    let m : IntVec := fun i => (hcong i).choose
    have hm (i : Fin 3) : v i - a * u i = (p : ℤ) * m i := (hcong i).choose_spec
    have hveq : v = a • u + (p : ℤ) • m := by
      funext i
      change v i = a * u i + (p : ℤ) * m i
      rw [← hm i]
      ring
    have hQv' : (p : ℤ) ^ 2 ∣
        dot3 (a • u + (p : ℤ) • m) (a • u + (p : ℤ) • m) := by
      rw [← hveq]
      exact hQv
    rw [hveq]
    exact divided_decomposition_mem_neighbor p hp hp2 u m a ha hQu hQv'

end A354766Research.Neighbor

#print axioms A354766Research.Neighbor.standard
#print axioms A354766Research.Neighbor.midpoint
#print axioms A354766Research.Neighbor.neighbor
#print axioms A354766Research.Neighbor.p_smul_standard_mem_midpoint
#print axioms A354766Research.Neighbor.p_smul_neighbor_mem_midpoint
#print axioms A354766Research.Neighbor.neighbor_integral
#print axioms A354766Research.Neighbor.standard_inf_neighbor
#print axioms A354766Research.Neighbor.dotMod_surjective
#print axioms A354766Research.Neighbor.card_standard_quotient_midpoint
#print axioms A354766Research.Neighbor.smul_liftVec_mem_midpoint_iff
#print axioms A354766Research.Neighbor.card_neighbor_quotient_midpoint
#print axioms A354766Research.Neighbor.midpoint_relIndex_standard
#print axioms A354766Research.Neighbor.midpoint_relIndex_neighbor
#print axioms A354766Research.Neighbor.midpoint_condition_of_isotropic_decomposition
#print axioms A354766Research.Neighbor.decomposition_of_divided_mem_neighbor
#print axioms A354766Research.Neighbor.exterior_neighbor_membership_iff
