import Mathlib.LinearAlgebra.Projectivization.Cardinality
import Mathlib.Data.Fin.VecNotation
import Mathlib.Data.Fintype.Option
import Mathlib.FieldTheory.Finite.Basic
import Mathlib.NumberTheory.LegendreSymbol.QuadraticChar.Basic
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Ring

/-!
# Explicit points of a split ternary conic

The parametrization below proves the projective conic count by an actual
equivalence, rather than by division of a nonzero-vector count.  It works over
every field, including fields of characteristic two.  The standard
three-squares bridge below requires characteristic different from two.
-/

namespace A354766Research.IsotropicLines

variable (F : Type*) [Field F]

abbrev Ternary := Fin 3 → F

/-- A representative of an isotropic projective line for `a*b = c^2`.
The existential formulation makes independence of the representative explicit. -/
def SplitIsotropic (P : Projectivization F (Ternary F)) : Prop :=
  ∃ (v : Ternary F) (hv : v ≠ 0),
    Projectivization.mk F v hv = P ∧ v 0 * v 1 = (v 2) ^ 2

abbrev SplitConic := {P : Projectivization F (Ternary F) // SplitIsotropic F P}

/-- The affine chart and the single point at infinity. -/
def chartVector : Option F → Ternary F
  | none => ![0, 1, 0]
  | some t => ![1, t ^ 2, t]

theorem chartVector_ne_zero (t : Option F) : chartVector F t ≠ 0 := by
  cases t with
  | none =>
      intro h
      have := congrFun h 1
      simpa [chartVector] using this
  | some t =>
      intro h
      have := congrFun h 0
      simpa [chartVector] using this

theorem chartVector_isotropic (t : Option F) :
    chartVector F t 0 * chartVector F t 1 = (chartVector F t 2) ^ 2 := by
  cases t <;> simp [chartVector]

def conicParam (t : Option F) : SplitConic F :=
  ⟨Projectivization.mk F (chartVector F t) (chartVector_ne_zero F t),
    chartVector F t, chartVector_ne_zero F t, rfl, chartVector_isotropic F t⟩

theorem conicParam_injective : Function.Injective (conicParam F) := by
  intro s t h
  have hp := congrArg Subtype.val h
  obtain ⟨a, ha⟩ :=
    (Projectivization.mk_eq_mk_iff' F (chartVector F s) (chartVector F t)
      (chartVector_ne_zero F s) (chartVector_ne_zero F t)).mp hp
  have h0 := congrFun ha 0
  have h1 := congrFun ha 1
  have h2 := congrFun ha 2
  cases s with
  | none =>
      cases t with
      | none => rfl
      | some t =>
          simp [chartVector] at h0 h1
          simp [h0] at h1
  | some s =>
      cases t with
      | none => simpa [chartVector] using h0
      | some t =>
          simp [chartVector] at h0 h2
          have hts : t = s := by simpa [h0] using h2
          exact congrArg some hts.symm

theorem conicParam_surjective : Function.Surjective (conicParam F) := by
  rintro ⟨P, v, hv, rfl, hq⟩
  by_cases h0 : v 0 = 0
  · have h2 : v 2 = 0 := by
      have hs : (v 2) ^ 2 = 0 := by simpa [h0] using hq.symm
      exact eq_zero_of_pow_eq_zero hs
    have h1 : v 1 ≠ 0 := by
      intro hh
      apply hv
      ext i
      fin_cases i <;> simp [h0, h2, hh]
    refine ⟨none, Subtype.ext ?_⟩
    apply (Projectivization.mk_eq_mk_iff' F _ _ _ _).mpr
    refine ⟨(v 1)⁻¹, ?_⟩
    ext i
    fin_cases i <;> simp [chartVector, h0, h2, h1]
  · refine ⟨some (v 2 / v 0), Subtype.ext ?_⟩
    apply (Projectivization.mk_eq_mk_iff' F _ _ _ _).mpr
    refine ⟨(v 0)⁻¹, ?_⟩
    ext i
    fin_cases i
    · simp [chartVector, h0]
    · change (v 0)⁻¹ * v 1 = (v 2 / v 0) ^ 2
      field_simp [h0]
      simpa [mul_comm] using hq
    · simp [chartVector, div_eq_mul_inv, mul_comm]

/-- Every split isotropic projective line has exactly one chart parameter. -/
noncomputable def splitConicEquiv : Option F ≃ SplitConic F :=
  Equiv.ofBijective (conicParam F)
    ⟨conicParam_injective F, conicParam_surjective F⟩

/-- A split ternary conic has `|F| + 1` projective isotropic lines. -/
theorem card_splitConic [Finite F] : Nat.card (SplitConic F) = Nat.card F + 1 := by
  classical
  letI : Fintype F := Fintype.ofFinite F
  rw [← Nat.card_congr (splitConicEquiv F)]
  simp only [Nat.card_eq_fintype_card, Fintype.card_option]

/-- The standard quadratic form on three coordinates. -/
def standardNorm (v : Ternary F) : F := v 0 ^ 2 + v 1 ^ 2 + v 2 ^ 2

def StandardIsotropic (P : Projectivization F (Ternary F)) : Prop :=
  ∃ (v : Ternary F) (hv : v ≠ 0),
    Projectivization.mk F v hv = P ∧ standardNorm F v = 0

abbrev StandardConic := {P : Projectivization F (Ternary F) // StandardIsotropic F P}

/-- Coordinates adapted to the isotropic vector `(a,b,1)`. -/
def toSplit (a b : F) : Ternary F →ₗ[F] Ternary F where
  toFun v := ![v 2 - a * v 0 - b * v 1, v 2 + a * v 0 + b * v 1,
    a * v 1 - b * v 0]
  map_add' v w := by ext i; fin_cases i <;> simp <;> ring
  map_smul' s v := by ext i; fin_cases i <;> simp <;> ring

def fromSplit (a b : F) : Ternary F →ₗ[F] Ternary F where
  toFun w := ![-a * (w 1 - w 0) / 2 + b * w 2,
    -b * (w 1 - w 0) / 2 - a * w 2, (w 0 + w 1) / 2]
  map_add' v w := by ext i; fin_cases i <;> simp <;> ring
  map_smul' s v := by ext i; fin_cases i <;> simp <;> ring

theorem fromSplit_toSplit (a b : F) (hab : a ^ 2 + b ^ 2 = -1)
    (h2 : (2 : F) ≠ 0) (v : Ternary F) :
    fromSplit F a b (toSplit F a b v) = v := by
  ext i
  fin_cases i
  · change -a * ((v 2 + a * v 0 + b * v 1) -
        (v 2 - a * v 0 - b * v 1)) / 2 + b * (a * v 1 - b * v 0) = v 0
    field_simp [h2]
    linear_combination -2 * v 0 * hab
  · change -b * ((v 2 + a * v 0 + b * v 1) -
        (v 2 - a * v 0 - b * v 1)) / 2 - a * (a * v 1 - b * v 0) = v 1
    field_simp [h2]
    linear_combination -2 * v 1 * hab
  · change ((v 2 - a * v 0 - b * v 1) +
        (v 2 + a * v 0 + b * v 1)) / 2 = v 2
    field_simp [h2] <;> ring

theorem toSplit_fromSplit (a b : F) (hab : a ^ 2 + b ^ 2 = -1)
    (h2 : (2 : F) ≠ 0) (w : Ternary F) :
    toSplit F a b (fromSplit F a b w) = w := by
  ext i
  fin_cases i
  · change (w 0 + w 1) / 2 -
        a * (-a * (w 1 - w 0) / 2 + b * w 2) -
        b * (-b * (w 1 - w 0) / 2 - a * w 2) = w 0
    field_simp [h2]
    linear_combination (w 1 - w 0) * hab
  · change (w 0 + w 1) / 2 +
        a * (-a * (w 1 - w 0) / 2 + b * w 2) +
        b * (-b * (w 1 - w 0) / 2 - a * w 2) = w 1
    field_simp [h2]
    linear_combination (w 0 - w 1) * hab
  · change a * (-b * (w 1 - w 0) / 2 - a * w 2) -
        b * (-a * (w 1 - w 0) / 2 + b * w 2) = w 2
    field_simp [h2]
    linear_combination -2 * w 2 * hab

/-- The explicit invertible change to split coordinates. -/
def splitLinearEquiv (a b : F) (hab : a ^ 2 + b ^ 2 = -1)
    (h2 : (2 : F) ≠ 0) : Ternary F ≃ₗ[F] Ternary F where
  toLinearMap := toSplit F a b
  invFun := fromSplit F a b
  left_inv := fromSplit_toSplit F a b hab h2
  right_inv := toSplit_fromSplit F a b hab h2

theorem toSplit_norm (a b : F) (hab : a ^ 2 + b ^ 2 = -1)
    (v : Ternary F) :
    toSplit F a b v 0 * toSplit F a b v 1 - (toSplit F a b v 2) ^ 2 =
      standardNorm F v := by
  simp only [toSplit, standardNorm, LinearMap.coe_mk, AddHom.coe_mk,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one,
      Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons]
  linear_combination -(v 0 ^ 2 + v 1 ^ 2) * hab

def projectiveEquiv (e : Ternary F ≃ₗ[F] Ternary F) :
    Projectivization F (Ternary F) ≃ Projectivization F (Ternary F) where
  toFun := Projectivization.map e.toLinearMap e.injective
  invFun := Projectivization.map e.symm.toLinearMap e.symm.injective
  left_inv P := by
    induction P using Projectivization.ind with
    | h v hv => simp only [Projectivization.map_mk, LinearEquiv.coe_coe,
        LinearEquiv.symm_apply_apply]
  right_inv P := by
    induction P using Projectivization.ind with
    | h v hv => simp only [Projectivization.map_mk, LinearEquiv.coe_coe,
        LinearEquiv.apply_symm_apply]

theorem standard_iff_split (a b : F) (hab : a ^ 2 + b ^ 2 = -1)
    (h2 : (2 : F) ≠ 0) (P : Projectivization F (Ternary F)) :
    StandardIsotropic F P ↔
      SplitIsotropic F (projectiveEquiv F (splitLinearEquiv F a b hab h2) P) := by
  let e := splitLinearEquiv F a b hab h2
  constructor
  · rintro ⟨v, hv, rfl, hq⟩
    refine ⟨e v, e.map_ne_zero_iff.mpr hv, rfl, ?_⟩
    apply sub_eq_zero.mp
    exact (toSplit_norm F a b hab v).trans hq
  · rintro ⟨w, hw, hwP, hq⟩
    refine ⟨e.symm w, e.symm.map_ne_zero_iff.mpr hw, ?_, ?_⟩
    · apply (projectiveEquiv F e).injective
      change Projectivization.map e.toLinearMap e.injective
        (Projectivization.mk F (e.symm w) _) = _
      simpa only [Projectivization.map_mk, LinearEquiv.coe_coe,
        LinearEquiv.apply_symm_apply] using hwP
    · have hn := toSplit_norm F a b hab (e.symm w)
      change e (e.symm w) 0 * e (e.symm w) 1 - (e (e.symm w) 2) ^ 2 = _ at hn
      rw [e.apply_symm_apply] at hn
      exact hn.symm.trans (sub_eq_zero.mpr hq)

/-- A standard conic count given an isotropic vector `(a,b,1)`. -/
theorem card_standardConic_of_sq_add_sq [Finite F] (a b : F)
    (hab : a ^ 2 + b ^ 2 = -1) (h2 : (2 : F) ≠ 0) :
    Nat.card (StandardConic F) = Nat.card F + 1 := by
  let e := Equiv.subtypeEquiv
    (projectiveEquiv F (splitLinearEquiv F a b hab h2))
    (standard_iff_split F a b hab h2)
  exact (Nat.card_congr e).trans (card_splitConic F)

/-- The standard ternary form has exactly `p+1` isotropic projective lines over
`ZMod p`, for every odd prime `p`. -/
theorem card_standardConic_zmod (p : ℕ) [hp : Fact p.Prime] (hp2 : p ≠ 2) :
    Nat.card (StandardConic (ZMod p)) = p + 1 := by
  obtain ⟨a, b, hab⟩ := ZMod.sq_add_sq p (-1)
  have h2 : (2 : ZMod p) ≠ 0 := by
    intro h
    have hd : p ∣ 2 := (ZMod.natCast_eq_zero_iff 2 p).mp h
    exact hp2 (Nat.le_antisymm (Nat.le_of_dvd (by decide) hd) hp.out.two_le)
  simpa only [Nat.card_zmod] using
    card_standardConic_of_sq_add_sq (ZMod p) a b hab h2

/-- The quadratic equation for a conic point perpendicular to `(A,B,C)`.
The infinity chart occurs precisely when `A=0`. -/
def SplitPerpParameter (A B C : F) : Option F → Prop
  | none => A = 0
  | some t => A * t ^ 2 - 2 * C * t + B = 0

theorem completing_square (A B C t : F) :
    (A * t - C) ^ 2 - (C ^ 2 - A * B) =
      A * (A * t ^ 2 - 2 * C * t + B) := by ring

def completingSquareEquiv (A B C : F) (hA : A ≠ 0) :
    {t : F // A * t ^ 2 - 2 * C * t + B = 0} ≃
      {s : F // s ^ 2 = C ^ 2 - A * B} where
  toFun t := ⟨A * t - C, by
    apply sub_eq_zero.mp
    rw [completing_square, t.property, mul_zero]⟩
  invFun s := ⟨(s + C) / A, by
    have hlin : A * ((s + C) / A) - C = s := by field_simp [hA] <;> ring
    have hh : A * (A * ((s + C) / A) ^ 2 - 2 * C * ((s + C) / A) + B) = 0 := by
      rw [← completing_square, hlin, s.property, sub_self]
    exact (mul_eq_zero.mp hh).resolve_left hA⟩
  left_inv t := by
    apply Subtype.ext
    change ((A * t - C + C) / A) = t
    field_simp [hA] <;> ring
  right_inv s := by
    apply Subtype.ext
    change A * ((s + C) / A) - C = s
    field_simp [hA] <;> ring

/-- Partition an `Option` subtype into its infinity and affine pieces. -/
def optionSubtypeSumEquiv {α : Type*} (P : Option α → Prop) :
    {t : Option α // P t} ≃ ({_u : Unit // P none} ⊕ {t : α // P (some t)}) where
  toFun := by
    rintro ⟨t, ht⟩
    cases t with
    | none => exact Sum.inl ⟨(), ht⟩
    | some t => exact Sum.inr ⟨t, ht⟩
  invFun := by
    rintro (⟨_, ht⟩ | ⟨t, ht⟩)
    · exact ⟨none, ht⟩
    · exact ⟨some t, ht⟩
  left_inv := by rintro ⟨(_ | t), ht⟩ <;> rfl
  right_inv := by
    rintro (⟨u, ht⟩ | ⟨t, ht⟩)
    · cases u; rfl
    · rfl

/-- The chart equation has `1+χ(C²-A*B)` parameters for a nonzero coefficient
triple. This includes the infinity point and both degenerate affine cases. -/
theorem card_splitPerpParameter [Fintype F] [DecidableEq F]
    (hchar : ringChar F ≠ 2) (A B C : F)
    (hne : ¬(A = 0 ∧ B = 0 ∧ C = 0)) :
    (Nat.card {t : Option F // SplitPerpParameter F A B C t} : ℤ) =
      quadraticChar F (C ^ 2 - A * B) + 1 := by
  classical
  have hcard : Nat.card {t : Option F // SplitPerpParameter F A B C t} =
      Nat.card {_u : Unit // A = 0} +
        Nat.card {t : F // A * t ^ 2 - 2 * C * t + B = 0} := by
    exact (Nat.card_congr (optionSubtypeSumEquiv (SplitPerpParameter F A B C))).trans
      (Nat.card_sum)
  by_cases hA : A = 0
  · have hinf : Nat.card {_u : Unit // A = 0} = 1 := by simp [hA]
    by_cases hC : C = 0
    · have hB : B ≠ 0 := fun hB => hne ⟨hA, hB, hC⟩
      have hfinite : Nat.card {t : F // A * t ^ 2 - 2 * C * t + B = 0} = 0 := by
        letI : IsEmpty {t : F // A * t ^ 2 - 2 * C * t + B = 0} :=
          ⟨by rintro ⟨t, ht⟩; exact hB (by simpa [hA, hC] using ht)⟩
        exact Nat.card_of_isEmpty
      rw [hcard, hinf, hfinite]
      simp [hA, hC]
    · have h2C : 2 * C ≠ 0 := mul_ne_zero (Ring.two_ne_zero hchar) hC
      have hroot (t : F) :
          A * t ^ 2 - 2 * C * t + B = 0 ↔ t = B / (2 * C) := by
        rw [eq_div_iff h2C]
        constructor
        · intro ht
          rw [hA] at ht
          linear_combination -ht
        · intro ht
          rw [hA]
          linear_combination -ht
      have hfinite : Nat.card {t : F // A * t ^ 2 - 2 * C * t + B = 0} = 1 := by
        apply Nat.card_eq_one_iff_exists.mpr
        refine ⟨⟨B / (2 * C), (hroot _).mpr rfl⟩, ?_⟩
        intro y
        exact Subtype.ext ((hroot y).mp y.property)
      rw [hcard, hinf, hfinite]
      simp [hA, quadraticChar_sq_one' (F := F) hC]
  · have hinf : Nat.card {_u : Unit // A = 0} = 0 := by
      letI : IsEmpty {_u : Unit // A = 0} := ⟨fun u => hA u.property⟩
      exact Nat.card_of_isEmpty
    have hsquare :
        (Nat.card {s : F // s ^ 2 = C ^ 2 - A * B} : ℤ) =
          quadraticChar F (C ^ 2 - A * B) + 1 := by
      have hn := Nat.card_eq_card_toFinset {s : F | s ^ 2 = C ^ 2 - A * B}
      exact (congrArg (fun n : ℕ => (n : ℤ)) hn).trans
        (quadraticChar_card_sqrts hchar _)
    have hfinite := Nat.card_congr (completingSquareEquiv F A B C hA)
    simpa only [hcard, hinf, zero_add, hfinite] using hsquare

/-- Twice the standard dot product in split coordinates. -/
def splitPolar (x : Ternary F) : Ternary F →ₗ[F] F where
  toFun y := x 0 * y 1 + x 1 * y 0 - 2 * x 2 * y 2
  map_add' v w := by simp; ring
  map_smul' s v := by simp; ring

abbrev SplitPerpConic (x : Ternary F) :=
  {P : SplitConic F // P.val.submodule ≤ (splitPolar F x).ker}

theorem splitPolar_chart_zero_iff (x : Ternary F) (t : Option F) :
    splitPolar F x (chartVector F t) = 0 ↔
      SplitPerpParameter F (x 0) (x 1) (x 2) t := by
  cases t with
  | none => simp [splitPolar, chartVector, SplitPerpParameter]
  | some t =>
      change x 0 * t ^ 2 + x 1 * 1 - 2 * x 2 * t = 0 ↔
        x 0 * t ^ 2 - 2 * x 2 * t + x 1 = 0
      rw [show x 0 * t ^ 2 + x 1 * 1 - 2 * x 2 * t =
        x 0 * t ^ 2 - 2 * x 2 * t + x 1 by ring]

noncomputable def splitPerpConicEquiv (x : Ternary F) :
    {t : Option F // SplitPerpParameter F (x 0) (x 1) (x 2) t} ≃
      SplitPerpConic F x :=
  Equiv.subtypeEquiv (splitConicEquiv F) (by
    intro t
    change SplitPerpParameter F (x 0) (x 1) (x 2) t ↔
      (Projectivization.mk F (chartVector F t) _).submodule ≤ (splitPolar F x).ker
    rw [Projectivization.submodule_mk, Submodule.span_singleton_le_iff_mem,
      LinearMap.mem_ker]
    exact (splitPolar_chart_zero_iff F x t).symm)

theorem card_splitPerpConic [Fintype F] [DecidableEq F]
    (hchar : ringChar F ≠ 2) (x : Ternary F) (hx : x ≠ 0) :
    (Nat.card (SplitPerpConic F x) : ℤ) =
      quadraticChar F ((x 2) ^ 2 - x 0 * x 1) + 1 := by
  have hne : ¬(x 0 = 0 ∧ x 1 = 0 ∧ x 2 = 0) := by
    rintro ⟨h0, h1, h2⟩
    apply hx
    ext i
    fin_cases i <;> simp [h0, h1, h2]
  rw [← Nat.card_congr (splitPerpConicEquiv F x)]
  exact card_splitPerpParameter F hchar (x 0) (x 1) (x 2) hne

/-- The standard dot product as a linear functional in its second variable. -/
def standardDot (x : Ternary F) : Ternary F →ₗ[F] F where
  toFun y := x 0 * y 0 + x 1 * y 1 + x 2 * y 2
  map_add' v w := by simp; ring
  map_smul' s v := by simp; ring

abbrev StandardPerpConic (x : Ternary F) :=
  {P : StandardConic F // P.val.submodule ≤ (standardDot F x).ker}

theorem card_standardPerpConic_zero :
    Nat.card (StandardPerpConic F 0) = Nat.card (StandardConic F) := by
  apply Nat.card_congr
  apply Equiv.subtypeUnivEquiv
  intro P v hv
  change standardDot F 0 v = 0
  simp [standardDot]

theorem toSplit_polar (a b : F) (hab : a ^ 2 + b ^ 2 = -1)
    (x y : Ternary F) :
    splitPolar F (toSplit F a b x) (toSplit F a b y) = 2 * standardDot F x y := by
  simp only [splitPolar, standardDot, toSplit, LinearMap.coe_mk, AddHom.coe_mk,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one,
    Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons]
  linear_combination -2 * (x 0 * y 0 + x 1 * y 1) * hab

def standardConicEquiv (a b : F) (hab : a ^ 2 + b ^ 2 = -1)
    (h2 : (2 : F) ≠ 0) : StandardConic F ≃ SplitConic F :=
  Equiv.subtypeEquiv (projectiveEquiv F (splitLinearEquiv F a b hab h2))
    (standard_iff_split F a b hab h2)

theorem standard_perp_iff_split (a b : F) (hab : a ^ 2 + b ^ 2 = -1)
    (h2 : (2 : F) ≠ 0) (x : Ternary F) (P : Projectivization F (Ternary F)) :
    P.submodule ≤ (standardDot F x).ker ↔
      (projectiveEquiv F (splitLinearEquiv F a b hab h2) P).submodule ≤
        (splitPolar F (toSplit F a b x)).ker := by
  induction P using Projectivization.ind with
  | h v hv =>
      change (Projectivization.mk F v hv).submodule ≤ (standardDot F x).ker ↔
        (Projectivization.mk F (toSplit F a b v) _).submodule ≤
          (splitPolar F (toSplit F a b x)).ker
      rw [Projectivization.submodule_mk, Projectivization.submodule_mk,
        Submodule.span_singleton_le_iff_mem, Submodule.span_singleton_le_iff_mem,
        LinearMap.mem_ker, LinearMap.mem_ker, toSplit_polar F a b hab]
      simp only [mul_eq_zero, h2, false_or]

def standardPerpConicEquiv (a b : F) (hab : a ^ 2 + b ^ 2 = -1)
    (h2 : (2 : F) ≠ 0) (x : Ternary F) :
    StandardPerpConic F x ≃ SplitPerpConic F (toSplit F a b x) :=
  Equiv.subtypeEquiv (standardConicEquiv F a b hab h2) (by
    intro P
    exact standard_perp_iff_split F a b hab h2 x P.val)

/-- The orthogonal-line count, with the exceptional zero vector excluded. -/
theorem card_standardPerpConic_of_sq_add_sq [Fintype F] [DecidableEq F]
    (hchar : ringChar F ≠ 2) (a b : F) (hab : a ^ 2 + b ^ 2 = -1)
    (x : Ternary F) (hx : x ≠ 0) :
    (Nat.card (StandardPerpConic F x) : ℤ) =
      quadraticChar F (-standardNorm F x) + 1 := by
  let h2 := Ring.two_ne_zero hchar
  let e := splitLinearEquiv F a b hab h2
  rw [Nat.card_congr (standardPerpConicEquiv F a b hab h2 x)]
  have hcount := card_splitPerpConic F hchar (e x) (e.map_ne_zero_iff.mpr hx)
  have hdisc : (e x 2) ^ 2 - e x 0 * e x 1 = -standardNorm F x := by
    change (toSplit F a b x 2) ^ 2 - toSplit F a b x 0 * toSplit F a b x 1 = _
    linear_combination -(toSplit_norm F a b hab x)
  simpa only [hdisc] using hcount

/-- The companion of `card_standardConic_zmod`: for a nonzero vector `x`,
exactly `1+χ(-Q(x))` isotropic projective lines lie in its perpendicular plane. -/
theorem card_standardPerpConic_zmod (p : ℕ) [Fact p.Prime] (hp2 : p ≠ 2)
    (x : Ternary (ZMod p)) (hx : x ≠ 0) :
    (Nat.card (StandardPerpConic (ZMod p) x) : ℤ) =
      quadraticChar (ZMod p) (-standardNorm (ZMod p) x) + 1 := by
  classical
  obtain ⟨a, b, hab⟩ := ZMod.sq_add_sq p (-1)
  have hchar : ringChar (ZMod p) ≠ 2 := by
    simpa only [ZMod.ringChar_zmod_n] using hp2
  exact card_standardPerpConic_of_sq_add_sq (ZMod p) hchar a b hab x hx

theorem card_standardPerpConic_zmod_zero (p : ℕ) [Fact p.Prime] (hp2 : p ≠ 2) :
    Nat.card (StandardPerpConic (ZMod p) 0) = p + 1 := by
  rw [card_standardPerpConic_zero, card_standardConic_zmod p hp2]

end A354766Research.IsotropicLines

#print axioms A354766Research.IsotropicLines.card_standardConic_zmod
#print axioms A354766Research.IsotropicLines.card_standardPerpConic_zmod
#print axioms A354766Research.IsotropicLines.card_standardPerpConic_zmod_zero
