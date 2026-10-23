import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Data.Rat.Cast.Order
import Mathlib.Tactic.Ring

/-!
Embed the rational coordinate model of a neighbor into the Euclidean space
used by the small-lattice theorem. The map is integral-linear and injective;
it identifies the rational dot product with the real inner product.
-/

noncomputable section

open scoped RealInnerProductSpace

namespace A354766Neighbors

abbrev RationalVector := Fin 3 → ℚ
abbrev RealTernarySpace := EuclideanSpace ℝ (Fin 3)

def rationalDot (v w : RationalVector) : ℚ :=
  v 0 * w 0 + v 1 * w 1 + v 2 * w 2

def rationalToReal : RationalVector →ₗ[ℤ] RealTernarySpace where
  toFun v := WithLp.toLp 2 (fun i => (v i : ℝ))
  map_add' := by
    intro v w
    ext i
    simp
  map_smul' := by
    intro n v
    ext i
    simp [Pi.smul_apply, PiLp.smul_apply, zsmul_eq_mul]

@[simp] theorem rationalToReal_apply (v : RationalVector) (i : Fin 3) :
    rationalToReal v i = (v i : ℝ) := rfl

theorem rationalToReal_injective : Function.Injective rationalToReal := by
  intro v w h
  funext i
  have hi := congrArg (fun x : RealTernarySpace => x i) h
  change (v i : ℝ) = (w i : ℝ) at hi
  exact Rat.cast_injective hi

theorem inner_rationalToReal (v w : RationalVector) :
    ⟪rationalToReal v, rationalToReal w⟫ = (rationalDot v w : ℝ) := by
  simp [rationalToReal, EuclideanSpace.inner_eq_star_dotProduct, dotProduct,
    rationalDot, Fin.sum_univ_succ, mul_comm] <;> ring

def realify (L : Submodule ℤ RationalVector) : Submodule ℤ RealTernarySpace :=
  L.map rationalToReal

def realifyMap (L : Submodule ℤ RationalVector) : L →ₗ[ℤ] realify L where
  toFun x := ⟨rationalToReal x.1, ⟨x.1, x.property, rfl⟩⟩
  map_add' := by
    intro x y
    apply Subtype.ext
    exact rationalToReal.map_add x.1 y.1
  map_smul' := by
    intro n x
    apply Subtype.ext
    exact rationalToReal.map_smul n x.1

theorem realifyMap_bijective (L : Submodule ℤ RationalVector) :
    Function.Bijective (realifyMap L) := by
  constructor
  · intro x y h
    apply Subtype.ext
    apply rationalToReal_injective
    exact congrArg (fun z : realify L => (z : RealTernarySpace)) h
  · rintro ⟨x, hx⟩
    rcases hx with ⟨v, hv, rfl⟩
    exact ⟨⟨v, hv⟩, rfl⟩

def realifyEquiv (L : Submodule ℤ RationalVector) : L ≃ₗ[ℤ] realify L :=
  LinearEquiv.ofBijective (realifyMap L) (realifyMap_bijective L)

theorem realify_integral (L : Submodule ℤ RationalVector)
    (hL : ∀ v ∈ L, ∀ w ∈ L, ∃ z : ℤ, rationalDot v w = (z : ℚ)) :
    ∀ x ∈ realify L, ∀ y ∈ realify L, ∃ z : ℤ, ⟪x, y⟫ = (z : ℝ) := by
  rintro x ⟨v, hv, rfl⟩ y ⟨w, hw, rfl⟩
  obtain ⟨z, hz⟩ := hL v hv w hw
  refine ⟨z, ?_⟩
  rw [inner_rationalToReal, hz]
  simp

end A354766Neighbors

#print axioms A354766Neighbors.rationalToReal_injective
#print axioms A354766Neighbors.inner_rationalToReal
#print axioms A354766Neighbors.realify_integral
