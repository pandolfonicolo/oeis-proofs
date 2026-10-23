import A354766.StandardRealLattice
import A354766.PrimitiveNeighborAlgebra
import A354766.PrimitiveVectorModel
import A354766.ShellEquivalence

/-!
Actual normalized neighbor shells have the historical primitive three-square
cardinality. The lattice coordinate equivalence is constructed by the proved
small-lattice classification, and every shell identification is an equivalence.
No shell cardinality or representation recurrence is assumed.
-/

noncomputable section

namespace A354766Neighbors

open A354766Research.Neighbor

/-- Integer norm levels and the recovered primitive-content model agree. -/
def rationalPrimitiveVectorShellEquiv (n : ℕ) :
    {v : IntegerVector // (vectorNorm v : ℚ) = (n : ℚ) ∧ PrimitiveElement v} ≃
      PrimitiveVectorShell n :=
  Equiv.subtypeEquivRight (fun v => by
    have hnorm : (vectorNorm v : ℚ) = (n : ℚ) ↔ vectorNorm v = (n : ℤ) := by
      constructor <;> intro h <;> exact_mod_cast h
    have hprimitive : PrimitiveElement v ↔ vectorContent v = 1 :=
      (vectorContent_eq_one_iff_primitive v).symm
    exact and_congr hnorm hprimitive)

/-- Explicit integral norm coordinates identify primitive shells. -/
def coordinatePrimitiveShellEquiv {U : Type*} [AddCommGroup U]
    (e : U ≃ₗ[ℤ] IntegerVector) (Q : U → ℚ)
    (he : ∀ x, (vectorNorm (e x) : ℚ) = Q x) (n : ℕ) :
    {x : U // Q x = (n : ℚ) ∧ PrimitiveElement x} ≃ PrimitiveVectorShell n :=
  (primitiveShellEquiv e Q (fun v => (vectorNorm v : ℚ)) he (n : ℚ)).trans
    (rationalPrimitiveVectorShellEquiv n)

theorem coordinatePrimitiveShell_card {U : Type*} [AddCommGroup U]
    (e : U ≃ₗ[ℤ] IntegerVector) (Q : U → ℚ)
    (he : ∀ x, (vectorNorm (e x) : ℚ) = Q x) (n : ℕ) :
    Nat.card {x : U // Q x = (n : ℚ) ∧ PrimitiveElement x} =
      A354766.r3PrimitiveFinite n :=
  (Nat.card_congr (coordinatePrimitiveShellEquiv e Q he n)).trans
    (primitiveVectorShell_card n)

/-- Moving membership from an ambient shell into a subtype preserves the
exact scalar-divisibility definition of primitivity. -/
def ambientPrimitiveShellEquiv {V : Type*} [AddCommGroup V]
    (L : Submodule ℤ V) (Q : V → ℚ) (level : ℚ) :
    {y : V // y ∈ L ∧ Q y = level ∧ PrimitiveIn L y} ≃
      {x : L // Q (x : V) = level ∧ PrimitiveElement x} where
  toFun y := ⟨⟨y.val, y.property.1⟩, y.property.2.1,
    (primitiveIn_subtype_iff L ⟨y.val, y.property.1⟩).mp y.property.2.2⟩
  invFun x := ⟨x.val.val, x.val.property, x.property.1,
    (primitiveIn_subtype_iff L x.val).mpr x.property.2⟩
  left_inv y := by apply Subtype.ext; rfl
  right_inv x := by apply Subtype.ext; rfl

/-- The actual normalized neighbor shell is equivalent to the finite
three-square model, at every natural norm level. -/
def actual_neighbor_shell_equiv
    (p : ℕ) (hp : p.Prime) (u : IntVec)
    (hu : ∃ i : Fin 3, ¬(p : ℤ) ∣ u i)
    (hQ : (p : ℤ) ^ 2 ∣ dot3 u u) (level : ℕ) :
    {y : RatVec // y ∈ neighbor p u ∧ dot3 y y = (level : ℚ) ∧
      PrimitiveIn (neighbor p u) y} ≃ PrimitiveVectorShell level := by
  let e := Classical.choose (neighbor_integral_coordinates p hp u hu hQ)
  have he := Classical.choose_spec (neighbor_integral_coordinates p hp u hu hQ)
  have heQ (x : neighbor p u) :
      (vectorNorm (e x) : ℚ) = dot3 (x : RatVec) (x : RatVec) := by
    apply (Rat.cast_injective : Function.Injective (fun q : ℚ => (q : ℝ)))
    simpa [e, vectorNorm, Fin.sum_univ_succ, add_assoc] using he x
  exact (ambientPrimitiveShellEquiv (neighbor p u) (fun y => dot3 y y) (level : ℚ)).trans
    (coordinatePrimitiveShellEquiv e (fun x => dot3 (x : RatVec) (x : RatVec)) heQ level)

/-- This is the concrete cardinality needed by the projective-neighbor
double count, with every geometric hypothesis discharged above. -/
theorem actual_neighbor_shell_card
    (p : ℕ) (hp : p.Prime) (u : IntVec)
    (hu : ∃ i : Fin 3, ¬(p : ℤ) ∣ u i)
    (hQ : (p : ℤ) ^ 2 ∣ dot3 u u) (level : ℕ) :
    Nat.card {y : RatVec // y ∈ neighbor p u ∧ dot3 y y = (level : ℚ) ∧
      PrimitiveIn (neighbor p u) y} = A354766.r3PrimitiveFinite level :=
  (Nat.card_congr (actual_neighbor_shell_equiv p hp u hu hQ level)).trans
    (primitiveVectorShell_card level)

theorem actual_neighbor_shell_finite
    (p : ℕ) (hp : p.Prime) (u : IntVec)
    (hu : ∃ i : Fin 3, ¬(p : ℤ) ∣ u i)
    (hQ : (p : ℤ) ^ 2 ∣ dot3 u u) (level : ℕ) :
    Finite {y : RatVec // y ∈ neighbor p u ∧ dot3 y y = (level : ℚ) ∧
      PrimitiveIn (neighbor p u) y} :=
  Finite.of_equiv (PrimitiveVectorShell level)
    (actual_neighbor_shell_equiv p hp u hu hQ level).symm

end A354766Neighbors

#print axioms A354766Neighbors.rationalPrimitiveVectorShellEquiv
#print axioms A354766Neighbors.coordinatePrimitiveShell_card
#print axioms A354766Neighbors.actual_neighbor_shell_equiv
#print axioms A354766Neighbors.actual_neighbor_shell_card
#print axioms A354766Neighbors.actual_neighbor_shell_finite
