import A354766.InsideShellPartition
import Mathlib.SetTheory.Cardinal.Finite

namespace A354766Neighbors

variable {V R : Type*} [AddCommGroup V] [CommRing R] [IsDomain R]

abbrev AmbientPrimitiveShell (N : Submodule ℤ V) (Q : V → R) (level : R) :=
  {x : V // x ∈ N ∧ Q x = level ∧ PrimitiveIn N x}

def insideOutsideMap (L N : Submodule ℤ V) (Q : V → R) (level : R) :
    (InsidePrimitiveShell L N Q level ⊕ OutsidePrimitiveShell L N Q level) →
      AmbientPrimitiveShell N Q level
  | Sum.inl x => ⟨x.val, x.property.2.1, x.property.2.2.1, x.property.2.2.2⟩
  | Sum.inr x => ⟨x.val, x.property.1, x.property.2.1, x.property.2.2.1⟩

theorem insideOutsideMap_bijective (L N : Submodule ℤ V) (Q : V → R) (level : R) :
    Function.Bijective (insideOutsideMap L N Q level) := by
  constructor
  · intro x y h
    have hval := congrArg Subtype.val h
    cases x with
    | inl x =>
      cases y with
      | inl y => exact congrArg Sum.inl (Subtype.ext hval)
      | inr y =>
        change x.val = y.val at hval
        have hxL : y.val ∈ L := by rw [← hval]; exact x.property.1
        exact False.elim (y.property.2.2.2 hxL)
    | inr x =>
      cases y with
      | inl y =>
        change x.val = y.val at hval
        have hyL : x.val ∈ L := by rw [hval]; exact y.property.1
        exact False.elim (x.property.2.2.2 hyL)
      | inr y => exact congrArg Sum.inr (Subtype.ext hval)
  · intro x
    by_cases hxL : x.val ∈ L
    · exact ⟨Sum.inl ⟨x.val, hxL, x.property.1, x.property.2.1, x.property.2.2⟩, rfl⟩
    · exact ⟨Sum.inr ⟨x.val, x.property.1, x.property.2.1, x.property.2.2, hxL⟩, rfl⟩

noncomputable def insideOutsideShellEquiv
    (L N : Submodule ℤ V) (Q : V → R) (level : R) :
    (InsidePrimitiveShell L N Q level ⊕ OutsidePrimitiveShell L N Q level) ≃
      AmbientPrimitiveShell N Q level :=
  Equiv.ofBijective (insideOutsideMap L N Q level)
    (insideOutsideMap_bijective L N Q level)

instance finite_insidePrimitiveShell
    (L N : Submodule ℤ V) (Q : V → R) (level : R)
    [Finite (AmbientPrimitiveShell N Q level)] :
    Finite (InsidePrimitiveShell L N Q level) :=
  Finite.of_injective
    (fun x : InsidePrimitiveShell L N Q level =>
      (⟨x.val, x.property.2.1, x.property.2.2.1, x.property.2.2.2⟩ :
        AmbientPrimitiveShell N Q level))
    (fun _ _ h => Subtype.ext
      (congrArg (fun x : AmbientPrimitiveShell N Q level => x.val) h))

instance finite_outsidePrimitiveShell
    (L N : Submodule ℤ V) (Q : V → R) (level : R)
    [Finite (AmbientPrimitiveShell N Q level)] :
    Finite (OutsidePrimitiveShell L N Q level) :=
  Finite.of_injective
    (fun x : OutsidePrimitiveShell L N Q level =>
      (⟨x.val, x.property.1, x.property.2.1, x.property.2.2.1⟩ :
        AmbientPrimitiveShell N Q level))
    (fun _ _ h => Subtype.ext
      (congrArg (fun x : AmbientPrimitiveShell N Q level => x.val) h))

instance finite_insidePrimitiveZeroShell
    (L N : Submodule ℤ V) (p : ℕ) (Q : V → R) (level : R)
    [Finite (AmbientPrimitiveShell L Q level)] :
    Finite (InsidePrimitiveZeroShell L N p Q level) :=
  Finite.of_injective
    (fun x : InsidePrimitiveZeroShell L N p Q level =>
      (⟨x.val, x.property.1, x.property.2.2.1, x.property.2.2.2.1⟩ :
        AmbientPrimitiveShell L Q level))
    (fun _ _ h => Subtype.ext
      (congrArg (fun x : AmbientPrimitiveShell L Q level => x.val) h))

theorem ambientPrimitiveShell_card_partition
    (L N : Submodule ℤ V) (Q : V → R) (level : R)
    [Finite (AmbientPrimitiveShell N Q level)] :
    Nat.card (AmbientPrimitiveShell N Q level) =
      Nat.card (InsidePrimitiveShell L N Q level) +
        Nat.card (OutsidePrimitiveShell L N Q level) := by
  rw [← Nat.card_congr (insideOutsideShellEquiv L N Q level), Nat.card_sum]

theorem insidePrimitiveShell_card_partition
    (L N M : Submodule ℤ V) (p : ℕ) (hp : p.Prime)
    (hML : M ≤ L) (hMN : M ≤ N) (hcommon : L ⊓ N ≤ M)
    (hpL : ∀ z ∈ L, (p : ℤ) • z ∈ M)
    (hpN : ∀ z ∈ N, (p : ℤ) • z ∈ M)
    (hcancel : Function.Injective (fun z : V => (p : ℤ) • z))
    (Q : V → R) (scale level : R) (hscale : scale ≠ 0)
    (hQ : ∀ z, Q ((p : ℤ) • z) = scale * Q z)
    [Finite (AmbientPrimitiveShell L Q (scale * level))]
    [Finite (AmbientPrimitiveShell L Q level)] :
    Nat.card (InsidePrimitiveShell L N Q (scale * level)) =
      Nat.card (InsidePrimitiveZeroShell L N p Q (scale * level)) +
        Nat.card (OutsidePrimitiveShell N L Q level) := by
  rw [← Nat.card_congr (insidePrimitiveShellEquiv
    L N M p hp hML hMN hcommon hpL hpN hcancel Q scale level hscale hQ), Nat.card_sum]

end A354766Neighbors

#print axioms A354766Neighbors.insideOutsideShellEquiv
#print axioms A354766Neighbors.ambientPrimitiveShell_card_partition
#print axioms A354766Neighbors.insidePrimitiveShell_card_partition
