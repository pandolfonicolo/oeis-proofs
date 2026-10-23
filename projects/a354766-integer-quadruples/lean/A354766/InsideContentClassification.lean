import A354766.PrimitiveNeighborAlgebra
import Mathlib.Tactic.Push

/-!
Every primitive neighbor vector that lies in the standard lattice has
standard content either one or exactly p. The proof extracts an actual
prime divisor and excludes a second p division; it does not assume a
content decomposition or a counting recurrence.
-/

namespace A354766Neighbors

variable {V : Type*} [AddCommGroup V]

theorem inside_primitive_cases
    (L N M : Submodule ℤ V) (p : ℕ) (hp : p.Prime)
    (hML : M ≤ L) (hMN : M ≤ N) (hcommon : L ⊓ N ≤ M)
    (hpL : ∀ z ∈ L, (p : ℤ) • z ∈ M)
    (hpN : ∀ z ∈ N, (p : ℤ) • z ∈ M)
    (x : V) (hxL : x ∈ L) (hxN : x ∈ N) (hx : PrimitiveIn N x) :
    PrimitiveIn L x ∨
      ∃ z ∈ L, PrimitiveIn L z ∧ x = (p : ℤ) • z ∧ z ∉ N := by
  classical
  by_cases hxprim : PrimitiveIn L x
  · exact Or.inl hxprim
  · right
    have hxM : x ∈ M := hcommon ⟨hxL, hxN⟩
    have hawayN : PrimitiveAway N p x :=
      ((primitiveIn_iff_away_and_at N p hp x).mp hx).1
    have hawayL : PrimitiveAway L p x :=
      (primitiveAway_iff_of_prime_multiple_inclusions
        L N M p hp hML hMN hpL hpN x hxM).mpr hawayN
    change ¬ (∀ q : ℕ, q.Prime → ¬ DivisibleIn L q x) at hxprim
    push_neg at hxprim
    obtain ⟨q, hq, hqdiv⟩ := hxprim
    have hqp : q = p := by
      by_contra hqp
      exact hawayL q hq hqp hqdiv
    subst q
    obtain ⟨z, hzL, hpz⟩ := hqdiv
    have hawayZ : PrimitiveAway L p z :=
      (primitiveAway_prime_smul_iff L p hp z hzL).mp (by simpa only [hpz] using hawayL)
    have hatZ : ¬ DivisibleIn L p z := by
      rintro ⟨w, hwL, hpw⟩
      apply hx p hp
      refine ⟨(p : ℤ) • w, hMN (hpL w hwL), ?_⟩
      calc
        (p : ℤ) • ((p : ℤ) • w) = (p : ℤ) • z := congrArg ((p : ℤ) • ·) hpw
        _ = x := hpz
    have hzprim : PrimitiveIn L z :=
      (primitiveIn_iff_away_and_at L p hp z).mpr ⟨hawayZ, hatZ⟩
    have hzN : z ∉ N := fun h => hx p hp ⟨z, h, hpz⟩
    exact ⟨z, hzL, hzprim, hpz.symm, hzN⟩

theorem inside_primitive_iff_content_cases
    (L N M : Submodule ℤ V) (p : ℕ) (hp : p.Prime)
    (hML : M ≤ L) (hMN : M ≤ N) (hcommon : L ⊓ N ≤ M)
    (hpL : ∀ z ∈ L, (p : ℤ) • z ∈ M)
    (hpN : ∀ z ∈ N, (p : ℤ) • z ∈ M)
    (hcancel : Function.Injective (fun z : V => (p : ℤ) • z))
    (x : V) (hxL : x ∈ L) (hxN : x ∈ N) :
    PrimitiveIn N x ↔
      (PrimitiveIn L x ∧ ¬ DivisibleIn N p x) ∨
        ∃ z ∈ L, PrimitiveIn L z ∧ x = (p : ℤ) • z ∧ z ∉ N := by
  constructor
  · intro hx
    rcases inside_primitive_cases L N M p hp hML hMN hcommon hpL hpN x hxL hxN hx with h | h
    · exact Or.inl ⟨h, hx p hp⟩
    · exact Or.inr h
  · rintro (⟨hx, hdiv⟩ | ⟨z, hzL, hz, rfl, hzN⟩)
    · exact (inside_primitive_iff_not_divisible L N M p hp hML hMN hpL hpN
        x (hcommon ⟨hxL, hxN⟩) hx).mpr hdiv
    · exact (inside_one_primitive_iff_not_mem L N M p hp hML hMN hpL hpN
        hcancel z hzL hz).mpr hzN

end A354766Neighbors

#print axioms A354766Neighbors.inside_primitive_cases
#print axioms A354766Neighbors.inside_primitive_iff_content_cases
