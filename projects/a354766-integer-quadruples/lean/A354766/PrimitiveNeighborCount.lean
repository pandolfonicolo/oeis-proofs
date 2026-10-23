import A354766.NeighborFiberCounts
import A354766.NeighborShellCounts
import A354766.ShellPartitions
import A354766.CharacterScaling
import A354766.ExteriorNeighborCount
import A354766.InsideNeighborSums
import A354766.EulerProductFromRecurrence
import A354766.KernelBase

/-! The actual primitive-neighbor recurrences, with no recurrence hypothesis. -/

open scoped BigOperators

namespace A354766Neighbors

open A354766Research.Neighbor A354766Research.NeighborFamily
open A354766Research.IsotropicLines

instance family_ambient_shell_finite (p : ℕ) [Fact p.Prime] (hp2 : p ≠ 2)
    (P : StandardConic (ZMod p)) (level : ℕ) :
    Finite (AmbientPrimitiveShell (family p hp2 P) rationalNorm (level : ℚ)) :=
  actual_neighbor_shell_finite p Fact.out (normalizedRepresentative p hp2 P)
    ((reduceVec_ne_zero_iff p _).mp (normalizedRepresentative_ne_zero p hp2 P))
    (normalizedRepresentative_norm p hp2 P) level

theorem family_ambient_shell_card (p : ℕ) [Fact p.Prime] (hp2 : p ≠ 2)
    (P : StandardConic (ZMod p)) (level : ℕ) :
    Nat.card (AmbientPrimitiveShell (family p hp2 P) rationalNorm (level : ℚ)) =
      A354766.r3PrimitiveFinite level :=
  actual_neighbor_shell_card p Fact.out (normalizedRepresentative p hp2 P)
    ((reduceVec_ne_zero_iff p _).mp (normalizedRepresentative_ne_zero p hp2 P))
    (normalizedRepresentative_norm p hp2 P) level

/-- Summing actual primitive neighbor shells gives `(p+1)*r3Primitive`.
Finiteness comes from the proved lattice-coordinate equivalences. -/
theorem total_family_shell_card (p : ℕ) [Fact p.Prime] (hp2 : p ≠ 2) (level : ℕ) :
    Nat.card (Σ P : StandardConic (ZMod p),
      AmbientPrimitiveShell (family p hp2 P) rationalNorm (level : ℚ)) =
        (p + 1) * A354766.r3PrimitiveFinite level := by
  classical
  letI : Fintype (StandardConic (ZMod p)) := Fintype.ofFinite _
  rw [Nat.card_sigma]
  simp only [family_ambient_shell_card, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  rw [← Nat.card_eq_fintype_card, card_standardConic_zmod p hp2]
  simp only [Nat.cast_id]

/-- The global inside/outside partition, obtained by summing the actual
per-neighbor bijections; no counting identity is a structural input. -/
theorem total_family_shell_partition (p : ℕ) [Fact p.Prime] (hp2 : p ≠ 2) (level : ℕ) :
    Nat.card (Σ P : StandardConic (ZMod p),
      AmbientPrimitiveShell (family p hp2 P) rationalNorm (level : ℚ)) =
      Nat.card (Σ P : StandardConic (ZMod p),
        InsidePrimitiveShell standard (family p hp2 P) rationalNorm (level : ℚ)) +
      Nat.card (Σ P : StandardConic (ZMod p),
        OutsidePrimitiveShell standard (family p hp2 P) rationalNorm (level : ℚ)) := by
  classical
  letI : Fintype (StandardConic (ZMod p)) := Fintype.ofFinite _
  rw [Nat.card_sigma, Nat.card_sigma, Nat.card_sigma, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro P _
  exact ambientPrimitiveShell_card_partition standard (family p hp2 P) rationalNorm (level : ℚ)

/-- The primitive-vector double-count balance, before evaluating its inside
term. The exterior term is the proved unique-projective-line bijection. -/
theorem family_count_balance (p m : ℕ) [Fact p.Prime] (hp2 : p ≠ 2) :
    ((p : ℤ) + 1) * (A354766.r3PrimitiveFinite (3 * m ^ 2) : ℤ) =
      (Nat.card (Σ P : StandardConic (ZMod p),
        InsidePrimitiveShell standard (family p hp2 P) rationalNorm (3 * (m : ℚ) ^ 2)) : ℤ) +
      (A354766.r3PrimitiveFinite (3 * (p * m) ^ 2) : ℤ) := by
  have hlevel : ((3 * m ^ 2 : ℕ) : ℚ) = 3 * (m : ℚ) ^ 2 := by
    push_cast <;> ring
  have ht : Nat.card (Σ P : StandardConic (ZMod p),
      AmbientPrimitiveShell (family p hp2 P) rationalNorm (3 * (m : ℚ) ^ 2)) =
        (p + 1) * A354766.r3PrimitiveFinite (3 * m ^ 2) := by
    rw [← hlevel]
    exact total_family_shell_card p hp2 (3 * m ^ 2)
  have hpart : Nat.card (Σ P : StandardConic (ZMod p),
      AmbientPrimitiveShell (family p hp2 P) rationalNorm (3 * (m : ℚ) ^ 2)) =
      Nat.card (Σ P : StandardConic (ZMod p),
        InsidePrimitiveShell standard (family p hp2 P) rationalNorm (3 * (m : ℚ) ^ 2)) +
      Nat.card (Σ P : StandardConic (ZMod p),
        OutsidePrimitiveShell standard (family p hp2 P) rationalNorm (3 * (m : ℚ) ^ 2)) := by
    rw [← hlevel]
    exact total_family_shell_partition p hp2 (3 * m ^ 2)
  have hnat : (p + 1) * A354766.r3PrimitiveFinite (3 * m ^ 2) =
      Nat.card (Σ P : StandardConic (ZMod p),
        InsidePrimitiveShell standard (family p hp2 P) rationalNorm (3 * (m : ℚ) ^ 2)) +
      A354766.r3PrimitiveFinite (3 * (p * m) ^ 2) := by
    rw [← ht, hpart, outside_family_card p hp2 m]
  exact_mod_cast hnat

/-- The first prime step, proved by the actual inside/outside double count. -/
theorem primitive_neighbor_first_step (p m : ℕ) [Fact p.Prime] (hp2 : p ≠ 2)
    (hpm : ¬ p ∣ m) :
    (A354766.r3PrimitiveFinite (3 * (p * m) ^ 2) : ℤ) =
      ((p : ℤ) - A354766Research.residueCharacter p) *
        (A354766.r3PrimitiveFinite (3 * m ^ 2) : ℤ) := by
  have hlevel : ((3 * m ^ 2 : ℕ) : ℚ) = 3 * (m : ℚ) ^ 2 := by
    push_cast <;> ring
  have hb := family_count_balance p m hp2
  have hi := inside_family_card_of_not_dvd p m hp2 hpm
  rw [hlevel] at hi
  linear_combination -hb - hi

/-- The repeated prime step, including the ramified prime three. -/
theorem primitive_neighbor_repeated_step (p m : ℕ) [Fact p.Prime] (hp2 : p ≠ 2)
    (hpm : p ∣ m) :
    (A354766.r3PrimitiveFinite (3 * (p * m) ^ 2) : ℤ) =
      ((p : ℤ) + 1) * (A354766.r3PrimitiveFinite (3 * m ^ 2) : ℤ) -
        (if p ∣ m / p then (p : ℤ) else (p : ℤ) - A354766Research.residueCharacter p) *
          (A354766.r3PrimitiveFinite (3 * (m / p) ^ 2) : ℤ) := by
  have hlevel : ((3 * m ^ 2 : ℕ) : ℚ) = 3 * (m : ℚ) ^ 2 := by
    push_cast <;> ring
  have hb := family_count_balance p m hp2
  have hi := inside_family_card_of_dvd p m hp2 hpm
  rw [hlevel] at hi
  have hc : (p : ℤ) - (if p ∣ m / p then 0 else A354766Research.residueCharacter p) =
      (if p ∣ m / p then (p : ℤ) else (p : ℤ) - A354766Research.residueCharacter p) := by
    by_cases h : p ∣ m / p <;> simp only [h, if_true, if_false, sub_zero]
  rw [hc] at hi
  linear_combination -hb - hi

def primitiveOddCount (m : ℕ) : ℤ := (A354766.r3PrimitiveFinite (3 * m ^ 2) : ℤ)

/-- Every recurrence input to the independently proved Euler-product theorem
is instantiated by the actual three-square count. -/
theorem actual_odd_prime_recurrences :
    A354766Research.OddPrimeRecurrences primitiveOddCount A354766Research.residueCharacter where
  at_one := by
    simp only [primitiveOddCount, one_pow, mul_one]
    exact_mod_cast A354766Research.primitive_three_base_kernel
  first_step := by
    intro p m hp hpo _ _ hpm
    letI : Fact p.Prime := ⟨hp⟩
    have hp2 : p ≠ 2 := by
      intro h
      subst p
      rcases hpo with ⟨k, hk⟩
      omega
    exact primitive_neighbor_first_step p m hp2 hpm
  repeated_step := by
    intro p m hp hpo _ _ hpm
    letI : Fact p.Prime := ⟨hp⟩
    have hp2 : p ≠ 2 := by
      intro h
      subst p
      rcases hpo with ⟨k, hk⟩
      omega
    exact primitive_neighbor_repeated_step p m hp2 hpm

/-- The primitive three-squares Euler product, with the recurrences supplied
by the proved projective-neighbor double count. -/
theorem primitive_three_squares_euler_product (m : ℕ) (hm : 0 < m) (hmo : Odd m) :
    (A354766.r3PrimitiveFinite (3 * m ^ 2) : ℚ) =
      8 * (m : ℚ) * ∏ p ∈ m.primeFactors,
        (1 - (A354766Research.residueCharacter p : ℚ) / (p : ℚ)) := by
  have h := A354766Research.euler_product_rat actual_odd_prime_recurrences hm hmo
  simpa only [primitiveOddCount, Int.cast_natCast] using h

end A354766Neighbors

#print axioms A354766Neighbors.total_family_shell_card
#print axioms A354766Neighbors.total_family_shell_partition
#print axioms A354766Neighbors.family_count_balance
#print axioms A354766Neighbors.primitive_neighbor_first_step
#print axioms A354766Neighbors.primitive_neighbor_repeated_step
#print axioms A354766Neighbors.actual_odd_prime_recurrences
#print axioms A354766Neighbors.primitive_three_squares_euler_product
