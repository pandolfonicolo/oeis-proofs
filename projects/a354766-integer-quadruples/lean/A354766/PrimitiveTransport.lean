import Mathlib.Data.Int.GCD
import Mathlib.Algebra.Module.Submodule.Basic
import Mathlib.Data.Nat.Prime.Basic

/-!
Primitivity transport between submodules whose intersection contains their
prime multiples. These are algebraic components of the neighbor construction;
no representation-count recurrence or lattice classification is assumed.
-/

namespace A354766Neighbors

variable {V : Type*} [AddCommGroup V]

/-- Bézout descent into an integer submodule. -/
theorem mem_of_coprime_smul_mem (M : Submodule ℤ V) (x : V)
    (p q : ℕ) (hpq : p.Coprime q)
    (hp : (p : ℤ) • x ∈ M) (hq : (q : ℤ) • x ∈ M) : x ∈ M := by
  have hbez : (1 : ℤ) = (p : ℤ) * Nat.gcdA p q + (q : ℤ) * Nat.gcdB p q := by
    simpa only [hpq.gcd_eq_one, Nat.cast_one] using Nat.gcd_eq_gcd_ab p q
  have hsum : ((p : ℤ) * Nat.gcdA p q + (q : ℤ) * Nat.gcdB p q) • x ∈ M := by
    rw [add_smul, mul_smul, mul_smul,
      smul_comm (p : ℤ) (Nat.gcdA p q) x,
      smul_comm (q : ℤ) (Nat.gcdB p q) x]
    exact M.add_mem (M.smul_mem _ hp) (M.smul_mem _ hq)
  rwa [← hbez, one_smul] at hsum

/-- Divisibility inside the indicated lattice/submodule. -/
def DivisibleIn (L : Submodule ℤ V) (q : ℕ) (x : V) : Prop :=
  ∃ y ∈ L, (q : ℤ) • y = x

/-- Multiplication by a coprime integer preserves divisibility in a lattice. -/
theorem divisibleIn_smul_iff (L : Submodule ℤ V) (y : V) (hy : y ∈ L)
    (p q : ℕ) (hpq : p.Coprime q) :
    DivisibleIn L q ((p : ℤ) • y) ↔ DivisibleIn L q y := by
  have hbez : (Nat.gcdA p q) * (p : ℤ) + (Nat.gcdB p q) * (q : ℤ) = 1 := by
    simpa only [hpq.gcd_eq_one, Nat.cast_one, mul_comm] using
      (Nat.gcd_eq_gcd_ab p q).symm
  constructor
  · rintro ⟨z, hz, hqz⟩
    refine ⟨Nat.gcdA p q • z + Nat.gcdB p q • y,
      L.add_mem (L.smul_mem _ hz) (L.smul_mem _ hy), ?_⟩
    calc
      (q : ℤ) • (Nat.gcdA p q • z + Nat.gcdB p q • y) =
          Nat.gcdA p q • ((q : ℤ) • z) + Nat.gcdB p q • ((q : ℤ) • y) := by
        rw [smul_add, smul_comm (q : ℤ) (Nat.gcdA p q) z,
          smul_comm (q : ℤ) (Nat.gcdB p q) y]
      _ = Nat.gcdA p q • ((p : ℤ) • y) + Nat.gcdB p q • ((q : ℤ) • y) := by
        rw [hqz]
      _ = (Nat.gcdA p q * (p : ℤ) + Nat.gcdB p q * (q : ℤ)) • y := by
        rw [add_smul, mul_smul, mul_smul]
      _ = y := by rw [hbez, one_smul]
  · rintro ⟨z, hz, hqz⟩
    refine ⟨(p : ℤ) • z, L.smul_mem _ hz, ?_⟩
    rw [smul_comm (q : ℤ) (p : ℤ) z, hqz]

/-- At a prime away from `p`, an element of the common submodule has the
same divisibility in both lattices. The hypotheses are the explicit
inclusions that the neighbor construction must prove. -/
theorem divisibleIn_iff_of_prime_multiple_inclusions
    (L N M : Submodule ℤ V) (p q : ℕ) (hpq : p.Coprime q)
    (hML : M ≤ L) (hMN : M ≤ N)
    (hpL : ∀ y ∈ L, (p : ℤ) • y ∈ M)
    (hpN : ∀ y ∈ N, (p : ℤ) • y ∈ M)
    (x : V) (hx : x ∈ M) :
    DivisibleIn L q x ↔ DivisibleIn N q x := by
  constructor
  · rintro ⟨y, hy, hqy⟩
    have hqyM : (q : ℤ) • y ∈ M := by rwa [hqy]
    have hyM := mem_of_coprime_smul_mem M y p q hpq (hpL y hy) hqyM
    exact ⟨y, hMN hyM, hqy⟩
  · rintro ⟨y, hy, hqy⟩
    have hqyM : (q : ℤ) • y ∈ M := by rwa [hqy]
    have hyM := mem_of_coprime_smul_mem M y p q hpq (hpN y hy) hqyM
    exact ⟨y, hML hyM, hqy⟩

def PrimitiveAway (L : Submodule ℤ V) (p : ℕ) (x : V) : Prop :=
  ∀ q : ℕ, q.Prime → q ≠ p → ¬ DivisibleIn L q x

theorem primitiveAway_iff_of_prime_multiple_inclusions
    (L N M : Submodule ℤ V) (p : ℕ) (hp : p.Prime)
    (hML : M ≤ L) (hMN : M ≤ N)
    (hpL : ∀ y ∈ L, (p : ℤ) • y ∈ M)
    (hpN : ∀ y ∈ N, (p : ℤ) • y ∈ M)
    (x : V) (hx : x ∈ M) :
    PrimitiveAway L p x ↔ PrimitiveAway N p x := by
  have hcop (q : ℕ) (hq : q.Prime) (hne : q ≠ p) : p.Coprime q := by
    apply hp.coprime_iff_not_dvd.mpr
    intro hd
    exact hne ((Nat.prime_dvd_prime_iff_eq hp hq).mp hd).symm
  constructor
  · intro h q hq hne hdiv
    apply h q hq hne
    exact (divisibleIn_iff_of_prime_multiple_inclusions
      L N M p q (hcop q hq hne) hML hMN hpL hpN x hx).mpr hdiv
  · intro h q hq hne hdiv
    apply h q hq hne
    exact (divisibleIn_iff_of_prime_multiple_inclusions
      L N M p q (hcop q hq hne) hML hMN hpL hpN x hx).mp hdiv

/-- Away from `p`, multiplication carries neighbor vectors to standard
lattice vectors without changing primitivity. -/
theorem primitiveAway_scaled_iff
    (L N M : Submodule ℤ V) (p : ℕ) (hp : p.Prime)
    (hML : M ≤ L) (hMN : M ≤ N)
    (hpL : ∀ y ∈ L, (p : ℤ) • y ∈ M)
    (hpN : ∀ y ∈ N, (p : ℤ) • y ∈ M)
    (y : V) (hy : y ∈ N) :
    PrimitiveAway L p ((p : ℤ) • y) ↔ PrimitiveAway N p y := by
  have hdiv (q : ℕ) (hq : q.Prime) (hne : q ≠ p) :
      DivisibleIn L q ((p : ℤ) • y) ↔ DivisibleIn N q y := by
    have hpq : p.Coprime q := by
      apply hp.coprime_iff_not_dvd.mpr
      intro hd
      exact hne ((Nat.prime_dvd_prime_iff_eq hp hq).mp hd).symm
    exact (divisibleIn_iff_of_prime_multiple_inclusions
      L N M p q hpq hML hMN hpL hpN ((p : ℤ) • y) (hpN y hy)).trans
      (divisibleIn_smul_iff N y hy p q hpq)
  constructor
  · intro h q hq hne hd
    exact h q hq hne ((hdiv q hq hne).mpr hd)
  · intro h q hq hne hd
    exact h q hq hne ((hdiv q hq hne).mp hd)

/-- A vector outside the standard lattice cannot have a `p`-th part in
the neighbor when all neighbor `p`-multiples lie in the standard lattice. -/
theorem not_divisibleIn_of_outside
    (L N : Submodule ℤ V) (p : ℕ)
    (hpN : ∀ z ∈ N, (p : ℤ) • z ∈ L)
    (y : V) (hy : y ∉ L) : ¬ DivisibleIn N p y := by
  rintro ⟨z, hz, hqz⟩
  apply hy
  rw [← hqz]
  exact hpN z hz

/-- The inside vectors with at least two powers of `p` in their content
cannot be primitive in any neighbor containing the standard `p`-multiples. -/
theorem divisibleIn_pow_of_two_le
    (L N : Submodule ℤ V) (p a : ℕ) (ha : 2 ≤ a)
    (hpL : ∀ z ∈ L, (p : ℤ) • z ∈ N)
    (z : V) (hz : z ∈ L) : DivisibleIn N p (((p : ℤ) ^ a) • z) := by
  refine ⟨(p : ℤ) • (((p : ℤ) ^ (a - 2)) • z),
    hpL _ (L.smul_mem _ hz), ?_⟩
  calc
    (p : ℤ) • ((p : ℤ) • (((p : ℤ) ^ (a - 2)) • z)) =
        (((p : ℤ) * p) * (p : ℤ) ^ (a - 2)) • z := by
      simp only [smul_smul, mul_assoc]
    _ = ((p : ℤ) ^ (a - 2) * ((p : ℤ) * p)) • z := by rw [mul_comm]
    _ = ((p : ℤ) ^ ((a - 2) + 2)) • z := by rw [pow_add, pow_two]
    _ = ((p : ℤ) ^ a) • z := by rw [Nat.sub_add_cancel ha]

/-- In a torsion-free ambient module, a standard vector of content exactly
`p` fails primitivity in a neighbor exactly when its quotient lies there. -/
theorem divisibleIn_smul_iff_mem
    (N : Submodule ℤ V) (p : ℕ)
    (hcancel : Function.Injective (fun x : V => (p : ℤ) • x)) (z : V) :
    DivisibleIn N p ((p : ℤ) • z) ↔ z ∈ N := by
  constructor
  · rintro ⟨w, hw, h⟩
    have hwz : w = z := hcancel h
    simpa only [hwz] using hw
  · intro hz
    exact ⟨z, hz, rfl⟩

end A354766Neighbors

#print axioms A354766Neighbors.mem_of_coprime_smul_mem
#print axioms A354766Neighbors.primitiveAway_iff_of_prime_multiple_inclusions
#print axioms A354766Neighbors.divisibleIn_smul_iff
#print axioms A354766Neighbors.primitiveAway_scaled_iff
#print axioms A354766Neighbors.not_divisibleIn_of_outside
#print axioms A354766Neighbors.divisibleIn_pow_of_two_le
#print axioms A354766Neighbors.divisibleIn_smul_iff_mem
