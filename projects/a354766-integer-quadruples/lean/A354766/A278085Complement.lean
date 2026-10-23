import A354766.FiniteCounts
import A354766.PrimitiveNeighborAlgebra

/-!
The primary A278085 equations have sum 3n and norm 3n². The complement
q ↦ (n-h,n-i,n-j,n-k) is an explicit involution identifying them with
the sum-n, norm-n² model used throughout the arithmetic proof.
-/

namespace A354766

def IsA278085Quad (n : ℤ) (q : QuadCoords) : Prop :=
  q.h + q.i + q.j + q.k = 3 * n ∧
    q.h ^ 2 + q.i ^ 2 + q.j ^ 2 + q.k ^ 2 = 3 * n ^ 2

def complementQuad (n : ℤ) (q : QuadCoords) : QuadCoords :=
  ⟨n - q.h, n - q.i, n - q.j, n - q.k⟩

theorem complementQuad_sum (n : ℤ) (q : QuadCoords) :
    (complementQuad n q).h + (complementQuad n q).i +
      (complementQuad n q).j + (complementQuad n q).k =
      4 * n - (q.h + q.i + q.j + q.k) := by
  simp only [complementQuad]
  ring

theorem complementQuad_norm (n : ℤ) (q : QuadCoords) :
    (complementQuad n q).h ^ 2 + (complementQuad n q).i ^ 2 +
      (complementQuad n q).j ^ 2 + (complementQuad n q).k ^ 2 =
      (q.h ^ 2 + q.i ^ 2 + q.j ^ 2 + q.k ^ 2) -
        2 * n * (q.h + q.i + q.j + q.k) + 4 * n ^ 2 := by
  simp only [complementQuad]
  ring

theorem complementQuad_involutive (n : ℤ) : Function.Involutive (complementQuad n) := by
  intro q
  cases q
  dsimp [complementQuad]
  congr 1 <;> ring

theorem complementQuad_primary {n : ℤ} {q : QuadCoords} (hq : IsQuad n q) :
    IsA278085Quad n (complementQuad n q) := by
  constructor
  · rw [complementQuad_sum, hq.1]
    ring
  · rw [complementQuad_norm, hq.1, hq.2]
    ring

theorem complementQuad_standard {n : ℤ} {q : QuadCoords} (hq : IsA278085Quad n q) :
    IsQuad n (complementQuad n q) := by
  constructor
  · rw [complementQuad_sum, hq.1]
    ring
  · rw [complementQuad_norm, hq.1, hq.2]
    ring

def a278085QuadEquiv (n : ℤ) :
    {q : QuadCoords // IsQuad n q} ≃ {q : QuadCoords // IsA278085Quad n q} where
  toFun q := ⟨complementQuad n q.val, complementQuad_primary q.property⟩
  invFun q := ⟨complementQuad n q.val, complementQuad_standard q.property⟩
  left_inv q := Subtype.ext (complementQuad_involutive n q.val)
  right_inv q := Subtype.ext (complementQuad_involutive n q.val)

def finiteA278085QuadEquiv (n : ℕ) :
    {q : QuadCoords // q ∈ quadFinset n} ≃
      {q : QuadCoords // IsA278085Quad (n : ℤ) q} :=
  (Equiv.subtypeEquivRight (fun _ => mem_quadFinset)).trans (a278085QuadEquiv (n : ℤ))

instance finite_A278085_quads (n : ℕ) :
    Finite {q : QuadCoords // IsA278085Quad (n : ℤ) q} :=
  Finite.of_equiv {q : QuadCoords // q ∈ quadFinset n} (finiteA278085QuadEquiv n)

theorem a278085_quad_count (n : ℕ) :
    Nat.card {q : QuadCoords // IsA278085Quad (n : ℤ) q} = tqFinite n := by
  have h := Nat.card_congr (finiteA278085QuadEquiv n)
  simpa only [Nat.card_eq_fintype_card, Fintype.card_coe, tqFinite] using h.symm

noncomputable def A278085ComplementTotal (n : ℕ) : ℕ :=
  Nat.card {q : QuadCoords // IsA278085Quad (n : ℤ) q} / 4

theorem A278085ComplementTotal_eq_normalized_count (n : ℕ) :
    A278085ComplementTotal n = tqFinite n / 4 := by
  rw [A278085ComplementTotal, a278085_quad_count]

/-- A common prime divisor of all four coordinates. -/
def PrimeDividesQuad (p : ℕ) (q : QuadCoords) : Prop :=
  (p : ℤ) ∣ q.h ∧ (p : ℤ) ∣ q.i ∧ (p : ℤ) ∣ q.j ∧ (p : ℤ) ∣ q.k

theorem quadContent_eq_one_iff_no_prime (q : QuadCoords) :
    quadContent q = 1 ↔ ∀ p : ℕ, p.Prime → ¬ PrimeDividesQuad p q := by
  rw [Nat.eq_one_iff_not_exists_prime_dvd]
  simp only [quadContent, PrimeDividesQuad, Nat.dvd_gcd_iff, Int.natCast_dvd]

theorem primeDividesQuad_norm (p : ℕ) (q : QuadCoords) (hq : PrimeDividesQuad p q) :
    (p : ℤ) ^ 2 ∣ q.h ^ 2 + q.i ^ 2 + q.j ^ 2 + q.k ^ 2 := by
  rcases hq with ⟨⟨a, ha⟩, ⟨b, hb⟩, ⟨c, hc⟩, ⟨d, hd⟩⟩
  rw [ha, hb, hc, hd]
  refine ⟨a ^ 2 + b ^ 2 + c ^ 2 + d ^ 2, ?_⟩
  ring

theorem primary_prime_divisor_dvd_level (p n : ℕ) (hp : p.Prime) (q : QuadCoords)
    (hprimary : IsA278085Quad (n : ℤ) q) (hq : PrimeDividesQuad p q) : p ∣ n := by
  have hInt : (p : ℤ) ^ 2 ∣ 3 * (n : ℤ) ^ 2 := by
    rw [← hprimary.2]
    exact primeDividesQuad_norm p q hq
  have hNat : p ^ 2 ∣ 3 * n ^ 2 := by exact_mod_cast hInt
  exact (A354766Neighbors.prime_sq_dvd_three_mul_sq_iff p n hp).mp hNat

theorem standard_quad_divisor_dvd_level (p n : ℕ) (q : QuadCoords)
    (hstandard : IsQuad (n : ℤ) q) (hq : PrimeDividesQuad p q) : p ∣ n := by
  have hsum : (p : ℤ) ∣ q.h + q.i + q.j + q.k :=
    dvd_add (dvd_add (dvd_add hq.1 hq.2.1) hq.2.2.1) hq.2.2.2
  rw [hstandard.1] at hsum
  exact Int.natCast_dvd_natCast.mp hsum

theorem complement_prime_divisibility_iff (n : ℕ) (q : QuadCoords)
    (hstandard : IsQuad (n : ℤ) q) (p : ℕ) (hp : p.Prime) :
    PrimeDividesQuad p (complementQuad (n : ℤ) q) ↔ PrimeDividesQuad p q := by
  constructor
  · intro hc
    have hpn : (p : ℤ) ∣ (n : ℤ) := Int.natCast_dvd_natCast.mpr
      (primary_prime_divisor_dvd_level p n hp (complementQuad (n : ℤ) q)
        (complementQuad_primary hstandard) hc)
    exact ⟨by simpa [complementQuad] using dvd_sub hpn hc.1,
      by simpa [complementQuad] using dvd_sub hpn hc.2.1,
      by simpa [complementQuad] using dvd_sub hpn hc.2.2.1,
      by simpa [complementQuad] using dvd_sub hpn hc.2.2.2⟩
  · intro hq
    have hpn : (p : ℤ) ∣ (n : ℤ) := Int.natCast_dvd_natCast.mpr
      (standard_quad_divisor_dvd_level p n q hstandard hq)
    exact ⟨dvd_sub hpn hq.1, dvd_sub hpn hq.2.1,
      dvd_sub hpn hq.2.2.1, dvd_sub hpn hq.2.2.2⟩

theorem complement_primitive_iff (n : ℕ) (q : QuadCoords)
    (hstandard : IsQuad (n : ℤ) q) :
    quadContent (complementQuad (n : ℤ) q) = 1 ↔ quadContent q = 1 := by
  rw [quadContent_eq_one_iff_no_prime, quadContent_eq_one_iff_no_prime]
  constructor
  · intro h p hp hq
    exact h p hp ((complement_prime_divisibility_iff n q hstandard p hp).mpr hq)
  · intro h p hp hc
    exact h p hp ((complement_prime_divisibility_iff n q hstandard p hp).mp hc)

theorem complement_primary_primitive_iff (n : ℕ) (q : QuadCoords)
    (hprimary : IsA278085Quad (n : ℤ) q) :
    quadContent (complementQuad (n : ℤ) q) = 1 ↔ quadContent q = 1 := by
  have h := complement_primitive_iff n (complementQuad (n : ℤ) q)
    (complementQuad_standard hprimary)
  simpa only [complementQuad_involutive (n : ℤ) q] using h.symm

def a278085PrimitiveQuadEquiv (n : ℕ) :
    {q : QuadCoords // IsQuad (n : ℤ) q ∧ quadContent q = 1} ≃
      {q : QuadCoords // IsA278085Quad (n : ℤ) q ∧ quadContent q = 1} where
  toFun q := ⟨complementQuad (n : ℤ) q.val, complementQuad_primary q.property.1,
    (complement_primitive_iff n q.val q.property.1).mpr q.property.2⟩
  invFun q := ⟨complementQuad (n : ℤ) q.val, complementQuad_standard q.property.1,
    (complement_primary_primitive_iff n q.val q.property.1).mpr q.property.2⟩
  left_inv q := Subtype.ext (complementQuad_involutive (n : ℤ) q.val)
  right_inv q := Subtype.ext (complementQuad_involutive (n : ℤ) q.val)

def finiteA278085PrimitiveQuadEquiv (n : ℕ) :
    {q : QuadCoords // q ∈ primitiveQuadFinset n} ≃
      {q : QuadCoords // IsA278085Quad (n : ℤ) q ∧ quadContent q = 1} :=
  (Equiv.subtypeEquivRight (fun _ => mem_primitiveQuadFinset)).trans
    (a278085PrimitiveQuadEquiv n)

instance finite_A278085_primitive_quads (n : ℕ) :
    Finite {q : QuadCoords // IsA278085Quad (n : ℤ) q ∧ quadContent q = 1} :=
  Finite.of_equiv {q : QuadCoords // q ∈ primitiveQuadFinset n}
    (finiteA278085PrimitiveQuadEquiv n)

theorem a278085_primitive_quad_count (n : ℕ) :
    Nat.card {q : QuadCoords // IsA278085Quad (n : ℤ) q ∧ quadContent q = 1} = pqFinite n := by
  have h := Nat.card_congr (finiteA278085PrimitiveQuadEquiv n)
  simpa only [Nat.card_eq_fintype_card, Fintype.card_coe, pqFinite] using h.symm

/-- The genuine OEIS primary definition counts primitive complementary quads. -/
noncomputable def A278085Primary (n : ℕ) : ℕ :=
  Nat.card {q : QuadCoords // IsA278085Quad (n : ℤ) q ∧ quadContent q = 1} / 4

theorem A278085Primary_eq_normalized_count (n : ℕ) :
    A278085Primary n = pqFinite n / 4 := by
  rw [A278085Primary, a278085_primitive_quad_count]

end A354766

#print axioms A354766.a278085_quad_count
#print axioms A354766.A278085ComplementTotal_eq_normalized_count
#print axioms A354766.complement_primitive_iff
#print axioms A354766.a278085_primitive_quad_count
#print axioms A354766.A278085Primary_eq_normalized_count
