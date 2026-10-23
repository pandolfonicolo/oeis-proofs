import A354766.ContentDecomposition
import A354766.SignOrbit

/-!
# Normalized divisor decomposition

The raw content decomposition and sign-orbit divisibility combine here to
justify division by four term by term.
-/

namespace A354766

theorem tqFinite_div_four_eq_sum_pqFinite_div_four (n : ℕ) (hn : 0 < n) :
    tqFinite n / 4 = ∑ d ∈ n.divisors, pqFinite d / 4 := by
  rw [tqFinite_eq_sum_pqFinite n hn]
  exact Nat.sum_div fun d _ => four_dvd_pqFinite d

end A354766
