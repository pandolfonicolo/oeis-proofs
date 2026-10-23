import A354766.FiniteCounts

/-! A kernel-reduced base count, independent of the recovered native_decide proof. -/

namespace A354766Research

set_option maxRecDepth 8000 in
set_option maxHeartbeats 2000000 in
theorem primitive_three_base_kernel : A354766.r3PrimitiveFinite 3 = 8 := by
  decide

end A354766Research

#print axioms A354766Research.primitive_three_base_kernel
