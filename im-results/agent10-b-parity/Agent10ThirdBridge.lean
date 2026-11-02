import SamplePart22
import Agent10GrowthSource

namespace BB6.Agent10B

/-- The original source-defined Machine B scalar sample at reset index A2 is odd. -/
theorem source_third_sample_odd :
    (BB6.OneDim.iterG (BB6.OneDim.scalarA 2) 0)%2=1 := by
  rw [A2_exact]
  rw [←iterG_eq_source]
  exact third_sample_odd

#print axioms source_third_sample_odd
end BB6.Agent10B
