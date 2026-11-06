import BB429Rank
set_option maxHeartbeats 10000000
set_option maxRecDepth 10000000

namespace Agent6RootPrefix

/-- Kernel-checked blank-root checkpoint entering the n=13 zero-row band. -/
theorem blank_reaches_n13_start :
    BB429.run 11728 (0,0)=some (0,49172) := by decide

/-- Kernel-checked blank-root checkpoint entering the n=14 affine-return band. -/
theorem blank_reaches_n14_start :
    BB429.run 23597 (0,0)=some (0,98408) := by decide

#print axioms blank_reaches_n13_start
#print axioms blank_reaches_n14_start

end Agent6RootPrefix
