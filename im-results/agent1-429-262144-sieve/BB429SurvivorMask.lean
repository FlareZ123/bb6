import BB429SurvivorCount3

namespace BB429SurvivorMask

/-- Exactly 255 finer-modulus candidates survive intersection of the
    previous 58/16384 necessary gate with the 673 new, universally
    excluded terminal cylinders. Each block count was checked by Lean's
    kernel (not a VM native_decide shortcut). -/
theorem live255_count : live255.length = 255 := by
  simp only [live255, List.length_append, block_count0, block_count1, block_count2, block_count3, block_count4, block_count5, block_count6, block_count7, block_count8, block_count9, block_count10, block_count11, block_count12, block_count13, block_count14, block_count15]

#print axioms live255_count
#print axioms live255_iff
end BB429SurvivorMask
