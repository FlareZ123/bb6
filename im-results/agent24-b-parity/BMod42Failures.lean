import BParityAperiodic
set_option maxRecDepth 4096
namespace BB6.Agent24

/-- A generic index in a purported survival-compatible mod-42 class
    can nevertheless have an even (halting-style) sampled parity bit. -/
theorem generic_residue_31_even : (iterG 31 0)%2=0 := by decide
theorem generic_residue_45_even : (iterG 45 0)%2=0 := by decide

#print axioms generic_residue_31_even
#print axioms generic_residue_45_even

end BB6.Agent24
