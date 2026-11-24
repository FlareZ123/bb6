import CapTerminalSpacing

namespace CapSieve

theorem signed_root_two : (∃ limit, bandHaltBy limit 0 6=true) ↔
    ∃ limit, signedHaltBy limit 0 6=true := by
  simp only [signed_halt_by_eq (by unfold ValidQ P; decide : ValidQ 0 6)]

theorem signed_root_one : (∃ limit, bandHaltBy limit 0 12=true) ↔
    ∃ limit, signedHaltBy limit 0 12=true := by
  simp only [signed_halt_by_eq (by unfold ValidQ P; decide : ValidQ 0 12)]

theorem signed_root_three : (∃ limit, bandHaltBy limit 0 8=true) ↔
    ∃ limit, signedHaltBy limit 0 8=true := by
  simp only [signed_halt_by_eq (by unfold ValidQ P; decide : ValidQ 0 8)]

#print axioms signed_root_two
#print axioms signed_root_one
#print axioms signed_root_three

end CapSieve
