import Q0MacroCheck
namespace BB429Q0Macro
set_option maxHeartbeats 0
set_option maxRecDepth 10000000
set_option Elab.async false

theorem cover_1000000 : cover 43 0 0 1000000 = true := by decide +kernel

theorem no_q0_path_below_million (u : Nat) (hu : u<1000000) :
    ¬ Path (8*u+5) (24*u+22) (6*u+4) :=
  cover_sound 43 0 0 1000000 u (by decide) (by simpa only [Nat.pow_zero] using Nat.mod_one u) hu cover_1000000

#print axioms cover_1000000
#print axioms no_q0_path_below_million
end BB429Q0Macro
