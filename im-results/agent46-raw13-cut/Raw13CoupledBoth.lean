import Raw13CoupledLive

namespace BB6.Agent46Raw13CoupledBoth
open BB6Coverage BB6.Agent46Raw13Detour BB6.Agent46Raw13CoupledLive

theorem both_cylinders_never :
    (∀ m, compatible base m → NeverHalts m) ∧
    (∀ m, compatible detour m → NeverHalts m) :=
  both_never base_live

#print axioms both_cylinders_never
end BB6.Agent46Raw13CoupledBoth
