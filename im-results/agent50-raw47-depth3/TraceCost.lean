import CheckedSweepTrace
namespace BB6.Agent50TraceCost
open BB6Coverage BB6Coverage.Agent31Pump BB6.Agent50CheckedSweepTrace

theorem trace_at (p : PartialMachine) (cs : List (Cmd p)) (n : Nat) (z z' : Z0)
    (hn : cost cs = n) (h : trace cs z = some z') : run0 p n z = some z' := by
  rw [← hn]
  exact trace_sound cs z z' h

theorem join_at (p : PartialMachine) (n k t : Nat) (a b c : Z0)
    (ht : n+k=t) (h : run0 p n a = some b) (g : run0 p k b = some c) : run0 p t a = some c := by
  rw [← ht]
  exact join0 h g
#print axioms trace_at
#print axioms join_at
end BB6.Agent50TraceCost
