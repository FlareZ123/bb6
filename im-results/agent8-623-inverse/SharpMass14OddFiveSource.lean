import Agent8SharpMass14OddAuxSource
import Agent8RootedMassSource
namespace BB6.Agent8SharpSource
open BusyBeaver.M_1RB0LE_0RC1RC_0RD1LA_1LD0LA_1LF1LC_HHH0LA

theorem drain_five_exact (a : Nat) (ha : 3≤a) :
    drainB a 5 3 = some (.D (a-3) 26) := by
  rw [drainB]
  simp only [if_neg (by decide : (5:Nat)≠0)]
  have hm : 3+2*5+3=16 := by omega
  rw [hm,eval_four_exact a 16 ha]
  simp only [Option.bind_some,if_pos (by decide : (0:Nat)<5)]
  rw [drainB]
  simp only [if_true]
end BB6.Agent8SharpSource
