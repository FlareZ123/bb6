import AllQFirstHalt
import Lean.Elab.Tactic.Omega

set_option maxHeartbeats 50000000
set_option maxRecDepth 8192

namespace BB6.Agent2AllQE1101101100
open CryptidBoundary

/- A second source-connected terminal cylinder, not the previous
   1101101100 trigger: this one is lifted from the certified terminal
   1011011 + 000 entry of TailWindowPrefix's 64-word table. -/
def terminal000 : List Bool :=
  [true,false,true,true,false,true,true,false,false,false]

def pre000 : List Bool :=
  [true,true,false] ++ terminal000

/- Finite source replay is uniform over any left/right exterior:
   the first 114 steps read at most five left cells and ten right cells. -/
theorem terminal000_frozen (L ys : List Bool) :
    (run 114 (⟨[false,false,true,false,true] ++ L,false,
      terminal000 ++ ys,4⟩ : Cfg)).st = 6 := by
  simp [terminal000,run,step,goL,goR]

theorem trigger3_000 (L ys : List Bool) :
    run 3 (⟨L,false,pre000 ++ ys,0⟩ : Cfg) =
      ⟨[false,false,true] ++ L,false,terminal000 ++ ys,4⟩ := by
  simp [pre000,terminal000,run,step,goL,goR]

theorem pairL_front (q : Nat) :
    pairL (q+1) = [false,true] ++ pairL q := by
  induction q with
  | zero => rfl
  | succ q ih =>
      simp only [pairL]
      rw [ih]
      simp only [List.append_assoc]
      rfl

/- Arbitrarily many leading 10 pairs preserve a different halting
   suffix: (10)^q 110 1011011 000 Y. -/
theorem all_q_prefix000_frozen (q : Nat) (L ys : List Bool) :
    (run (121+2*q)
      (⟨[false,false,true] ++ L,false,
        pairR q ++ pre000 ++ ys,4⟩ : Cfg)).st = 6 := by
  have ht : 121+2*q = 4+(2*q+(3+114)) := by omega
  rw [ht,run_add,prelude4,run_add]
  simp only [List.append_assoc]
  rw [scan_all,run_add,trigger3_000]
  cases q with
  | zero =>
      change (run 114
        (⟨[false,false,true,false,true] ++ ([true] ++ L),false,
          terminal000 ++ ys,4⟩ : Cfg)).st = 6
      exact terminal000_frozen _ _
  | succ q =>
      rw [pairL_front]
      change (run 114
        (⟨[false,false,true,false,true] ++
          (pairL q ++ [false,true,true] ++ L),false,
          terminal000 ++ ys,4⟩ : Cfg)).st = 6
      exact terminal000_frozen _ _

#print axioms terminal000_frozen
#print axioms pairL_front
#print axioms all_q_prefix000_frozen
end BB6.Agent2AllQE1101101100
