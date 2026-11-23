import AllQSourceFeeder
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

/- All symbolic checkpoints keep L and ys untouched. Each segment is
   a small exact original-machine simulation, not an extrapolation. -/
def checkpoint0 (L ys : List Bool) : Cfg :=
  ⟨[false,false,true,false,true] ++ L, false,
    [true,false,true,true,false,true,true,false,false,false] ++ ys, 4⟩

def checkpoint20 (L ys : List Bool) : Cfg :=
  ⟨[false,true,true,false,true,true,false,true,false,true,true,false,true] ++ L, false,
    [false,false] ++ ys, 0⟩

def checkpoint40 (L ys : List Bool) : Cfg :=
  ⟨[true,true,false,true,true,false,true] ++ L, true,
    [true,false,true,false,true,true,true,false] ++ ys, 1⟩

def checkpoint60 (L ys : List Bool) : Cfg :=
  ⟨[false,true,true,true,false,true,true,false,true] ++ L, false,
    [false,true,false,true,false,false] ++ ys, 1⟩

def checkpoint80 (L ys : List Bool) : Cfg :=
  ⟨[true] ++ L, false,
    [true,true,false,true,false,true,false,true,false,true,false,true,false,false] ++ ys, 0⟩

def checkpoint100 (L ys : List Bool) : Cfg :=
  ⟨[true,false,true,false,true,false,true,false,true,false,true,true,true] ++ L, false,
    [true,true] ++ ys, 3⟩

def checkpoint113 (L ys : List Bool) : Cfg :=
  ⟨[] ++ L, true,
    [true,true,true,true,true,true,true,true,true,true,true,true,true,true,true] ++ ys, 5⟩

def checkpoint114 (L ys : List Bool) : Cfg :=
  ⟨[] ++ L, true,
    [true,true,true,true,true,true,true,true,true,true,true,true,true,true,true] ++ ys, 6⟩

theorem segment20 (L ys : List Bool) :
    run 20 (checkpoint0 L ys) = checkpoint20 L ys := by
  simp [checkpoint0,checkpoint20,run,step,goL,goR]

theorem segment40 (L ys : List Bool) :
    run 20 (checkpoint20 L ys) = checkpoint40 L ys := by
  simp [checkpoint20,checkpoint40,run,step,goL,goR]

theorem segment60 (L ys : List Bool) :
    run 20 (checkpoint40 L ys) = checkpoint60 L ys := by
  simp [checkpoint40,checkpoint60,run,step,goL,goR]

theorem segment80 (L ys : List Bool) :
    run 20 (checkpoint60 L ys) = checkpoint80 L ys := by
  simp [checkpoint60,checkpoint80,run,step,goL,goR]

theorem segment100 (L ys : List Bool) :
    run 20 (checkpoint80 L ys) = checkpoint100 L ys := by
  simp [checkpoint80,checkpoint100,run,step,goL,goR]

theorem segment113 (L ys : List Bool) :
    run 13 (checkpoint100 L ys) = checkpoint113 L ys := by
  simp [checkpoint100,checkpoint113,run,step,goL,goR]

theorem segment114 (L ys : List Bool) :
    run 1 (checkpoint113 L ys) = checkpoint114 L ys := by
  simp [checkpoint113,checkpoint114,run,step,goL,goR]

/- The complete 114-step trace reaches frozen halt, for every exterior. -/
theorem terminal000_frozen (L ys : List Bool) :
    (run 114 (⟨[false,false,true,false,true] ++ L,false,
      terminal000 ++ ys,4⟩ : Cfg)).st = 6 := by
  change (run 114 (checkpoint0 L ys)).st = 6
  have hn : 114=20+(20+(20+(20+(20+(13+1))))) := by omega
  rw [hn,run_add,segment20,run_add,segment40,run_add,segment60,
      run_add,segment80,run_add,segment100,run_add,segment113,
      run_add,segment114]
  rfl

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
