import Lean.Elab.Tactic.Omega
import EHaltCylinder

set_option maxHeartbeats 30000000
set_option maxRecDepth 4096
set_option linter.unusedSimpArgs false

namespace BB6.Agent2AllQE1101101100
open CryptidBoundary

/- Pair blocks in the actual right-hand scan order, and the reversed
   order generated on the left stack by the 2-step A/B scanner. -/
def pairR : Nat → List Bool
  | 0 => []
  | n+1 => true :: false :: pairR n

def pairL : Nat → List Bool
  | 0 => []
  | n+1 => pairL n ++ [false,true]

def word : List Bool :=
  [true,true,false,true,true,false,true,true,false,false]

/- Four primitive steps turn E/0 with left prefix 001 into A/0
   without reading or changing the right-hand list. -/
theorem prelude4 (L r : List Bool) :
    run 4 (⟨[false,false,true] ++ L,false,r,4⟩ : Cfg) =
      ⟨[false,true,true] ++ L,false,r,0⟩ := by
  simp [run,step,goL,goR]

/- The exact two-step scanner rule for the first 10 pair. -/
theorem scan2 (q : Nat) (L ys : List Bool) :
    run 2 (⟨L,false,pairR (q+1) ++ ys,0⟩ : Cfg) =
      ⟨[false,true] ++ L,false,pairR q ++ ys,0⟩ := by
  simp [pairR,run,step,goL,goR]

/- Universal, unbounded scan. No finite bound on q or tape tails. -/
theorem scan_all (q : Nat) (L ys : List Bool) :
    run (2*q) (⟨L,false,pairR q ++ ys,0⟩ : Cfg) =
      ⟨pairL q ++ L,false,ys,0⟩ := by
  induction q generalizing L with
  | zero => rfl
  | succ q ih =>
      calc
        run (2*(q+1)) (⟨L,false,pairR (q+1) ++ ys,0⟩ : Cfg)
            = run (2*q) (run 2 (⟨L,false,pairR (q+1) ++ ys,0⟩ : Cfg)) := by
                rw [show 2*(q+1)=2+2*q by omega,run_add]
        _ = run (2*q) (⟨[false,true] ++ L,false,pairR q ++ ys,0⟩ : Cfg) := by
                rw [scan2]
        _ = (⟨pairL q ++ ([false,true] ++ L),false,ys,0⟩ : Cfg) := ih _
        _ = (⟨pairL (q+1) ++ L,false,ys,0⟩ : Cfg) := by
                simp [pairL,List.append_assoc]

/- The 11 start of the ten-bit trigger takes A/0 to an E/0 boundary
   with exactly 001 on the left and 1101100 on the right. -/
theorem trigger3 (L ys : List Bool) :
    run 3 (⟨L,false,word ++ ys,0⟩ : Cfg) =
      ⟨[false,false,true] ++ L,false,
        BB6.CryptidEHalt.haltWord ++ ys,4⟩ := by
  simp [word,BB6.CryptidEHalt.haltWord,run,step,goL,goR]

/- Every number q of 10 packets, and every unknown left and right tail,
   enters the ORIGINAL source machine frozen state 6 in 73+2*q raw steps. -/
theorem all_q_e_terminal_halt (q : Nat) (L ys : List Bool) :
    (run (73+2*q) (⟨[false,false,true] ++ L,false,
      pairR q ++ word ++ ys,4⟩ : Cfg)).st = 6 := by
  have ht : 73+2*q = 4+(2*q+(3+66)) := by omega
  rw [ht,run_add,prelude4,run_add,scan_all,run_add,trigger3]
  exact BB6.CryptidEHalt.e_halt_66 _ _

#print axioms prelude4
#print axioms scan_all
#print axioms trigger3
#print axioms all_q_e_terminal_halt
end BB6.Agent2AllQE1101101100
