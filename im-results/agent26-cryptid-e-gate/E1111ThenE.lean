import Lean.Elab.Tactic.Omega
import E1101010111ThenB

namespace BB6.Agent26EFour

open CryptidBoundary
open BB6.Agent26E1101010111
open BB6.Agent26EThenB

set_option maxHeartbeats 10000000
set_option maxRecDepth 4096

def eFour (m : Nat) (ys : List Bool) : Cfg :=
  ⟨false::false::pairs (m+2) ++ [true,true], false,
    [true,true,true,true] ++ ys,4⟩

def restTail (ys : List Bool) : List Bool :=
  [true,false,true,false,true,false,true] ++ ys

/-- Shift a 10-stack with one leading zero into an 01-stack. -/
private theorem leftShift (m : Nat) :
    false :: (pairs m ++ [true,true]) =
      oppairs m ++ [false,true,true] := by
  induction m with
  | zero => rfl
  | succ m ih =>
      change false :: true :: (false :: (pairs m ++ [true,true])) =
        false :: true :: (oppairs m ++ [false,true,true])
      rw [ih]

/-- Exactly seventeen original primitive transitions turn an E/1111 boundary
    into the source C-reverse-walk grammar, for arbitrary remaining tape. -/
theorem eFour17 (m : Nat) (ys : List Bool) :
    run 17 (eFour m ys) =
      cWalk (m+1) [false,true,true] (restTail ys) := by
  simp [eFour,cWalk,restTail,run,step,goL,goR,pairs,oppairs]
  exact leftShift m

/-- Four final left moves reach F on physical blank-left zero. -/
theorem cFour4 (ys : List Bool) :
    run 4 (⟨[false,true,true],true,ys,2⟩ : Cfg) =
      ⟨[],false,[true,true,true,true] ++ ys,5⟩ := by
  rfl

/-- All-natural E-boundary transform for four leading ones, independent of
    its remaining right suffix. -/
theorem eFour_run (m : Nat) (ys : List Bool) :
    run (2*m+23) (eFour m ys) =
      ⟨[],false,
        [true,true,true,true] ++
          (List.replicate (2*(m+1)) true ++ restTail ys),5⟩ := by
  have ht : 2*m+23=17+(2*(m+1)+4) := by omega
  rw [ht,run_add,eFour17]
  rw [run_add,cWalk_run]
  change run 4
    (⟨[false,true,true],true,
       List.replicate (2*(m+1)) true ++ restTail ys,2⟩ : Cfg) = _
  exact cFour4 _

/-- F-to-F source rule after an E boundary with four right-hand ones. -/
theorem full_E_four (k : Nat) (ys : List Bool) :
    run (12*k*k+49*k+58)
      (init (List.replicate (3*k+2) true ++
        false :: ([true,true,true,true] ++ ys))) =
      ⟨[],false,
        [true,true,true,true] ++
          (List.replicate (2*((4*k+1)+1)) true ++ restTail ys),5⟩ := by
  have ht : 12*k*k+49*k+58 =
      (12*k*k+41*k+33)+(2*(4*k+1)+23) := by omega
  rw [ht,run_add,prefix_E]
  change run (2*(4*k+1)+23) (eFour (4*k+1) ys) = _
  exact eFour_run (4*k+1) ys

/-- The exceptional E first-return packet, when k=3t+1, is immediately
    a fresh E section with four leading ones. -/
theorem next_e (t q : Nat) (ys : List Bool) :
    (⟨[],false,List.replicate (8*(3*t+1)+5) true ++ bWord q ys,5⟩ : Cfg) =
    init (List.replicate (3*(8*t+3)+2) true ++
      false :: ([true,true,true,true] ++
        (List.replicate (2*q+2) true ++ tail ys))) := by
  rw [bWord_shape]
  have hone :
      List.replicate (8*(3*t+1)+5) true =
        true :: true :: List.replicate (3*(8*t+3)+2) true := by
    have hn : 8*(3*t+1)+5=2+(3*(8*t+3)+2) := by omega
    rw [hn]
    calc
      _ = List.replicate 2 true ++
            List.replicate (3*(8*t+3)+2) true := by
          rw [List.replicate_append_replicate]
      _ = _ := by rfl
  have htwo :
      List.replicate (2*q+6) true =
        [true,true,true,true] ++ List.replicate (2*q+2) true := by
    have hn : 2*q+6=4+(2*q+2) := by omega
    rw [hn]
    calc
      _ = List.replicate 4 true ++ List.replicate (2*q+2) true := by
        rw [List.replicate_append_replicate]
      _ = _ := by rfl
  rw [hone,htwo]
  rfl

/-- A third exact, source-connected two-return sector: k=3t+1 for all q.
    The right suffix remains physically exact for arbitrary ys. -/
theorem e_then_e (t q : Nat) (ys : List Bool) :
    run ((12*(3*t+1)*(3*t+1)+49*(3*t+1)+80+4*q) +
         (12*(8*t+3)*(8*t+3)+49*(8*t+3)+58))
      (init (List.replicate (3*(3*t+1)+2) true ++
        false :: (pairs q ++ wordE ys))) =
      ⟨[],false,
        [true,true,true,true] ++
          (List.replicate (2*((4*(8*t+3)+1)+1)) true ++
            restTail (List.replicate (2*q+2) true ++ tail ys)),5⟩ := by
  rw [run_add,full_E_1101010111_pairs (3*t+1) q ys]
  rw [next_e]
  exact full_E_four (8*t+3) _

#print axioms eFour17
#print axioms eFour_run
#print axioms full_E_four
#print axioms next_e
#print axioms e_then_e

end BB6.Agent26EFour
