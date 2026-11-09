import Lean.Elab.Tactic.Omega
import EDouble

namespace BB6.Agent26EZTwo
open CryptidBoundary

set_option maxRecDepth 8192
set_option maxHeartbeats 10000000

private theorem a_start7 (L ys : List Bool) :
    run 7 (⟨L,false,[true,true,false] ++ ys,0⟩ : Cfg) =
      ⟨[false,true,true] ++ L,false,ys,0⟩ := by
  simp [run,step,goL,goR]

private theorem a_pair_two (q : Nat) (L ys : List Bool) :
    run 2 (⟨L,false,pairs (q+1) ++ ys,0⟩ : Cfg) =
      ⟨[false,true] ++ L,false,pairs q ++ ys,0⟩ := by
  simp [run,step,goL,goR,pairs]

private theorem oppairs_snoc (q : Nat) :
    oppairs q ++ [false,true] = oppairs (q+1) := by
  induction q with
  | zero => rfl
  | succ q ih => simp [oppairs,ih,List.append_assoc]

private theorem a_pair_scan (q : Nat) (L ys : List Bool) :
    run (2*q) (⟨L,false,pairs q ++ ys,0⟩ : Cfg) =
      ⟨oppairs q ++ L,false,ys,0⟩ := by
  induction q generalizing L with
  | zero => rfl
  | succ q ih =>
    have ht : 2*(q+1) = 2+(2*q) := by omega
    rw [ht,run_add,a_pair_two,ih]
    congr 1
    calc
      oppairs q ++ ([false,true] ++ L) =
          (oppairs q ++ [false,true]) ++ L := by simp [List.append_assoc]
      _ = oppairs (q+1) ++ L := by rw [oppairs_snoc]

private theorem a_zero_two (L ys : List Bool) :
    run 2 (⟨L,false,false::ys,0⟩ : Cfg) =
      ⟨L,true,true::ys,2⟩ := by
  simp [run,step,goL,goR]

private theorem c_pair_two (q : Nat) (L ys : List Bool) :
    run 2 (⟨oppairs (q+1) ++ L,true,ys,2⟩ : Cfg) =
      ⟨oppairs q ++ L,true,[true,true] ++ ys,2⟩ := by
  simp [run,step,goL,goR,oppairs]

private theorem c_pair_scan (q : Nat) (L ys : List Bool) :
    run (2*q) (⟨oppairs q ++ L,true,ys,2⟩ : Cfg) =
      ⟨L,true,List.replicate (2*q) true ++ ys,2⟩ := by
  induction q generalizing ys with
  | zero => rfl
  | succ q ih =>
    have ht : 2*(q+1)=2+(2*q) := by omega
    rw [ht,run_add,c_pair_two,ih]
    congr 1
    calc
      List.replicate (2*q) true ++ ([true,true] ++ ys) =
          (List.replicate (2*q) true ++ List.replicate 2 true) ++ ys := by
            simp [List.append_assoc]
      _ = List.replicate (2+2*q) true ++ ys := by
            rw [List.replicate_append_replicate]
            rw [show 2+2*q=2*q+2 by omega]

/-- The short seven-step C finish is inherited from an already audited
    sixteen-step A turn. We isolate it as a reusable arbitrary-suffix map. -/
private theorem c_finish7 (q : Nat) (L ys : List Bool) :
    run 7
      (⟨[false,true,true] ++ (oppairs (q+3) ++ L),
        true,true::ys,2⟩ : Cfg) =
      cWalk (q+1) L ([true,false] ++ List.replicate 6 true ++ ys) := by
  have h := BB6.Agent35.aFront16 q L ys
  change run 16
    (⟨oppairs (q+3) ++ L,false,
      [true,true,false] ++ (false::ys),0⟩ : Cfg) = _ at h
  rw [show (16:Nat)=7+(2+7) by omega,run_add,a_start7] at h
  rw [run_add,a_zero_two] at h
  exact h

/-- Original-machine A/C turn for an unbounded 110(10)^r0 gate,
    with an arbitrary unknown left tail L. Each additional right
    10 pair incurs exactly four primitive steps and adds two 1s
    to the return-side suffix. -/
theorem a_front_Z (q r : Nat) (L ys : List Bool) :
    run (16+4*r)
      (⟨oppairs (q+3) ++ L,false,
        [true,true,false] ++ (pairs r ++ (false::ys)),0⟩ : Cfg) =
      cWalk (q+1) L
        ([true,false] ++ List.replicate (2*r+6) true ++ ys) := by
  let A : List Bool := [false,true,true] ++ (oppairs (q+3) ++ L)
  have hR : run (2*r)
    (⟨A,false,pairs r ++ (false::ys),0⟩ : Cfg) =
      ⟨oppairs r ++ A,false,false::ys,0⟩ :=
    a_pair_scan r A (false::ys)
  have hA : run 2
    (⟨oppairs r ++ A,false,false::ys,0⟩ : Cfg) =
      ⟨oppairs r ++ A,true,true::ys,2⟩ :=
    a_zero_two (oppairs r ++ A) ys
  have hC : run (2*r)
    (⟨oppairs r ++ A,true,true::ys,2⟩ : Cfg) =
      ⟨A,true,List.replicate (2*r) true ++ (true::ys),2⟩ :=
    c_pair_scan r A (true::ys)
  have hcomm :
      List.replicate (2*r) true ++ (true::ys) =
        true :: (List.replicate (2*r) true ++ ys) := by
    induction (2*r) with
    | zero => rfl
    | succ n ih => simp [List.replicate_succ,ih]
  let Z : List Bool := List.replicate (2*r) true ++ ys
  have hrep : List.replicate 6 true ++ List.replicate (2*r) true =
      List.replicate (2*r+6) true := by
    rw [List.replicate_append_replicate]
    congr 1 <;> omega
  have hinput :
      (⟨A,true,List.replicate (2*r) true ++ (true::ys),2⟩ : Cfg) =
      (⟨A,true,true::Z,2⟩ : Cfg) :=
    congrArg (fun w : List Bool => (⟨A,true,w,2⟩ : Cfg)) hcomm
  have hout :
      ([true,false] ++ List.replicate 6 true ++ Z) =
      ([true,false] ++ List.replicate (2*r+6) true ++ ys) := by
    have htail : List.replicate 6 true ++ Z =
        List.replicate (2*r+6) true ++ ys := by
      dsimp [Z]
      calc
        List.replicate 6 true ++ (List.replicate (2*r) true ++ ys) =
            (List.replicate 6 true ++ List.replicate (2*r) true) ++ ys :=
              (List.append_assoc _ _ _).symm
        _ = List.replicate (2*r+6) true ++ ys :=
              congrArg (fun z : List Bool => z ++ ys) hrep
    exact congrArg (fun z : List Bool => [true,false] ++ z) htail
  have hfinish : run 7
    (⟨A,true,List.replicate (2*r) true ++ (true::ys),2⟩ : Cfg) =
      cWalk (q+1) L
        ([true,false] ++ List.replicate (2*r+6) true ++ ys) :=
    (congrArg (run 7) hinput).trans
      ((c_finish7 q L Z).trans (congrArg (cWalk (q+1) L) hout))
  have ht : 16+4*r = 7+(2*r+(2+(2*r+7))) := by omega
  rw [ht,run_add,run_add,run_add,run_add]
  rw [a_start7]
  change run 7 (run (2*r) (run 2
    (run (2*r) (⟨A,false,pairs r ++ (false::ys),0⟩ : Cfg)))) = _
  rw [hR,hA,hC]
  exact hfinish

#print axioms a_front_Z
end BB6.Agent26EZTwo
