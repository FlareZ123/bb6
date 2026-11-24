module
public import CountedSymPure

@[expose] public section

open Mathlib Relation Nat Turing BusyBeaver
open BusyBeaver.RleStackEngine BusyBeaver.SymRunEngine BB6.Agent11.SourceCost

namespace BB6.Agent49.CountedSym.CountedAtoms
set_option maxRecDepth 200000
set_option maxHeartbeats 4000000
variable {target_tm : Machine (Fin 2) (Fin 6)} {flag : Bool}
variable (rules : CountedAtoms target_tm flag)
include rules

/-! Machine-independent counted counterparts to the original HaltShared sweeps.
The charge functions depend on the cost variant, and all actual tape-state
changes use the unchanged upstream functions. Adapted from Agent26's counted
F412 sweep draft; it is not accepted until original-source CI passes. -/

def costSweepBB (flag : Bool) : List SymTok → List SymTok → Nat
  | [], _ => costElemBB flag []
  | .item .zero :: L1, _ => costElemBB flag (.item .zero :: L1)
  | .item (.run 0) :: L1, R => fcost flag 8 6 + costSweepBB flag L1 (.item (.run 0) :: R)
  | .item (.run 1) :: L1, R => 3 + costSweepBB flag L1 (.item (.run 0) :: bumpSymR R)
  | .item (.run (d+2)) :: L1, _ => costElemBB flag (.item (.run (d+2)) :: L1)
  | .repB1 k :: L1, R => fcost flag 11 9 * k + costSweepBB flag L1 (eatB1 k R)
  | .rep2 p :: L1, R =>
    match stripPrefixSym [.item (.run 0), .item (.run 1)] R with
    | some R2 => fcost flag 14 12 * p + costSweepBB flag L1 (.item (.run 0) :: .item (.run 1) :: eatB2 p R2)
    | none => costElemBB flag (peelTok (.rep2 p) L1)
  | .rep12 m :: L1, R =>
    match stripPrefixSym [.item (.run 0), .item (.run 1)] R with
    | some R2 => fcost flag 25 21 * m + costSweepBB flag L1 (.item (.run 0) :: .item (.run 1) :: eatB12R m R2)
    | none => costElemBB flag (peelTok (.rep12 m) L1)

theorem sweepBB_exact (L R : List SymTok) :
    ReachesIn target_tm (costSweepBB flag L R) (evalSym target_tm (.BB,L,R))
      (evalSym target_tm (sweepBB L R)) := by
  induction L generalizing R with
  | nil => exact rules.sourceElemBB_exact [] R
  | cons t L1 ih =>
    cases t with
    | item it =>
      cases it with
      | zero => exact rules.sourceElemBB_exact (.item .zero :: L1) R
      | run d =>
        rcases d with _ | _ | d
        · simp only [sweepBB, costSweepBB]
          exact ReachesIn.trans (rules.step_BB_run0_exact (encSymL L1) (encSymR R))
            (ih (.item (.run 0) :: R))
        · simp only [sweepBB, costSweepBB, strictList_eq]
          have h1 : ReachesIn target_tm 3
              (evalSym target_tm (.BB,.item (.run 1) :: L1,R))
              (evalSym target_tm (.BB,L1,.item (.run 0) :: bumpSymR R)) := by
            simp only [evalSym, evalM, encSymL, encSymR, encSymR_bumpSymR]
            exact rules.step_BB_run1_exact (encSymL L1) (encSymR R)
          exact ReachesIn.trans h1 (ih (.item (.run 0) :: bumpSymR R))
        · simpa only [sweepBB,costSweepBB,strictNat_eq] using
            rules.sourceElemBB_exact (.item (.run (d+2)) :: L1) R
    | repB1 k =>
      simp only [sweepBB, costSweepBB, strictList_eq]
      have h1 : ReachesIn target_tm (fcost flag 11 9 * k)
          (evalSym target_tm (.BB,.repB1 k :: L1,R))
          (evalSym target_tm (.BB,L1,eatB1 k R)) := by
        simp only [evalSym,evalM,encSymL,encSymR_eatB1]
        exact rules.sweep_BB_B1_exact k (encSymL L1) (encSymR R)
      exact ReachesIn.trans h1 (ih (eatB1 k R))
    | rep2 p =>
      simp only [sweepBB,costSweepBB]
      cases hstrip : stripPrefixSym [.item (.run 0), .item (.run 1)] R with
      | some R2 =>
        have hR := stripPrefixSym_some _ R R2 hstrip
        simp only [strictList_eq]
        have h1 : ReachesIn target_tm (fcost flag 14 12 * p)
            (evalSym target_tm (.BB,.rep2 p :: L1,R))
            (evalSym target_tm (.BB,L1,.item (.run 0) :: .item (.run 1) :: eatB2 p R2)) := by
          rw [hR]
          simp only [evalSym,evalM,encSymL,encSymR,encSymR_eatB2,List.cons_append,List.nil_append]
          exact rules.sweep_BB_C2_exact p (encSymL L1) (encSymR R2)
        exact ReachesIn.trans h1 (ih (.item (.run 0) :: .item (.run 1) :: eatB2 p R2))
      | none =>
        simp only [strictList_eq]
        have heq : evalSym target_tm (.BB,.rep2 p :: L1,R) =
            evalSym target_tm (.BB,peelTok (.rep2 p) L1,R) := by
          simp only [evalSym,encSymL_peelTok]
        rw [heq]
        exact rules.sourceElemBB_exact (peelTok (.rep2 p) L1) R
    | rep12 m =>
      simp only [sweepBB,costSweepBB]
      cases hstrip : stripPrefixSym [.item (.run 0), .item (.run 1)] R with
      | some R2 =>
        have hR := stripPrefixSym_some _ R R2 hstrip
        simp only [strictList_eq]
        have h1 : ReachesIn target_tm (fcost flag 25 21 * m)
            (evalSym target_tm (.BB,.rep12 m :: L1,R))
            (evalSym target_tm (.BB,L1,.item (.run 0) :: .item (.run 1) :: eatB12R m R2)) := by
          rw [hR]
          simp only [evalSym,evalM,encSymL,encSymR,encSymR_eatB12R,List.cons_append,List.nil_append]
          exact rules.sweep_BB_C12_exact m (encSymL L1) (encSymR R2)
        exact ReachesIn.trans h1 (ih (.item (.run 0) :: .item (.run 1) :: eatB12R m R2))
      | none =>
        simp only [strictList_eq]
        have heq : evalSym target_tm (.BB,.rep12 m :: L1,R) =
            evalSym target_tm (.BB,peelTok (.rep12 m) L1,R) := by
          simp only [evalSym,encSymL_peelTok]
        rw [heq]
        exact rules.sourceElemBB_exact (peelTok (.rep12 m) L1) R

def costSweepCB (flag : Bool) (L : List SymTok) : List SymTok → Nat
  | [] => 0
  | .item .zero :: _ => 0
  | .item (.run 0) :: .item (.run 1) :: R2 =>
    fcost flag 21 19 + costSweepCB flag (.item (.run 0) :: .item (.run 0) :: bumpSymL L) R2
  | .item (.run 0) :: _ => 0
  | .item (.run 1) :: R1 => 3 + costSweepCB flag (.item (.run 0) :: bumpSymL L) R1
  | .item (.run (_+2)) :: _ => 0
  | .repB1 k :: R1 =>
    match stripPrefixSym [.item (.run 0)] L with
    | some L1 => 1fcost flag 11 9 * k + costSweepCB flag (.item (.run 0) :: eatB1 k L1) R1
    | none => 0
  | .rep2 p :: R1 =>
    match stripPrefixSym [.item (.run 0)] L with
    | some L1 => fcost flag 24 22 * p + costSweepCB flag (.item (.run 0) :: eatC2 p L1) R1
    | none => 0
  | .rep12 m :: R1 =>
    match stripPrefixSym [.item (.run 0)] L with
    | some L1 => fcost flag 45 41 * m + costSweepCB flag (.item (.run 0) :: eatC12 m L1) R1
    | none => 0

theorem sweepCB_exact (L R : List SymTok) :
    ReachesIn target_tm (costSweepCB flag L R) (evalSym target_tm (.CB,L,R))
      (evalSym target_tm (.CB,(sweepCB L R).1,(sweepCB L R).2)) := by
  induction L, R using sweepCB.induct with
  | case1 L => rfl
  | case2 L R1 => rfl
  | case3 L R2 ih =>
    simp only [sweepCB,costSweepCB,strictList_eq]
    have h1 : ReachesIn target_tm (fcost flag 21 19)
        (evalSym target_tm (.CB,L,.item (.run 0) :: .item (.run 1) :: R2))
        (evalSym target_tm (.CB,.item (.run 0) :: .item (.run 0) :: bumpSymL L,R2)) := by
      simp only [evalSym,evalM,encSymL,encSymR,encSymL_bumpSymL]
      simpa using rules.step_CB_run0_run_pos_exact 0 (encSymL L) (encSymR R2)
    exact ReachesIn.trans h1 (ih (bumpSymL L))
  | case4 L R1 hnot =>
    cases R1 with
    | nil => rfl
    | cons y R2 =>
      cases y with
      | item it =>
        cases it with
        | zero => rfl
        | run d =>
          rcases d with _ | _ | d
          · rfl
          · exfalso; exact hnot R2 rfl
          · rfl
      | repB1 _ => rfl
      | rep2 _ => rfl
      | rep12 _ => rfl
  | case5 L R1 ih =>
    simp only [sweepCB,costSweepCB,strictList_eq]
    have h1 : ReachesIn target_tm 3
        (evalSym target_tm (.CB,L,.item (.run 1) :: R1))
        (evalSym target_tm (.CB,.item (.run 0) :: bumpSymL L,R1)) := by
      simp only [evalSym,evalM,encSymL,encSymR,encSymL_bumpSymL]
      exact rules.step_CB_run1_exact (encSymL L) (encSymR R1)
    exact ReachesIn.trans h1 (ih (bumpSymL L))
  | case6 L d R1 => rfl
  | case7 L k R1 L1 hstrip ih =>
    have hL := stripPrefixSym_some _ L L1 hstrip
    simp only [sweepCB,costSweepCB,hstrip,strictList_eq]
    have h1 : ReachesIn target_tm (1fcost flag 11 9 * k)
        (evalSym target_tm (.CB,L,.repB1 k :: R1))
        (evalSym target_tm (.CB,.item (.run 0) :: eatB1 k L1,R1)) := by
      rw [hL]
      simp only [evalSym,evalM,encSymL,encSymR,encSymL_eatB1,List.cons_append,List.nil_append]
      exact rules.sweep_CB_B1_exact k (encSymL L1) (encSymR R1)
    exact ReachesIn.trans h1 (ih (eatB1 k L1))
  | case8 L k R1 hstrip =>
    simp only [sweepCB,costSweepCB,hstrip]
    rfl
  | case9 L p R1 L1 hstrip ih =>
    have hL := stripPrefixSym_some _ L L1 hstrip
    simp only [sweepCB,costSweepCB,hstrip,strictList_eq]
    have h1 : ReachesIn target_tm (fcost flag 24 22 * p)
        (evalSym target_tm (.CB,L,.rep2 p :: R1))
        (evalSym target_tm (.CB,.item (.run 0) :: eatC2 p L1,R1)) := by
      rw [hL]
      simp only [evalSym,evalM,encSymL,encSymR,encSymL_eatC2,List.cons_append,List.nil_append]
      exact rules.sweep_CB_B2_exact p (encSymL L1) (encSymR R1)
    exact ReachesIn.trans h1 (ih (eatC2 p L1))
  | case10 L p R1 hstrip =>
    simp only [sweepCB,costSweepCB,hstrip]
    rfl
  | case11 L m R1 L1 hstrip ih =>
    have hL := stripPrefixSym_some _ L L1 hstrip
    simp only [sweepCB,costSweepCB,hstrip,strictList_eq]
    have h1 : ReachesIn target_tm (fcost flag 45 41 * m)
        (evalSym target_tm (.CB,L,.rep12 m :: R1))
        (evalSym target_tm (.CB,.item (.run 0) :: eatC12 m L1,R1)) := by
      rw [hL]
      simp only [evalSym,evalM,encSymL,encSymR,encSymL_eatC12,List.cons_append,List.nil_append]
      exact rules.sweep_CB_B12R_exact m (encSymL L1) (encSymR R1)
    exact ReachesIn.trans h1 (ih (eatC12 m L1))
  | case12 L m R1 hstrip =>
    simp only [sweepCB,costSweepCB,hstrip]
    rfl

def costElemSym (flag : Bool) : SymMode → List SymTok → List SymTok → Nat
  | .BB,L,_ => costElemBB flag L
  | .DL,L,R => costElemDL flag L R
  | .CB,_,R => costElemCB flag R
  | .HALT,_,_ => 0

theorem elemSym_exact (m : SymMode) (L R : List SymTok) :
    ReachesIn target_tm (costElemSym flag m L R) (evalSym target_tm (m,L,R))
      (evalSym target_tm (stepElemSym m L R)) := by
  cases m with
  | BB => exact rules.sourceElemBB_exact L R
  | DL => exact rules.sourceElemDL_exact L R
  | CB => exact rules.sourceElemCB_exact L R
  | HALT => rfl

def costFinishBB (flag : Bool) : SymState → Nat
  | (.BB,L,R) => costSweepBB flag L R
  | _ => 0

theorem finishBB_exact (s : SymState) :
    ReachesIn target_tm (costFinishBB flag s) (evalSym target_tm s)
      (evalSym target_tm (finishThenBB s)) := by
  rcases s with ⟨m,L,R⟩
  cases m with
  | BB => exact rules.sweepBB_exact L R
  | DL => rfl
  | CB => rfl
  | HALT => rfl

def costElemThenBB (flag : Bool) (m : SymMode) (L R : List SymTok) : Nat :=
  costElemSym flag m L R + costFinishBB flag (stepElemSym m L R)

theorem elemThenBB_exact (m : SymMode) (L R : List SymTok) :
    ReachesIn target_tm (costElemThenBB flag m L R) (evalSym target_tm (m,L,R))
      (evalSym target_tm (stepElemThenBB m L R)) :=
  ReachesIn.trans (rules.elemSym_exact m L R) (rules.finishBB_exact (stepElemSym m L R))





#print axioms sweepBB_exact
#print axioms sweepCB_exact
#print axioms elemThenBB_exact
end BB6.Agent49.CountedSym.CountedAtoms
end
