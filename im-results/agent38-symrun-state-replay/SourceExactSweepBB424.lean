import SourceExactPureBB424

set_option maxRecDepth 16384
set_option maxHeartbeats 0

open Mathlib Relation Nat Turing BusyBeaver
open BusyBeaver.RleStackEngine BusyBeaver.SymRunEngine
open BB6.Agent11.SourceCost

namespace BusyBeaver.M_1RB0LC_1LC0RE_1RF1LD_1LA0LB_1RD1RA_1LBHHH.Solution

/-- Exact primitive charge of the original source `sweepBB` wrapper for
    F424.  Item transitions and repeated-block sweeps are charged by their
    source exact witnesses; recursive sweep branches add their continuation. -/
def costSweepBB : List SymTok → List SymTok → Nat
  | [], _ => costElemBB true []
  | .item .zero :: L1, _ => costElemBB true (.item .zero :: L1)
  | .item (.run 0) :: L1, R =>
      costElemBB true (.item (.run 0) :: L1) +
        costSweepBB L1 (.item (.run 0) :: R)
  | .item (.run 1) :: L1, R =>
      costElemBB true (.item (.run 1) :: L1) +
        costSweepBB L1 (bumpSymR R)
  | .item (.run (d+2)) :: L1, R =>
      costElemBB true (.item (.run (d+2)) :: L1)
  | .repB1 k :: L1, R =>
      11 * k + costSweepBB L1 (eatB1 k R)
  | .rep2 p :: L1, R =>
      match stripPrefixSym [.item (.run 0), .item (.run 1)] R with
      | some R2 =>
          14 * p + costSweepBB L1
            (.item (.run 0) :: .item (.run 1) :: eatB2 p R2)
      | none => costElemBB true (peelTok (.rep2 p) L1)
  | .rep12 m :: L1, R =>
      match stripPrefixSym [.item (.run 0), .item (.run 1)] R with
      | some R2 =>
          25 * m + costSweepBB L1
            (.item (.run 0) :: .item (.run 1) :: eatB12R m R2)
      | none => costElemBB true (peelTok (.rep12 m) L1)

/-- Exact original-TM primitive cost of every F424 BB-mode sweep.  This is
    the first outer-`stepSym` component; unlike `costPureBB`, it includes
    all recursively swept leading tokens and the terminal `stepElemBB`. -/
theorem sourceSweepBB_exact (L R : List SymTok) :
    ReachesIn target_tm (costSweepBB L R)
      (evalSym target_tm (.BB, L, R))
      (evalSym target_tm (sweepBB L R)) := by
  induction L generalizing R with
  | nil =>
      simpa [sweepBB, costSweepBB, strictList_eq] using
        (sourceElemBB_exact [] R)
  | cons t L1 ih =>
      cases t with
      | item x =>
          cases x with
          | zero =>
              simpa [sweepBB, costSweepBB, strictList_eq] using
                (sourceElemBB_exact (.item .zero :: L1) R)
          | run d =>
              cases d with
              | zero =>
                  have h1 := sourceElemBB_exact (.item (.run 0) :: L1) R
                  have h2 := ih (.item (.run 0) :: R)
                  simpa [sweepBB, costSweepBB, strictList_eq, costElemBB,
                    stepElemBB] using reachesIn_trans h1 h2
              | succ d =>
                  cases d with
                  | zero =>
                      have h1 := sourceElemBB_exact (.item (.run 1) :: L1) R
                      have h2 := ih (bumpSymR R)
                      simpa [sweepBB, costSweepBB, strictList_eq, costElemBB,
                        stepElemBB] using reachesIn_trans h1 h2
                  | succ d =>
                      simpa [sweepBB, costSweepBB, strictList_eq] using
                        (sourceElemBB_exact (.item (.run (d+2)) :: L1) R)
      | repB1 k =>
          have h1 :
              ReachesIn target_tm (11 * k)
                (evalSym target_tm (.BB, .repB1 k :: L1, R))
                (evalSym target_tm (.BB, L1, eatB1 k R)) := by
            simpa [evalSym, evalM, encSymL, encSymR, encSymR_eatB1] using
              (sweep_BB_B1_exact k (encSymL L1) (encSymR R))
          have h2 := ih (eatB1 k R)
          simpa [sweepBB, costSweepBB, strictList_eq] using
            reachesIn_trans h1 h2
      | rep2 p =>
          cases hs : stripPrefixSym [.item (.run 0), .item (.run 1)] R with
          | some R2 =>
              have hR := stripPrefixSym_some _ R R2 hs
              rw [hR]
              have h1 :
                  ReachesIn target_tm (14 * p)
                    (evalSym target_tm
                      (.BB, .rep2 p :: L1, .item (.run 0) :: .item (.run 1) :: R2))
                    (evalSym target_tm
                      (.BB, L1, .item (.run 0) :: .item (.run 1) :: eatB2 p R2)) := by
                simpa [evalSym, evalM, encSymL, encSymR, encSymR_eatB2,
                  List.cons_append, List.nil_append] using
                  (sweep_BB_C2_exact p (encSymL L1) (encSymR R2))
              have h2 := ih (.item (.run 0) :: .item (.run 1) :: eatB2 p R2)
              simpa [sweepBB, costSweepBB, strictList_eq] using
                reachesIn_trans h1 h2
          | none =>
              have heq :
                  evalSym target_tm (.BB, .rep2 p :: L1, R) =
                    evalSym target_tm (.BB, peelTok (.rep2 p) L1, R) := by
                simp only [evalSym, encSymL_peelTok]
              rw [heq]
              simpa [sweepBB, costSweepBB, strictList_eq] using
                (sourceElemBB_exact (peelTok (.rep2 p) L1) R)
      | rep12 m =>
          cases hs : stripPrefixSym [.item (.run 0), .item (.run 1)] R with
          | some R2 =>
              have hR := stripPrefixSym_some _ R R2 hs
              rw [hR]
              have h1 :
                  ReachesIn target_tm (25 * m)
                    (evalSym target_tm
                      (.BB, .rep12 m :: L1, .item (.run 0) :: .item (.run 1) :: R2))
                    (evalSym target_tm
                      (.BB, L1, .item (.run 0) :: .item (.run 1) :: eatB12R m R2)) := by
                simpa [evalSym, evalM, encSymL, encSymR, encSymR_eatB12R,
                  List.cons_append, List.nil_append] using
                  (sweep_BB_C12_exact m (encSymL L1) (encSymR R2))
              have h2 := ih (.item (.run 0) :: .item (.run 1) :: eatB12R m R2)
              simpa [sweepBB, costSweepBB, strictList_eq] using
                reachesIn_trans h1 h2
          | none =>
              have heq :
                  evalSym target_tm (.BB, .rep12 m :: L1, R) =
                    evalSym target_tm (.BB, peelTok (.rep12 m) L1, R) := by
                simp only [evalSym, encSymL_peelTok]
              rw [heq]
              simpa [sweepBB, costSweepBB, strictList_eq] using
                (sourceElemBB_exact (peelTok (.rep12 m) L1) R)


/-- Exact primitive charge of the original source `sweepCB` wrapper for
    F424.  The nontrivial branches are the run0/run1 transition and the three
    repeated-block sweeps; all other branches are representation-only. -/
def costSweepCB : List SymTok → List SymTok → Nat
  | L, [] => 0
  | L, .item .zero :: R1 => 0
  | L, .item (.run 0) :: .item (.run 1) :: R2 =>
      21 + costSweepCB
        (.item (.run 0) :: .item (.run 0) :: bumpSymL L) R2
  | L, .item (.run 0) :: R1 => 0
  | L, .item (.run 1) :: R1 =>
      3 + costSweepCB (.item (.run 0) :: bumpSymL L) R1
  | L, .item (.run (d+2)) :: R1 => 0
  | L, .repB1 k :: R1 =>
      match stripPrefixSym [.item (.run 0)] L with
      | some L1 =>
          21 * k + costSweepCB (.item (.run 0) :: eatB1 k L1) R1
      | none => 0
  | L, .rep2 p :: R1 =>
      match stripPrefixSym [.item (.run 0)] L with
      | some L1 =>
          24 * p + costSweepCB (.item (.run 0) :: eatC2 p L1) R1
      | none => 0
  | L, .rep12 m :: R1 =>
      match stripPrefixSym [.item (.run 0)] L with
      | some L1 =>
          45 * m + costSweepCB (.item (.run 0) :: eatC12 m L1) R1
      | none => 0

/-- Exact original-TM primitive cost of every F424 CB-mode sweep. -/
theorem sourceSweepCB_exact (L R : List SymTok) :
    ReachesIn target_tm (costSweepCB L R)
      (evalSym target_tm (.CB, L, R))
      (evalSym target_tm (.CB, (sweepCB L R).1, (sweepCB L R).2)) := by
  induction L, R using sweepCB.induct with
  | case1 L =>
      simp [sweepCB, costSweepCB]
  | case2 L R1 =>
      simp [sweepCB, costSweepCB]
  | case3 L R2 ih =>
      simp only [sweepCB, strictList_eq]
      have h1 :
          ReachesIn target_tm 21
            (evalSym target_tm
              (.CB, L, .item (.run 0) :: .item (.run 1) :: R2))
            (evalSym target_tm
              (.CB, .item (.run 0) :: .item (.run 0) :: bumpSymL L, R2)) := by
        simpa [evalSym, evalM, encSymL, encSymR, encSymL_bumpSymL] using
          (step_CB_run0_run_pos_exact 0 (encSymL L) (encSymR R2))
      have h2 := ih (bumpSymL L)
      simpa [costSweepCB, sweepCB, strictList_eq] using
        reachesIn_trans h1 h2
  | case4 L R1 hnot =>
      have heq : sweepCB L (.item (.run 0) :: R1) =
          (L, .item (.run 0) :: R1) := by
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
              · exfalso
                exact hnot R2 rfl
              · rfl
          | repB1 _ => rfl
          | rep2 _ => rfl
          | rep12 _ => rfl
      rw [heq]
      change multiStep target_tm 0 _ = some _
      simp only [multiStep_zero]
      rfl
  | case5 L R1 ih =>
      simp only [sweepCB, strictList_eq]
      have h1 :
          ReachesIn target_tm 3
            (evalSym target_tm (.CB, L, .item (.run 1) :: R1))
            (evalSym target_tm (.CB, .item (.run 0) :: bumpSymL L, R1)) := by
        simpa [evalSym, evalM, encSymL, encSymR, encSymL_bumpSymL] using
          (step_CB_run1_exact (encSymL L) (encSymR R1))
      have h2 := ih (bumpSymL L)
      simpa [costSweepCB, sweepCB, strictList_eq] using
        reachesIn_trans h1 h2
  | case6 L d R1 =>
      simp [sweepCB, costSweepCB, strictNat_eq]
  | case7 L k R1 L1 hstrip ih =>
      have hL := stripPrefixSym_some _ L L1 hstrip
      simp only [sweepCB, hstrip, strictList_eq]
      have h1 :
          ReachesIn target_tm (21 * k)
            (evalSym target_tm (.CB, L, .repB1 k :: R1))
            (evalSym target_tm (.CB, .item (.run 0) :: eatB1 k L1, R1)) := by
        rw [hL]
        simp only [evalSym, evalM, encSymL, encSymR, encSymL_eatB1,
          List.cons_append, List.nil_append]
        exact sweep_CB_B1_exact k (encSymL L1) (encSymR R1)
      have h2 := ih (eatB1 k L1)
      simpa [costSweepCB, sweepCB, strictList_eq] using
        reachesIn_trans h1 h2
  | case8 L k R1 hstrip =>
      simp [sweepCB, costSweepCB, hstrip]
  | case9 L p R1 L1 hstrip ih =>
      have hL := stripPrefixSym_some _ L L1 hstrip
      simp only [sweepCB, hstrip, strictList_eq]
      have h1 :
          ReachesIn target_tm (24 * p)
            (evalSym target_tm (.CB, L, .rep2 p :: R1))
            (evalSym target_tm (.CB, .item (.run 0) :: eatC2 p L1, R1)) := by
        rw [hL]
        simp only [evalSym, evalM, encSymL, encSymR, encSymL_eatC2,
          List.cons_append, List.nil_append]
        exact sweep_CB_B2_exact p (encSymL L1) (encSymR R1)
      have h2 := ih (eatC2 p L1)
      simpa [costSweepCB, sweepCB, strictList_eq] using
        reachesIn_trans h1 h2
  | case10 L p R1 hstrip =>
      simp [sweepCB, costSweepCB, hstrip]
  | case11 L m R1 L1 hstrip ih =>
      have hL := stripPrefixSym_some _ L L1 hstrip
      simp only [sweepCB, hstrip, strictList_eq]
      have h1 :
          ReachesIn target_tm (45 * m)
            (evalSym target_tm (.CB, L, .rep12 m :: R1))
            (evalSym target_tm (.CB, .item (.run 0) :: eatC12 m L1, R1)) := by
        rw [hL]
        simp only [evalSym, evalM, encSymL, encSymR, encSymL_eatC12,
          List.cons_append, List.nil_append]
        exact sweep_CB_B12R_exact m (encSymL L1) (encSymR R1)
      have h2 := ih (eatC12 m L1)
      simpa [costSweepCB, sweepCB, strictList_eq] using
        reachesIn_trans h1 h2
  | case12 L m R1 hstrip =>
      simp [sweepCB, costSweepCB, hstrip]

/-- The exact BB-mode `stepSym` theorem is precisely the BB sweep theorem. -/
theorem sourceStepSymBB_exact (L R : List SymTok) :
    ReachesIn target_tm (costSweepBB L R)
      (evalSym target_tm (.BB, L, R))
      (evalSym target_tm (stepSym (.BB, L, R))) := by
  simpa [stepSym] using sourceSweepBB_exact L R

#print axioms sourceSweepBB_exact
#print axioms sourceSweepCB_exact
#print axioms sourceStepSymBB_exact


end BusyBeaver.M_1RB0LC_1LC0RE_1RF1LD_1LA0LB_1RD1RA_1LBHHH.Solution
