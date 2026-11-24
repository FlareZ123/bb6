module
import all F412CountedDispatch
import all F412CountedPure
import all BusyBeaver.BB6.Halt.M_1RB1RC_1LC0LF_1RF0LD_0RE1LB_1RCHHH_1LD0RA
import all BusyBeaver.Calculi.HaltShared
import SourceCostModel

open Mathlib Relation Nat Turing BusyBeaver
open BusyBeaver.RleStackEngine BusyBeaver.SymRunEngine BB6.Agent11.SourceCost
open BusyBeaver.M_1RB1RC_1LC0LF_1RF0LD_0RE1LB_1RCHHH_1LD0RA
open BusyBeaver.M_1RB1RC_1LC0LF_1RF0LD_0RE1LB_1RCHHH_1LD0RA.Solution (initSymCyc3 symChk4096 symChk8192 symChk12288 symChk16384 symChk20480 symChk21383 test_elem_rfl sym_chk1 sym_chk2 sym_chk3 sym_chk4 sym_chk5 sym_chk6)

namespace Agent26F412
set_option maxRecDepth 200000
set_option maxHeartbeats 4000000

/-! DRAFT: original-source counted prefix, checkpoint chain and first undefined
transition. Numerical constants are candidate replay results, independently
subject to Lean kernel evaluation. Do not treat the theorem as accepted before
the entire dependency closure passes. -/

abbrev MState := SymMode × List MItem × List MItem

/-- F412's exact primitive charge for one source MItem transition. -/
def costElemM412 : MState → Nat
  | (.BB, [], _) => 1
  | (.BB, .zero :: _, _) => 1
  | (.BB, .run 0 :: _, _) => 6
  | (.BB, .run 1 :: _, _) => 3
  | (.BB, .run 2 :: _, _) => 5
  | (.BB, .run 3 :: _, _) => 9
  | (.BB, .run (d + 4) :: _, _) => 9
  | (.DL, .zero :: _, _) => 0
  | (.DL, .run 0 :: _, _) => 1
  | (.DL, .run 1 :: _, _) => 3
  | (.DL, .run 2 :: _, .run d0 :: _) => 3 * d0 + 20
  | (.CB, _, []) => 2
  | (.CB, _, .zero :: _) => 2
  | (.CB, _, .run 0 :: []) => 3
  | (.CB, _, .run 0 :: .zero :: _) => 3
  | (.CB, _, .run 0 :: .run 0 :: _) => 6
  | (.CB, _, .run 0 :: .run (d2 + 1) :: _) => 3 * d2 + 19
  | (.CB, _, .run 1 :: _) => 3
  | (.CB, _, .run 2 :: _) => 5
  | (.CB, _, .run (d + 3) :: _) => 5
  | _ => 0

/-- Every MItem-level stepElemM branch is an exact original-TM run.
    The only zero-cost branches are stutters or the symbolic HALT marker,
    whose evalM image is the already-halting DL configuration. -/
theorem sourceElemM412_exact (s : MState) :
    ReachesIn target_tm (costElemM412 s)
      (evalM target_tm s)
      (evalM target_tm (stepElemM s)) := by
  rcases s with ⟨mode, L, R⟩
  cases mode with
  | BB =>
    cases L with
    | nil =>
      simpa [costElemM412, stepElemM, strictMList_eq, evalM] using
        step_BB_nil_exact R
    | cons t L1 =>
      cases t with
      | zero =>
        simpa [costElemM412, stepElemM, strictMList_eq, evalM] using
          step_BB_zero_exact L1 R
      | run d =>
        rcases d with _ | _ | _ | _ | d
        · simpa [costElemM412, stepElemM, strictMList_eq, strictNat_eq, evalM] using
            step_BB_run0_exact L1 R
        · simpa [costElemM412, stepElemM, strictMList_eq, strictNat_eq, evalM] using
            step_BB_run1_exact L1 R
        · simpa [costElemM412, stepElemM, strictMList_eq, strictNat_eq, evalM] using
            step_BB_run2_exact L1 R
        · simpa [costElemM412, stepElemM, strictMList_eq, strictNat_eq, evalM] using
            step_BB_run3_exact L1 R
        · simpa [costElemM412, stepElemM, strictMList_eq, strictNat_eq, evalM] using
            step_BB_run_ge4_exact d L1 R
  | DL =>
    cases L with
    | nil => rfl
    | cons t L1 =>
      cases t with
      | zero => rfl
      | run d =>
        rcases d with _ | _ | _ | d
        · simpa [costElemM412, stepElemM, strictMList_eq, strictNat_eq, evalM] using
            step_DL_run0_exact L1 R
        · simpa [costElemM412, stepElemM, strictMList_eq, strictNat_eq, evalM] using
            step_DL_run1_exact L1 R
        · cases R with
          | nil => rfl
          | cons rt R1 =>
            cases rt with
            | zero => rfl
            | run d0 =>
              simpa [costElemM412, stepElemM, strictMList_eq, strictNat_eq,
                prependZeroM_eq, evalM] using
                step_DL_run2_exact d0 L1 R1
        · rfl
  | CB =>
    cases R with
    | nil =>
      simpa [costElemM412, stepElemM, strictMList_eq, evalM] using
        step_CB_nil_exact L
    | cons t R1 =>
      cases t with
      | zero =>
        simpa [costElemM412, stepElemM, strictMList_eq, evalM] using
          step_CB_zero_exact L R1
      | run d =>
        rcases d with _ | _ | _ | d
        · cases R1 with
          | nil =>
            simpa [costElemM412, stepElemM, strictMList_eq, evalM] using
              step_CB_run0_nil_exact L
          | cons t2 R2 =>
            cases t2 with
            | zero =>
              simpa [costElemM412, stepElemM, strictMList_eq, evalM] using
                step_CB_run0_zero_exact L R2
            | run d2 =>
              rcases d2 with _ | d2
              · simpa [costElemM412, stepElemM, strictMList_eq, evalM] using
                  step_CB_run0_run0_exact L R2
              · simpa [costElemM412, stepElemM, strictMList_eq, strictNat_eq,
                  prependZeroM_eq, evalM] using
                  step_CB_run0_run_pos_exact d2 L R2
        · simpa [costElemM412, stepElemM, strictMList_eq, strictNat_eq, evalM] using
            step_CB_run1_exact L R1
        · simpa [costElemM412, stepElemM, strictMList_eq, strictNat_eq, evalM] using
            step_CB_run2_exact L R1
        · simpa [costElemM412, stepElemM, strictMList_eq, strictNat_eq, evalM] using
            step_CB_run_ge3_exact d L R1
  | HALT => rfl


/-- Cost of a finite block of source transitions, including nested blocks. -/
def costBlock {α : Type} (f : α → α) (charge : α → Nat) : Nat → α → Nat
  | 0,_ => 0
  | n+1,s => charge s + costBlock f charge n (f s)

theorem costBlock_exact {α : Type} (f : α → α) (charge : α → Nat)
    (eval : α → Cfg (Fin 2) (Fin 6))
    (h : ∀ s, ReachesIn target_tm (charge s) (eval s) (eval (f s)))
    (n : Nat) (s : α) :
    ReachesIn target_tm (costBlock f charge n s) (eval s) (eval (iterStep f n s)) := by
  induction n generalizing s with
  | zero => rfl
  | succ n ih => exact reachesIn_trans (h s) (ih (f s))

def costM16 := costBlock stepElemM costElemM412 16
def costM256 := costBlock stepElem16 costM16 16
def costM4096 := costBlock stepElem256 costM256 16

theorem costM16_exact (s : MState) :
    ReachesIn target_tm (costM16 s) (evalM target_tm s) (evalM target_tm (stepElem16 s)) :=
  costBlock_exact stepElemM costElemM412 (evalM target_tm) sourceElemM412_exact 16 s

theorem costM256_exact (s : MState) :
    ReachesIn target_tm (costM256 s) (evalM target_tm s) (evalM target_tm (stepElem256 s)) :=
  costBlock_exact stepElem16 costM16 (evalM target_tm) costM16_exact 16 s

theorem costM4096_exact (s : MState) :
    ReachesIn target_tm (costM4096 s) (evalM target_tm s) (evalM target_tm (stepElem4096 s)) :=
  costBlock_exact stepElem256 costM256 (evalM target_tm) costM256_exact 16 s

def costRunElemFast (a b c d : Nat) (s : MState) : Nat :=
  let s1 := iterStep stepElem4096 d s
  let s2 := iterStep stepElem256 c s1
  let s3 := iterStep stepElem16 b s2
  costBlock stepElem4096 costM4096 d s +
    (costBlock stepElem256 costM256 c s1 +
      (costBlock stepElem16 costM16 b s2 + costBlock stepElemM costElemM412 a s3))

theorem runElemFast_exact (a b c d : Nat) (s : MState) :
    ReachesIn target_tm (costRunElemFast a b c d s) (evalM target_tm s)
      (evalM target_tm (runElemFast a b c d s)) := by
  unfold runElemFast costRunElemFast
  exact reachesIn_trans (costBlock_exact stepElem4096 costM4096 (evalM target_tm) costM4096_exact d s)
    (reachesIn_trans (costBlock_exact stepElem256 costM256 (evalM target_tm) costM256_exact c _)
      (reachesIn_trans (costBlock_exact stepElem16 costM16 (evalM target_tm) costM16_exact b _)
        (costBlock_exact stepElemM costElemM412 (evalM target_tm) sourceElemM412_exact a _)))

theorem prefix_cost : costRunElemFast 7 3 11 4 (.BB,[.run 0],[]) = 145981 := by
  decide +kernel

theorem prefix_exact :
    ReachesIn target_tm 145981 (evalM target_tm (.BB,[.run 0],[]))
      (evalSym target_tm initSymCyc3) := by
  have h := runElemFast_exact 7 3 11 4 (.BB,[.run 0],[])
  rw [prefix_cost, test_elem_rfl] at h
  exact h

def costS16 := costBlock stepSym costStepSym 16
def costS256 := costBlock stepSym16 costS16 16
def costS4096 := costBlock stepSym256 costS256 16

theorem costS16_exact (s : SymState) :
    ReachesIn target_tm (costS16 s) (evalSym target_tm s) (evalSym target_tm (stepSym16 s)) :=
  costBlock_exact stepSym costStepSym (evalSym target_tm) stepSym_exact 16 s

theorem costS256_exact (s : SymState) :
    ReachesIn target_tm (costS256 s) (evalSym target_tm s) (evalSym target_tm (stepSym256 s)) :=
  costBlock_exact stepSym16 costS16 (evalSym target_tm) costS16_exact 16 s

theorem costS4096_exact (s : SymState) :
    ReachesIn target_tm (costS4096 s) (evalSym target_tm s) (evalSym target_tm (stepSym4096 s)) :=
  costBlock_exact stepSym256 costS256 (evalSym target_tm) costS256_exact 16 s

theorem chunk1_cost : costS4096 initSymCyc3 = 9518578242199 := by
  decide +kernel

theorem chunk1_exact :
    ReachesIn target_tm 9518578242199 (evalSym target_tm initSymCyc3)
      (evalSym target_tm symChk4096) := by
  have h := costS4096_exact initSymCyc3
  rw [chunk1_cost,sym_chk1] at h
  exact h

theorem chunk2_cost : costS4096 symChk4096 = 149532004664058688687 := by
  decide +kernel

theorem chunk2_exact :
    ReachesIn target_tm 149532004664058688687 (evalSym target_tm symChk4096)
      (evalSym target_tm symChk8192) := by
  have h := costS4096_exact symChk4096
  rw [chunk2_cost,sym_chk2] at h
  exact h

theorem chunk3_cost : costS4096 symChk8192 = 1668449373591493359382258349 := by
  decide +kernel

theorem chunk3_exact :
    ReachesIn target_tm 1668449373591493359382258349 (evalSym target_tm symChk8192)
      (evalSym target_tm symChk12288) := by
  have h := costS4096_exact symChk8192
  rw [chunk3_cost,sym_chk3] at h
  exact h

theorem chunk4_cost : costS4096 symChk12288 = 16553212053510893735896880543847944 := by
  decide +kernel

theorem chunk4_exact :
    ReachesIn target_tm 16553212053510893735896880543847944 (evalSym target_tm symChk12288)
      (evalSym target_tm symChk16384) := by
  have h := costS4096_exact symChk12288
  rw [chunk4_cost,sym_chk4] at h
  exact h

theorem chunk5_cost : costS4096 symChk16384 = 291963809089010400933573307583128936745424 := by
  decide +kernel

theorem chunk5_exact :
    ReachesIn target_tm 291963809089010400933573307583128936745424 (evalSym target_tm symChk16384)
      (evalSym target_tm symChk20480) := by
  have h := costS4096_exact symChk16384
  rw [chunk5_cost,sym_chk5] at h
  exact h

def costLast903 (s : SymState) : Nat :=
  let s1 := iterStep stepSym256 3 s
  let s2 := iterStep stepSym16 8 s1
  costBlock stepSym256 costS256 3 s +
    (costBlock stepSym16 costS16 8 s1 + costBlock stepSym costStepSym 7 s2)

theorem chunk6_cost : costLast903 symChk20480 = 8925127379187536836852650690361217137654196 := by
  decide +kernel

theorem chunk6_exact :
    ReachesIn target_tm 8925127379187536836852650690361217137654196 (evalSym target_tm symChk20480)
      (evalSym target_tm symChk21383) := by
  have h : ReachesIn target_tm (costLast903 symChk20480)
      (evalSym target_tm symChk20480)
      (evalSym target_tm (iterStep stepSym 7 (iterStep stepSym16 8 (iterStep stepSym256 3 symChk20480)))) := by
    exact reachesIn_trans
      (costBlock_exact stepSym256 costS256 (evalSym target_tm) costS256_exact 3 symChk20480)
      (reachesIn_trans
        (costBlock_exact stepSym16 costS16 (evalSym target_tm) costS16_exact 8 _)
        (costBlock_exact stepSym costStepSym (evalSym target_tm) stepSym_exact 7 _))
  rw [chunk6_cost,sym_chk6] at h
  exact h

theorem rootLive :
    ∃ cfg : Cfg (Fin 2) (Fin 6),
      ReachesIn target_tm 9217091204829760959746640857348768637582782 (init []) cfg ∧
      step target_tm cfg = none := by
  have h0 := init_to_BB_exact
  have hs := reachesIn_trans h0 (reachesIn_trans prefix_exact (reachesIn_trans chunk1_exact
    (reachesIn_trans chunk2_exact (reachesIn_trans chunk3_exact
      (reachesIn_trans chunk4_exact (reachesIn_trans chunk5_exact chunk6_exact))))))
  have hf := step_DL_zero_halt_exact
    (encSymL [.item .zero, .item (.run 1), .item (.run 1), .item (.run 0), .item (.run 1), .item
        (.run 0), .item .zero, .item .zero, .item (.run 1), .item (.run 0), .item (.run 1), .item
        (.run 2), .rep12 68766212839422643803, .item (.run 2), .repB1 343831064197113217107, .item
        (.run 0)])
    (encSymR [.item (.run 1), .item (.run 0), .item (.run 1), .item (.run 1), .item (.run 0),
        .item (.run 1), .item .zero, .item (.run 3), .item (.run 1), .item (.run 1)])
  exact ⟨_, reachesIn_trans hs hf, rfl⟩

public section

/-- Exact first undefined transition, in the original source semantics.
The step just before it still returns a configuration. -/
theorem F412_exact_halt :
    multiStep BusyBeaver.M_1RB1RC_1LC0LF_1RF0LD_0RE1LB_1RCHHH_1LD0RA.target (init []) 9217091204829760959746640857348768637582783 = none ∧
      (multiStep BusyBeaver.M_1RB1RC_1LC0LF_1RF0LD_0RE1LB_1RCHHH_1LD0RA.target (init []) 9217091204829760959746640857348768637582782).isSome = true := by
  obtain ⟨cfg,hReach,hStop⟩ := rootLive
  change multiStep target_tm (init []) _ = some cfg at hReach
  constructor
  · change multiStep target_tm (init []) (9217091204829760959746640857348768637582782 + 1) = none
    rw [multiStep_succ',hReach,hStop]
    rfl
  · change (multiStep target_tm (init []) 9217091204829760959746640857348768637582782).isSome = true
    rw [hReach]
    rfl

#print axioms F412_exact_halt

end
end Agent26F412
