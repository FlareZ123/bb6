module
import all F412CountedSweeps
import all F412CountedMacros
import all BusyBeaver.BB6.Halt.M_1RB1RC_1LC0LF_1RF0LD_0RE1LB_1RCHHH_1LD0RA
import all BusyBeaver.Calculi.HaltShared
import SourceCostModel

open Mathlib Relation Nat Turing BusyBeaver
open BusyBeaver.RleStackEngine BusyBeaver.SymRunEngine BB6.Agent11.SourceCost
open BusyBeaver.M_1RB1RC_1LC0LF_1RF0LD_0RE1LB_1RCHHH_1LD0RA
namespace Agent26F412
set_option maxRecDepth 2000000
set_option maxHeartbeats 4000000

/-! Draft: exact-cost shadow of the pinned source dispatcher, using the
quadratic cost closed forms rather than evaluating an astronomical number
of pure steps. Proof branches follow the original source soundness lemmas. -/

def costRuleA (L : List SymTok) (d : Nat) (R_tail : List SymTok) : Nat :=
  match stripPrefixSym [.item (.run 0), .item (.run 0), .item (.run 1), .item (.run 1),
      .item (.run 0), .item (.run 1), .item (.run 1), .item (.run 1), .item (.run 0),
      .item .zero, .item (.run 1)] L with
  | some rest =>
    match matchEndB1 rest with
    | some k =>
      match Nat.ble 2 (d/6) && Nat.ble (d/6) k with
      | true =>
        let n1 := d/6
        let m_new := n1-1
        let k_new := k-n1
        (28*(k_new+m_new)+284) + m_new*(28*k_new+76*m_new+332)
      | false => costElemThenBB .CB L (.item (.run d) :: R_tail)
    | none => costElemThenBB .CB L (.item (.run d) :: R_tail)
  | none => costElemThenBB .CB L (.item (.run d) :: R_tail)

theorem tryRuleA_exact (L : List SymTok) (d : Nat) (R_tail : List SymTok) :
    ReachesIn target_tm (costRuleA L d R_tail)
      (evalSym target_tm (.CB,L,.item (.run d) :: R_tail))
      (evalSym target_tm (tryRuleA L d R_tail)) := by
  unfold tryRuleA costRuleA
  cases hs : stripPrefixSym [.item (.run 0), .item (.run 0), .item (.run 1), .item (.run 1), .item
      (.run 0),
     .item (.run 1), .item (.run 1), .item (.run 1), .item (.run 0), .item .zero, .item (.run 1)]
         L with
  | none => dsimp only; exact elemThenBB_exact .CB L (.item (.run d) :: R_tail)
  | some rest =>
    dsimp only
    cases hm : matchEndB1 rest with
    | none => dsimp only; exact elemThenBB_exact .CB L (.item (.run d) :: R_tail)
    | some k =>
      simp only [strictNat_eq]
      cases hcond : (Nat.ble 2 (d / 6) && Nat.ble (d / 6) k)
      · exact elemThenBB_exact .CB L (.item (.run d) :: R_tail)
      · have hrest := matchEndB1_some rest k hm
        have hL := stripPrefixSym_some _ L rest hs
        rw [hrest] at hL
        have hble : 2 ≤ d / 6 ∧ d / 6 ≤ k := by
          simpa [Bool.and_eq_true, Nat.ble_eq] using hcond
        set n1 := d / 6
        set m_new := n1 - 1
        set k_new := k - n1
        set d_new := d - 6 * n1
        have hk_eq : k = (k_new + m_new) + 1 := by omega
        have hd_eq : d = (d_new + 6 * m_new) + 6 := by omega
        have hlhs : (.CB, L, .item (.run d) :: R_tail) =
            stateA0 ((k_new + m_new) + 1) ((d_new + 6 * m_new) + 6) R_tail := by
          rw [hL, hk_eq, hd_eq]; rfl
        rw [hlhs]
        exact reachesIn_trans (ruleA0_exact (k_new + m_new) (d_new + 6 * m_new) R_tail)
          (by simpa [stateA] using ruleA_iter_exact m_new 0 k_new d_new R_tail)

def costAfterSplitB2 (L : List SymTok) (d2 : Nat) (R_tail : List SymTok)
    (res : Nat × List SymTok) : Nat :=
  match popSep3 res.2 with
  | some (s_sep, rest0) =>
    match popRep12 rest0 with
    | some (m12, rest1) =>
      match stripPrefixSym [.item (.run 1), .item (.run 0), .item (.run 1)] rest1 with
      | some rest2 =>
        match popSep3 rest2 with
        | some (m_sep, rest3) =>
          match matchEndB1 rest3 with
          | some k1 =>
            match Nat.ble 2 res.1 && Nat.ble 2 m12 && Nat.ble m12 k1 with
            | true =>
              let n3 := m12-1
              let p0 := res.1-2
              let k_new := k1-n3
              n3*(136*p0+28*k_new+212*n3+bOffset s_sep m_sep+272)
            | false => costElemThenBB .CB L (.item .zero :: .item (.run d2) :: R_tail)
          | none => costElemThenBB .CB L (.item .zero :: .item (.run d2) :: R_tail)
        | none => costElemThenBB .CB L (.item .zero :: .item (.run d2) :: R_tail)
      | none => costElemThenBB .CB L (.item .zero :: .item (.run d2) :: R_tail)
    | none => costElemThenBB .CB L (.item .zero :: .item (.run d2) :: R_tail)
  | none => costElemThenBB .CB L (.item .zero :: .item (.run d2) :: R_tail)

def costRuleB (L : List SymTok) (d2 : Nat) (R_tail : List SymTok) : Nat :=
  match stripPrefixSym [.item (.run 0)] L with
  | some restL => costAfterSplitB2 L d2 R_tail (splitB2 0 restL)
  | none => costElemThenBB .CB L (.item .zero :: .item (.run d2) :: R_tail)

theorem tryRuleB_exact (L : List SymTok) (d2 : Nat) (R_tail : List SymTok) :
    ReachesIn target_tm (costRuleB L d2 R_tail)
      (evalSym target_tm (.CB,L,.item .zero :: .item (.run d2) :: R_tail))
      (evalSym target_tm (tryRuleB L d2 R_tail)) := by
  unfold tryRuleB costRuleB
  cases hsL : stripPrefixSym [.item (.run 0)] L with
  | none => dsimp only; exact elemThenBB_exact .CB L (.item .zero :: .item (.run d2) ::
      R_tail)
  | some restL =>
    dsimp only [afterSplitB2,costAfterSplitB2]
    cases hsep1 : popSep3 (splitB2 0 restL).2 with
    | none => dsimp only; exact elemThenBB_exact .CB L (.item .zero :: .item (.run d2) ::
        R_tail)
    | some sr1 =>
      rcases sr1 with ⟨s_sep, rest0⟩
      dsimp only
      cases h12 : popRep12 rest0 with
      | none => dsimp only; exact elemThenBB_exact .CB L (.item .zero :: .item (.run d2) ::
          R_tail)
      | some mr1 =>
        rcases mr1 with ⟨m12, rest1⟩
        dsimp only
        cases hs1 : stripPrefixSym [.item (.run 1), .item (.run 0), .item (.run 1)] rest1 with
        | none => dsimp only; exact elemThenBB_exact .CB L (.item .zero :: .item (.run d2) ::
            R_tail)
        | some rest2 =>
          dsimp only
          cases hsep2 : popSep3 rest2 with
          | none => dsimp only; exact elemThenBB_exact .CB L (.item .zero :: .item (.run d2)
              :: R_tail)
          | some mr2 =>
            rcases mr2 with ⟨m_sep, rest3⟩
            dsimp only
            cases hend : matchEndB1 rest3 with
            | none => dsimp only; exact elemThenBB_exact .CB L (.item .zero :: .item (.run d2)
                :: R_tail)
            | some k1 =>
              dsimp only
              cases hcond : (Nat.ble 2 (splitB2 0 restL).1 && Nat.ble 2 m12 && Nat.ble m12 k1)
              · exact elemThenBB_exact .CB L (.item .zero :: .item (.run d2) :: R_tail)
              · simp only [strictNat_eq]
                have hL := stripPrefixSym_some _ L restL hsL
                have hspec := splitB2Aux_spec 32 0 restL
                simp only [repBlock, List.nil_append] at hspec
                change encSymL restL = repBlock [.run 0, .run 1, .run 1] (splitB2 0 restL).1 ++
                    encSymL (splitB2 0 restL).2 at hspec
                obtain ⟨h_s, hs_or⟩ := popSep3_some (splitB2 0 restL).2 s_sep rest0 hsep1
                have h_m12 := popRep12_some rest0 m12 rest1 h12
                have h_r1 := stripPrefixSym_some _ rest1 rest2 hs1
                obtain ⟨h_m, hm_or⟩ := popSep3_some rest2 m_sep rest3 hsep2
                have h_k1 := matchEndB1_some rest3 k1 hend
                simp only [Bool.and_eq_true, Nat.ble_eq] at hcond
                rcases hcond with ⟨⟨hp, hm12⟩, hk1⟩
                set p := (splitB2 0 restL).1
                set n3 := m12 - 1
                set p0 := p - 2
                set k_new := k1 - n3
                have hp_eq : p = (p0 + 1) + 1 := by omega
                have hm_eq : m12 = 0 + n3 + 1 := by omega
                have hk_eq : k1 = k_new + n3 := by omega
                have hp_new : (splitB2 0 restL).1 + 2 * (m12 - 1) - 1 = p0 + 1 + 2 * n3 := by
                    omega
                have hk_new : k1 - (m12 - 1) = k_new := rfl
                have hd_new : d2 + 4 * (m12 - 1) = d2 + 4 * n3 := rfl
                have hlhs : (evalSym target_tm) (.CB, L, .item .zero :: .item (.run d2) :: R_tail)
                    =
                    (evalSym target_tm) (stateB s_sep m_sep (p0 + 1) (0 + n3 + 1) (k_new + n3) d2
                        R_tail) := by
                  simp only [evalSym, stateB, hL, encSymL, hspec, h_s, h_m12, h_r1, h_m, h_k1,
                    hp_eq, hm_eq, hk_eq, repBlock_B2_shift (p0 + 1), List.cons_append,
                        List.nil_append, List.append_assoc]
                rw [hlhs, hp_new]
                simpa only [Nat.mul_zero,Nat.add_zero] using ruleB_iter_exact s_sep m_sep hs_or hm_or n3 p0 0 k_new d2 R_tail

def costRuleBC (L : List SymTok) (d2 : Nat) (R_tail : List SymTok) : Nat :=
  match stripPrefixSym [.item (.run 0), .item (.run 0), .item (.run 1)] L with
  | some rest1 =>
    match popRep2 rest1 with
    | some (p, restC) =>
      match stripPrefixSym [.item (.run 0), .item (.run 1), .item (.run 1), .item (.run 1)] restC with
      | some rest2 =>
        match matchEndB1 rest2 with
        | some k1 =>
          match Nat.ble 3 p && Nat.ble 1 k1 with
          | true => let n4 := p-2; n4*(56*k1+90*n4+288)
          | false => costRuleB L d2 R_tail
        | none => costRuleB L d2 R_tail
      | none => costRuleB L d2 R_tail
    | none => costRuleB L d2 R_tail
  | none => costRuleB L d2 R_tail

theorem tryRuleBC_exact (L : List SymTok) (d2 : Nat) (R_tail : List SymTok) :
    ReachesIn target_tm (costRuleBC L d2 R_tail)
      (evalSym target_tm (.CB,L,.item .zero :: .item (.run d2) :: R_tail))
      (evalSym target_tm (tryRuleBC L d2 R_tail)) := by
  unfold tryRuleBC costRuleBC
  cases hs1 : stripPrefixSym [.item (.run 0), .item (.run 0), .item (.run 1)] L with
  | none => dsimp only; exact tryRuleB_exact L d2 R_tail
  | some rest1 =>
    dsimp only
    cases hp2 : popRep2 rest1 with
    | none => dsimp only; exact tryRuleB_exact L d2 R_tail
    | some pr =>
      rcases pr with ⟨p, restC⟩
      dsimp only
      cases hs2 : stripPrefixSym [.item (.run 0), .item (.run 1), .item (.run 1), .item (.run 1)]
          restC with
      | none => dsimp only; exact tryRuleB_exact L d2 R_tail
      | some rest2 =>
        dsimp only
        cases hend : matchEndB1 rest2 with
        | none => dsimp only; exact tryRuleB_exact L d2 R_tail
        | some k1 =>
          dsimp only
          cases hcond : (Nat.ble 3 p && Nat.ble 1 k1)
          · exact tryRuleB_exact L d2 R_tail
          · simp only [strictNat_eq]
            have hL1 := stripPrefixSym_some _ L rest1 hs1
            have hL2 := popRep2_some rest1 p restC hp2
            have hL3 := stripPrefixSym_some _ restC rest2 hs2
            have hL4 := matchEndB1_some rest2 k1 hend
            simp only [Bool.and_eq_true, Nat.ble_eq] at hcond
            rcases hcond with ⟨hp, hk1⟩
            set n4 := p - 2
            have hp_eq : p = 0 + n4 + 2 := by omega
            have hlhs : (.CB, L, .item .zero :: .item (.run d2) :: R_tail) =
                stateC (0 + n4 + 2) k1 d2 R_tail := by
              rw [hL1, hL2, hL3, hL4, hp_eq]; rfl
            rw [hlhs]
            simpa only [Nat.mul_zero,Nat.zero_add] using ruleC_iter_exact n4 0 k1 d2 R_tail hk1

def costAfterSweepCB : List SymTok × List SymTok → Nat
  | (L,.item .zero :: .item (.run d2) :: R_tail) => costRuleBC L d2 R_tail
  | (L,.item (.run (d+12)) :: R_tail) => costRuleA L (d+12) R_tail
  | (L,R) => costElemThenBB .CB L R

theorem afterSweepCB_exact (p : List SymTok × List SymTok) :
    ReachesIn target_tm (costAfterSweepCB p) (evalSym target_tm (.CB,p.1,p.2))
      (evalSym target_tm (afterSweepCB p)) := by
  rcases p with ⟨L, R⟩
  rcases R with _ | ⟨t1, R1⟩
  · exact elemThenBB_exact .CB L []
  · cases t1 with
    | item it1 =>
      cases it1 with
      | zero =>
        rcases R1 with _ | ⟨t2, R_tail⟩
        · exact elemThenBB_exact .CB L [.item .zero]
        · cases t2 with
          | item it2 =>
            cases it2 with
            | zero => exact elemThenBB_exact .CB L (.item .zero :: .item .zero :: R_tail)
            | run d2 => exact tryRuleBC_exact L d2 R_tail
          | repB1 k => exact elemThenBB_exact .CB L (.item .zero :: .repB1 k :: R_tail)
          | rep2 p => exact elemThenBB_exact .CB L (.item .zero :: .rep2 p :: R_tail)
          | rep12 m => exact elemThenBB_exact .CB L (.item .zero :: .rep12 m :: R_tail)
      | run d =>
        rcases d with _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | d
        · exact elemThenBB_exact .CB L (.item (.run 0) :: R1)
        · exact elemThenBB_exact .CB L (.item (.run 1) :: R1)
        · exact elemThenBB_exact .CB L (.item (.run 2) :: R1)
        · exact elemThenBB_exact .CB L (.item (.run 3) :: R1)
        · exact elemThenBB_exact .CB L (.item (.run 4) :: R1)
        · exact elemThenBB_exact .CB L (.item (.run 5) :: R1)
        · exact elemThenBB_exact .CB L (.item (.run 6) :: R1)
        · exact elemThenBB_exact .CB L (.item (.run 7) :: R1)
        · exact elemThenBB_exact .CB L (.item (.run 8) :: R1)
        · exact elemThenBB_exact .CB L (.item (.run 9) :: R1)
        · exact elemThenBB_exact .CB L (.item (.run 10) :: R1)
        · exact elemThenBB_exact .CB L (.item (.run 11) :: R1)
        · exact tryRuleA_exact L (d + 12) R1
    | repB1 k => exact elemThenBB_exact .CB L (.repB1 k :: R1)
    | rep2 p => exact elemThenBB_exact .CB L (.rep2 p :: R1)
    | rep12 m => exact elemThenBB_exact .CB L (.rep12 m :: R1)

def costStepSym : SymState → Nat
  | (.BB,L,R) => costSweepBB L R
  | (.DL,L,R) => costElemThenBB .DL (peelL L) R
  | (.HALT,_,_) => 0
  | (.CB,L,R) => costSweepCB L R + costAfterSweepCB (sweepCB L R)

theorem stepSym_exact (s : SymState) :
    ReachesIn target_tm (costStepSym s) (evalSym target_tm s)
      (evalSym target_tm (stepSym s)) := by
  rcases s with ⟨m, L, R⟩
  cases m with
  | BB => exact sweepBB_exact L R
  | DL =>
    simp only [stepSym,costStepSym,strictList_eq]
    have heq : (evalSym target_tm) (.DL, L, R) = (evalSym target_tm) (.DL, peelL L, R) := by
      simp only [evalSym, encSymL_peelL]
    rw [heq]
    exact elemThenBB_exact .DL (peelL L) R
  | HALT => rfl
  | CB =>
    exact reachesIn_trans (sweepCB_exact L R) (afterSweepCB_exact (sweepCB L R))

def costSymIter : Nat → SymState → Nat
  | 0,_ => 0
  | n+1,s => costStepSym s + costSymIter n (stepSym s)

theorem costSymIter_exact (n : Nat) (s : SymState) :
    ReachesIn target_tm (costSymIter n s) (evalSym target_tm s)
      (evalSym target_tm (iterStep stepSym n s)) := by
  induction n generalizing s with
  | zero => rfl
  | succ n ih => exact reachesIn_trans (stepSym_exact s) (ih (stepSym s))

#print axioms tryRuleA_exact
#print axioms tryRuleB_exact
#print axioms tryRuleBC_exact
#print axioms afterSweepCB_exact
#print axioms stepSym_exact
#print axioms costSymIter_exact
end Agent26F412
