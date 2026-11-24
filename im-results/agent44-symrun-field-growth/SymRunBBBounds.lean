import SymRunBBBase

/-! Sharper independent length and numeric-mass bounds for the exact BB sweep. -/

open BusyBeaver.SymRunEngine

namespace BusyBeaver.SymRunAudit

/-- Simultaneous amortized bounds: arbitrary right stacks get +12,
    while a right stack headed by run 0 gets one unit of extra slack. -/
theorem sweepBB_length_bound4_pair (L : List SymTok) :
    ∀ R : List SymTok,
      stateTokenCount (sweepBB L R) ≤ L.length + R.length + 4 * L.length + 12 ∧
      (∀ R1 : List SymTok,
        stateTokenCount (sweepBB L (.item (.run 0) :: R1)) ≤
          L.length + R1.length + 1 + 4 * L.length + 11) := by
  induction L with
  | nil =>
    intro R
    constructor
    · have hstep := stepElemBB_length_le [] R
      calc
        stateTokenCount (sweepBB [] R) = stateTokenCount (stepElemBB [] R) := by simp [sweepBB]
        _ ≤ R.length + 7 := by simpa using hstep
        _ ≤ [].length + R.length + 4 * [].length + 12 := by omega
    · intro R1
      have hstep := stepElemBB_length_le [] (.item (.run 0) :: R1)
      calc
        stateTokenCount (sweepBB [] (.item (.run 0) :: R1)) =
            stateTokenCount (stepElemBB [] (.item (.run 0) :: R1)) := by simp [sweepBB]
        _ ≤ R1.length + 1 + 7 := by simpa using hstep
        _ ≤ [].length + R1.length + 1 + 4 * [].length + 11 := by omega
  | cons t L1 ih =>
    intro R
    have hrecA (R' : List SymTok) :
        stateTokenCount (sweepBB L1 R') ≤
          L1.length + R'.length + 4 * L1.length + 12 :=
      (ih R').1
    have hrec0 (R' : List SymTok) :
        stateTokenCount (sweepBB L1 (.item (.run 0) :: R')) ≤
          L1.length + R'.length + 1 + 4 * L1.length + 11 :=
      (ih (.item (.run 0) :: R')).2 R'
    constructor
    · cases t with
      | item x =>
        cases x with
        | zero =>
          have hstep := stepElemBB_length_le (.item .zero :: L1) R
          calc
            stateTokenCount (sweepBB (.item .zero :: L1) R) =
                stateTokenCount (stepElemBB (.item .zero :: L1) R) := by simp [sweepBB]
            _ ≤ L1.length + 1 + R.length + 7 := by simpa using hstep
            _ ≤ (L1.length + 1) + R.length + 4 * (L1.length + 1) + 12 := by omega
        | run d =>
          cases d with
          | zero =>
            have hrec' := hrec0 R
            calc
              stateTokenCount (sweepBB (.item (.run 0) :: L1) R) =
                  stateTokenCount (sweepBB L1 (.item (.run 0) :: R)) := by simp [sweepBB]
              _ ≤ L1.length + R.length + 1 + 4 * L1.length + 11 := hrec'
              _ ≤ (L1.length + 1) + R.length + 4 * (L1.length + 1) + 12 := by omega
          | succ d =>
            cases d with
            | zero =>
              have hBump := bumpSymR_length_le R
              have hrec' := hrec0 (bumpSymR R)
              calc
                stateTokenCount (sweepBB (.item (.run 1) :: L1) R) =
                    stateTokenCount (sweepBB L1 (.item (.run 0) :: bumpSymR R)) := by
                      simp [sweepBB, strictList_eq]
                _ ≤ L1.length + (bumpSymR R).length + 1 + 4 * L1.length + 11 := hrec'
                _ ≤ (L1.length + 1) + R.length + 4 * (L1.length + 1) + 12 := by omega
            | succ d =>
              have hstep := stepElemBB_length_le (.item (.run (d + 2)) :: L1) R
              calc
                stateTokenCount (sweepBB (.item (.run (d + 2)) :: L1) R) =
                    stateTokenCount (stepElemBB (.item (.run (d + 2)) :: L1) R) := by
                      simp [sweepBB, strictNat_eq]
                _ ≤ L1.length + 1 + R.length + 7 := by simpa using hstep
                _ ≤ (L1.length + 1) + R.length + 4 * (L1.length + 1) + 12 := by omega
      | repB1 k =>
        have hEat := eatB1_length_le k R
        have hrec' := hrecA (eatB1 k R)
        calc
          stateTokenCount (sweepBB (.repB1 k :: L1) R) =
              stateTokenCount (sweepBB L1 (eatB1 k R)) := by simp [sweepBB, strictList_eq]
          _ ≤ L1.length + (eatB1 k R).length + 4 * L1.length + 12 := hrec'
          _ ≤ (L1.length + 1) + R.length + 4 * (L1.length + 1) + 12 := by omega
      | rep2 p =>
        cases hs : stripPrefixSym [.item (.run 0), .item (.run 1)] R with
        | some R2 =>
          have hprefix := stripPrefixSym_some _ R R2 hs
          have hRsum : listNumSum R = listNumSum R2 + 1 := by
            rw [hprefix, listNumSum_append]
            simp [listNumSum, tokNumSum]
          have hEat := eatB2_num_sum_le p R2
          have hrec' := hrec (.item (.run 0) :: .item (.run 1) :: eatB2 p R2)
          have hsum :
              listNumSum L1 + 1 + listNumSum (eatB2 p R2) ≤
                listNumSum (.rep2 p :: L1) + listNumSum R := by
            simp only [listNumSum, tokNumSum]
            omega
          calc
            symStateNumSum (sweepBB (.rep2 p :: L1) R) =
                symStateNumSum (sweepBB L1
                  (.item (.run 0) :: .item (.run 1) :: eatB2 p R2)) := by
                    simp [sweepBB, hs, strictList_eq]
            _ ≤ listNumSum L1 + 1 + listNumSum (eatB2 p R2) +
                  2 * L1.length + 5 := by
                    simpa [listNumSum, tokNumSum, Nat.add_assoc] using hrec'
            _ ≤ listNumSum (.rep2 p :: L1) + listNumSum R +
                  2 * L1.length + 5 :=
                    Nat.add_le_add_right hsum (2 * L1.length + 5)
            _ ≤ listNumSum (.rep2 p :: L1) + listNumSum R +
                  2 * (L1.length + 1) + 5 := by omega
        | none =>
          have hPeel := peelTok_num_sum_le (.rep2 p) L1
          have hPeel' : listNumSum (peelTok (.rep2 p) L1) ≤
              p + listNumSum L1 + 2 := by
            simpa [tokNumSum] using hPeel
          have hstep := stepElemBB_num_sum_le (peelTok (.rep2 p) L1) R
          calc
            symStateNumSum (sweepBB (.rep2 p :: L1) R) =
                symStateNumSum (stepElemBB (peelTok (.rep2 p) L1) R) := by
                  simp [sweepBB, hs, strictList_eq]
            _ ≤ listNumSum (peelTok (.rep2 p) L1) + listNumSum R + 3 := hstep
            _ ≤ listNumSum (.rep2 p :: L1) + listNumSum R + 5 := by
                  simp only [listNumSum, tokNumSum]
                  omega
            _ ≤ listNumSum (.rep2 p :: L1) + listNumSum R +
                  2 * (L1.length + 1) + 5 := by omega
      | rep12 m =>
        cases hs : stripPrefixSym [.item (.run 0), .item (.run 1)] R with
        | some R2 =>
          have hprefix := stripPrefixSym_some _ R R2 hs
          have hRsum : listNumSum R = listNumSum R2 + 1 := by
            rw [hprefix, listNumSum_append]
            simp [listNumSum, tokNumSum]
          have hEat := eatB12R_num_sum_le m R2
          have hrec' := hrec (.item (.run 0) :: .item (.run 1) :: eatB12R m R2)
          have hsum :
              listNumSum L1 + 1 + listNumSum (eatB12R m R2) ≤
                listNumSum (.rep12 m :: L1) + listNumSum R := by
            simp only [listNumSum, tokNumSum]
            omega
          calc
            symStateNumSum (sweepBB (.rep12 m :: L1) R) =
                symStateNumSum (sweepBB L1
                  (.item (.run 0) :: .item (.run 1) :: eatB12R m R2)) := by
                    simp [sweepBB, hs, strictList_eq]
            _ ≤ listNumSum L1 + 1 + listNumSum (eatB12R m R2) +
                  2 * L1.length + 5 := by
                    simpa [listNumSum, tokNumSum, Nat.add_assoc] using hrec'
            _ ≤ listNumSum (.rep12 m :: L1) + listNumSum R +
                  2 * L1.length + 5 :=
                    Nat.add_le_add_right hsum (2 * L1.length + 5)
            _ ≤ listNumSum (.rep12 m :: L1) + listNumSum R +
                  2 * (L1.length + 1) + 5 := by omega
        | none =>
          have hPeel := peelTok_num_sum_le (.rep12 m) L1
          have hPeel' : listNumSum (peelTok (.rep12 m) L1) ≤
              m + listNumSum L1 + 2 := by
            simpa [tokNumSum] using hPeel
          have hstep := stepElemBB_num_sum_le (peelTok (.rep12 m) L1) R
          calc
            symStateNumSum (sweepBB (.rep12 m :: L1) R) =
                symStateNumSum (stepElemBB (peelTok (.rep12 m) L1) R) := by
                  simp [sweepBB, hs, strictList_eq]
            _ ≤ listNumSum (peelTok (.rep12 m) L1) + listNumSum R + 3 := hstep
            _ ≤ listNumSum (.rep12 m :: L1) + listNumSum R + 5 := by
                  simp only [listNumSum, tokNumSum]
                  omega
            _ ≤ listNumSum (.rep12 m :: L1) + listNumSum R +
                  2 * (L1.length + 1) + 5 := by omega

theorem sweepBB_weight_bound_sharper (L R : List SymTok) :
    symStateWeight (sweepBB L R) ≤
      L.length + R.length + listNumSum L + listNumSum R + 6 * L.length + 17 := by
  have hlen := sweepBB_length_bound4 L R
  have hsum := sweepBB_num_sum_bound L R
  have h := Nat.add_le_add hlen hsum
  simp [symStateWeight, stateTokenCount, symStateNumSum] at h ⊢
  omega

theorem sweepBB_weight_bound_sharp (L R : List SymTok) :
    symStateWeight (sweepBB L R) ≤
      L.length + R.length + listNumSum L + listNumSum R + 7 * L.length + 17 := by
  have hlen := sweepBB_length_bound L R
  have hsum := sweepBB_num_sum_bound L R
  have h := Nat.add_le_add hlen hsum
  simp [symStateWeight, stateTokenCount, symStateNumSum] at h ⊢
  omega

theorem sweepBB_field_max_le (L R : List SymTok) :
    stateFieldMax (sweepBB L R) ≤
      listNumSum L + listNumSum R + 2 * L.length + 5 := by
  have hsum := sweepBB_num_sum_bound L R
  have hsum' :
      listNumSum (sweepBB L R).2.1 + listNumSum (sweepBB L R).2.2 ≤
        listNumSum L + listNumSum R + 2 * L.length + 5 := by
    simpa [symStateNumSum] using hsum
  have hL := listFieldMax_le_listNumSum (sweepBB L R).2.1
  have hR := listFieldMax_le_listNumSum (sweepBB L R).2.2
  have hL' : listFieldMax (sweepBB L R).2.1 ≤
      listNumSum L + listNumSum R + 2 * L.length + 5 := by omega
  have hR' : listFieldMax (sweepBB L R).2.2 ≤
      listNumSum L + listNumSum R + 2 * L.length + 5 := by omega
  simpa [stateFieldMax] using Nat.max_le.mpr ⟨hL', hR'⟩

#print axioms sweepBB_length_bound
#print axioms sweepBB_num_sum_bound
#print axioms sweepBB_weight_bound_sharp
#print axioms sweepBB_field_max_le

end BusyBeaver.SymRunAudit
