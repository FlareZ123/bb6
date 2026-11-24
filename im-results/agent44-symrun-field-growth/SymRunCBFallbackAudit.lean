import SymRunBBBase
import SymRunBBBounds

/-!
Source-connected CB-to-BB fallback field bound, extracted from the maintained
SymRunTraceStats proof. This module deliberately reuses the exact BB base and
BB-sweep bounds and isolates the CB numeric-mass chain from unrelated trace
aggregates and primitive-cost drafts.
-/

open BusyBeaver.SymRunEngine

namespace BusyBeaver.SymRunAudit

theorem bumpSymL_num_sum_le (xs : List SymTok) :
    listNumSum (bumpSymL xs) ≤ listNumSum xs + 3 := by
  induction xs with
  | nil => simp [bumpSymL, listNumSum, tokNumSum]
  | cons t xs ih =>
    cases t with
    | item x => cases x <;> simp [bumpSymL, listNumSum, tokNumSum] <;> omega
    | repB1 k =>
      cases k with
      | zero => simpa [bumpSymL, listNumSum, tokNumSum] using Nat.le_trans ih (by omega)
      | succ k =>
        cases k with
        | zero => simp [bumpSymL, listNumSum, tokNumSum] <;> omega
        | succ k => simp [bumpSymL, listNumSum, tokNumSum, strictNat_eq] <;> omega
    | rep2 p =>
      cases p with
      | zero => simpa [bumpSymL, listNumSum, tokNumSum] using Nat.le_trans ih (by omega)
      | succ p => simp [bumpSymL, listNumSum, tokNumSum, strictNat_eq] <;> omega
    | rep12 m =>
      cases m with
      | zero => simpa [bumpSymL, listNumSum, tokNumSum] using Nat.le_trans ih (by omega)
      | succ m => simp [bumpSymL, listNumSum, tokNumSum, strictNat_eq] <;> omega

theorem eatC2_num_sum_le (k : Nat) (xs : List SymTok) :
    listNumSum (eatC2 k xs) ≤ k + listNumSum xs := by
  simpa [eatC2] using
    (eatFuel_num_sum_le [.item (.run 1), .item (.run 0), .item (.run 1)] .rep2 getRep2
      (by simp [listNumSum, tokNumSum]) (by intro n; simp [tokNumSum])
      getRep2_num 4 k xs)

theorem eatC12_num_sum_le (k : Nat) (xs : List SymTok) :
    listNumSum (eatC12 k xs) ≤ k + listNumSum xs := by
  simpa [eatC12] using
    (eatFuel_num_sum_le [.item (.run 1), .item (.run 0), .item (.run 1), .item (.run 0), .item (.run 1)] .rep12 getRep12
      (by simp [listNumSum, tokNumSum]) (by intro n; simp [tokNumSum])
      getRep12_num 4 k xs)

def symPairNumSum (p : List SymTok × List SymTok) : Nat :=
  listNumSum p.1 + listNumSum p.2

theorem sweepCB_num_sum_bound (L R : List SymTok) :
    symPairNumSum (sweepCB L R) ≤
      listNumSum L + listNumSum R + 3 * R.length := by
  generalize hn : R.length = n
  induction n using Nat.strongRecOn generalizing R L with
  | ind n ih =>
    have hlen : R.length = n := hn
    cases R with
    | nil => simp [symPairNumSum, sweepCB, listNumSum] <;> omega
    | cons t R1 =>
      simp at hlen
      have hrecR1 (L' : List SymTok) :
          symPairNumSum (sweepCB L' R1) ≤
            listNumSum L' + listNumSum R1 + 3 * R1.length :=
        ih R1.length (by omega) L' R1 rfl
      cases t with
      | item x =>
        cases x with
        | zero => simp [symPairNumSum, sweepCB, listNumSum, tokNumSum] <;> omega
        | run d =>
          cases d with
          | zero =>
            cases R1 with
            | nil => simp [symPairNumSum, sweepCB, listNumSum, tokNumSum] <;> omega
            | cons t2 R2 =>
              simp at hlen
              have hrecR2 (L' : List SymTok) :
                  symPairNumSum (sweepCB L' R2) ≤
                    listNumSum L' + listNumSum R2 + 3 * R2.length :=
                ih R2.length (by omega) L' R2 rfl
              cases t2 with
              | item y =>
                cases y with
                | zero => simp [symPairNumSum, sweepCB, listNumSum, tokNumSum] <;> omega
                | run d2 =>
                  cases d2 with
                  | zero => simp [symPairNumSum, sweepCB, listNumSum, tokNumSum] <;> omega
                  | succ d2 =>
                    cases d2 with
                    | zero =>
                      have hB := bumpSymL_num_sum_le L
                      have hEq : R2.length + 2 = n := by omega
                      calc
                        symPairNumSum (sweepCB L (.item (.run 0) :: .item (.run 1) :: R2)) =
                            symPairNumSum (sweepCB (.item (.run 0) :: .item (.run 0) :: bumpSymL L) R2) := by
                          simp [sweepCB, strictList_eq, symPairNumSum, listNumSum, tokNumSum]
                        _ ≤ listNumSum (.item (.run 0) :: .item (.run 0) :: bumpSymL L) +
                              listNumSum R2 + 3 * R2.length :=
                          hrecR2 (.item (.run 0) :: .item (.run 0) :: bumpSymL L)
                        _ ≤ listNumSum L + listNumSum (.item (.run 0) :: .item (.run 1) :: R2) + 3 * n := by
                          simp [listNumSum, tokNumSum]
                          omega
                    | succ d2 => simp [symPairNumSum, sweepCB, listNumSum, tokNumSum] <;> omega
              | repB1 k => simp [symPairNumSum, sweepCB, listNumSum, tokNumSum] <;> omega
              | rep2 p => simp [symPairNumSum, sweepCB, listNumSum, tokNumSum] <;> omega
              | rep12 m => simp [symPairNumSum, sweepCB, listNumSum, tokNumSum] <;> omega
          | succ d =>
            cases d with
            | zero =>
              have hB := bumpSymL_num_sum_le L
              have hEq : R1.length + 1 = n := by omega
              calc
                symPairNumSum (sweepCB L (.item (.run 1) :: R1)) =
                    symPairNumSum (sweepCB (.item (.run 0) :: bumpSymL L) R1) := by
                  simp [sweepCB, strictList_eq, symPairNumSum, listNumSum, tokNumSum]
                _ ≤ listNumSum (.item (.run 0) :: bumpSymL L) + listNumSum R1 + 3 * R1.length :=
                  hrecR1 (.item (.run 0) :: bumpSymL L)
                _ ≤ listNumSum L + listNumSum (.item (.run 1) :: R1) + 3 * n := by
                  simp [listNumSum, tokNumSum]
                  omega
            | succ d => simp [symPairNumSum, sweepCB, listNumSum, tokNumSum] <;> omega
      | repB1 k =>
        cases hs : stripPrefixSym [.item (.run 0)] L with
        | none => simp [symPairNumSum, sweepCB, hs, listNumSum, tokNumSum] <;> omega
        | some L1 =>
          have hprefix := stripPrefixSym_some _ L L1 hs
          have he := eatB1_num_sum_le k L1
          have hEq : R1.length + 1 = n := by omega
          calc
            symPairNumSum (sweepCB L (.repB1 k :: R1)) =
                symPairNumSum (sweepCB (.item (.run 0) :: eatB1 k L1) R1) := by
              simp [sweepCB, hs, strictList_eq, symPairNumSum, listNumSum, tokNumSum]
            _ ≤ listNumSum (.item (.run 0) :: eatB1 k L1) + listNumSum R1 + 3 * R1.length :=
              hrecR1 (.item (.run 0) :: eatB1 k L1)
            _ ≤ listNumSum L + listNumSum (.repB1 k :: R1) + 3 * n := by
              rw [hprefix, listNumSum_append] at *
              simp [listNumSum, tokNumSum]
              omega
      | rep2 p =>
        cases hs : stripPrefixSym [.item (.run 0)] L with
        | none => simp [symPairNumSum, sweepCB, hs, listNumSum, tokNumSum] <;> omega
        | some L1 =>
          have hprefix := stripPrefixSym_some _ L L1 hs
          have he := eatC2_num_sum_le p L1
          have hEq : R1.length + 1 = n := by omega
          calc
            symPairNumSum (sweepCB L (.rep2 p :: R1)) =
                symPairNumSum (sweepCB (.item (.run 0) :: eatC2 p L1) R1) := by
              simp [sweepCB, hs, strictList_eq, symPairNumSum, listNumSum, tokNumSum]
            _ ≤ listNumSum (.item (.run 0) :: eatC2 p L1) + listNumSum R1 + 3 * R1.length :=
              hrecR1 (.item (.run 0) :: eatC2 p L1)
            _ ≤ listNumSum L + listNumSum (.rep2 p :: R1) + 3 * n := by
              rw [hprefix, listNumSum_append] at *
              simp [listNumSum, tokNumSum]
              omega
      | rep12 m =>
        cases hs : stripPrefixSym [.item (.run 0)] L with
        | none => simp [symPairNumSum, sweepCB, hs, listNumSum, tokNumSum] <;> omega
        | some L1 =>
          have hprefix := stripPrefixSym_some _ L L1 hs
          have he := eatC12_num_sum_le m L1
          have hEq : R1.length + 1 = n := by omega
          calc
            symPairNumSum (sweepCB L (.rep12 m :: R1)) =
                symPairNumSum (sweepCB (.item (.run 0) :: eatC12 m L1) R1) := by
              simp [sweepCB, hs, strictList_eq, symPairNumSum, listNumSum, tokNumSum]
            _ ≤ listNumSum (.item (.run 0) :: eatC12 m L1) + listNumSum R1 + 3 * R1.length :=
              hrecR1 (.item (.run 0) :: eatC12 m L1)
            _ ≤ listNumSum L + listNumSum (.rep12 m :: R1) + 3 * n := by
              rw [hprefix, listNumSum_append] at *
              simp [listNumSum, tokNumSum]
              omega

theorem listNumSum_le_length_mul_fieldMax (xs : List SymTok) :
    listNumSum xs ≤ xs.length * listFieldMax xs := by
  induction xs with
  | nil => simp [listNumSum, listFieldMax]
  | cons t xs ih =>
    have ht' : tokNumSum t ≤ listFieldMax (t :: xs) := by
      calc
        tokNumSum t = tokFieldMax t := tokNumSum_eq_tokFieldMax t
        _ ≤ max (tokFieldMax t) (listFieldMax xs) := Nat.le_max_left _ _
        _ = listFieldMax (t :: xs) := by simp [listFieldMax_cons]
    have htail : listFieldMax xs ≤ listFieldMax (t :: xs) := by
      simpa [listFieldMax_cons] using (Nat.le_max_right (tokFieldMax t) (listFieldMax xs))
    have htail' : listNumSum xs ≤ xs.length * listFieldMax (t :: xs) :=
      Nat.le_trans ih (Nat.mul_le_mul_left xs.length htail)
    calc
      listNumSum (t :: xs) = tokNumSum t + listNumSum xs := rfl
      _ ≤ listFieldMax (t :: xs) + xs.length * listFieldMax (t :: xs) := Nat.add_le_add ht' htail'
      _ = (xs.length + 1) * listFieldMax (t :: xs) := by rw [Nat.add_mul]; omega

theorem sweepCB_num_sum_le_94M282 (L R : List SymTok)
    (hT : L.length + R.length ≤ 94) :
    symPairNumSum (sweepCB L R) ≤ 94 * stateFieldMax (.CB, L, R) + 282 := by
  have hLsum := listNumSum_le_length_mul_fieldMax L
  have hRsum := listNumSum_le_length_mul_fieldMax R
  have hLmax : listFieldMax L ≤ stateFieldMax (.CB, L, R) := by
    simpa [stateFieldMax] using (Nat.le_max_left (listFieldMax L) (listFieldMax R))
  have hRmax : listFieldMax R ≤ stateFieldMax (.CB, L, R) := by
    simpa [stateFieldMax] using (Nat.le_max_right (listFieldMax L) (listFieldMax R))
  have hInitial : listNumSum L + listNumSum R ≤ 94 * stateFieldMax (.CB, L, R) := by
    calc
      listNumSum L + listNumSum R ≤ L.length * listFieldMax L + R.length * listFieldMax R := Nat.add_le_add hLsum hRsum
      _ ≤ L.length * stateFieldMax (.CB, L, R) + R.length * stateFieldMax (.CB, L, R) :=
        Nat.add_le_add (Nat.mul_le_mul_left L.length hLmax) (Nat.mul_le_mul_left R.length hRmax)
      _ = (L.length + R.length) * stateFieldMax (.CB, L, R) := by rw [Nat.add_mul]
      _ ≤ 94 * stateFieldMax (.CB, L, R) := Nat.mul_le_mul_right _ hT
  have hSweep := sweepCB_num_sum_bound L R
  have hRlen : R.length ≤ 94 := by omega
  have hGrowth : 3 * R.length ≤ 282 := by omega
  omega

theorem sweepCB_stateFieldMax_le_94M282 (L R : List SymTok)
    (hT : L.length + R.length ≤ 94) :
    stateFieldMax (.CB, (sweepCB L R).1, (sweepCB L R).2) ≤
      94 * stateFieldMax (.CB, L, R) + 282 := by
  have hsum := sweepCB_num_sum_le_94M282 L R hT
  have hL := listFieldMax_le_listNumSum (sweepCB L R).1
  have hR := listFieldMax_le_listNumSum (sweepCB L R).2
  have hmax : stateFieldMax (.CB, (sweepCB L R).1, (sweepCB L R).2) ≤
      symPairNumSum (sweepCB L R) := by
    simp [stateFieldMax, symPairNumSum]
    omega
  exact Nat.le_trans hmax hsum

theorem stepElemCB_BB_num_sum_le (L R : List SymTok)
    (hmode : (stepElemCB L R).1 = .BB) :
    symPairNumSum ((stepElemCB L R).2.1, (stepElemCB L R).2.2) ≤
      listNumSum L + listNumSum R + 3 := by
  cases R with
  | nil =>
      simp only [stepElemCB, strictList_eq] at hmode
      cases hmode
  | cons t R1 =>
    cases t with
    | item x =>
      cases x with
      | zero =>
          simp only [stepElemCB, strictList_eq] at hmode
          cases hmode
      | run d =>
        cases d with
        | zero =>
          cases R1 with
          | nil =>
            have hB := bumpSymL_num_sum_le L
            simp [stepElemCB, stepElemCB_run0, strictList_eq, symPairNumSum, listNumSum, tokNumSum]
            omega
          | cons t2 R2 =>
            cases t2 with
            | item y =>
              cases y with
              | zero =>
                have hB := bumpSymL_num_sum_le L
                simp [stepElemCB, stepElemCB_run0, strictList_eq, symPairNumSum, listNumSum, tokNumSum]
                omega
              | run d2 =>
                cases d2 with
                | zero =>
                  have hB := bumpSymL_num_sum_le L
                  simp [stepElemCB, stepElemCB_run0, strictList_eq, symPairNumSum, listNumSum, tokNumSum]
                  omega
                | succ d2 =>
                    simp only [stepElemCB, stepElemCB_run0, strictList_eq] at hmode
                    cases hmode
            | repB1 k => simp_all [stepElemCB, stepElemCB_run0, strictList_eq]
            | rep2 p => simp_all [stepElemCB, stepElemCB_run0, strictList_eq]
            | rep12 m => simp_all [stepElemCB, stepElemCB_run0, strictList_eq]
        | succ d =>
          cases d with
          | zero =>
              simp only [stepElemCB, strictList_eq] at hmode
              cases hmode
          | succ d =>
            cases d with
            | zero =>
              have hB := bumpSymL_num_sum_le L
              simp [stepElemCB, strictList_eq, symPairNumSum, listNumSum, tokNumSum]
              omega
            | succ d =>
              have hB := bumpSymL_num_sum_le L
              simp [stepElemCB, strictList_eq, symPairNumSum, listNumSum, tokNumSum]
              omega
    | repB1 k => simp_all [stepElemCB, strictList_eq]
    | rep2 p => simp_all [stepElemCB, strictList_eq]
    | rep12 m => simp_all [stepElemCB, strictList_eq]

theorem cb_fallback_bb_input_field_max_le_94M285 (L R : List SymTok)
    (hT : L.length + R.length ≤ 94)
    (hBB : (stepElemCB (sweepCB L R).1 (sweepCB L R).2).1 = .BB) :
    stateFieldMax (.BB,
      (stepElemCB (sweepCB L R).1 (sweepCB L R).2).2.1,
      (stepElemCB (sweepCB L R).1 (sweepCB L R).2).2.2) ≤
      94 * stateFieldMax (.CB, L, R) + 285 := by
  let L2 := (stepElemCB (sweepCB L R).1 (sweepCB L R).2).2.1
  let R2 := (stepElemCB (sweepCB L R).1 (sweepCB L R).2).2.2
  have hSweep := sweepCB_num_sum_le_94M282 L R hT
  have hElem := stepElemCB_BB_num_sum_le (sweepCB L R).1 (sweepCB L R).2 hBB
  have hSweep' :
      listNumSum (sweepCB L R).1 + listNumSum (sweepCB L R).2 + 3 ≤
        94 * stateFieldMax (.CB, L, R) + 285 := by
    have hS : listNumSum (sweepCB L R).1 + listNumSum (sweepCB L R).2 ≤
        94 * stateFieldMax (.CB, L, R) + 282 := by
      simpa [symPairNumSum] using hSweep
    omega
  have hsum : symPairNumSum (L2, R2) ≤ 94 * stateFieldMax (.CB, L, R) + 285 := by
    simpa [L2, R2, symPairNumSum] using Nat.le_trans hElem hSweep'
  have hL2 := listFieldMax_le_listNumSum L2
  have hR2 := listFieldMax_le_listNumSum R2
  have hmax : stateFieldMax (.BB, L2, R2) ≤ symPairNumSum (L2, R2) := by
    simp [stateFieldMax, symPairNumSum]
    omega
  simpa [L2, R2] using Nat.le_trans hmax hsum

theorem cb_fallback_bb_input_field_max_le_pow9 (L R : List SymTok)
    (hT : L.length + R.length ≤ 94)
    (hBB : (stepElemCB (sweepCB L R).1 (sweepCB L R).2).1 = .BB) :
    stateFieldMax (.BB,
      (stepElemCB (sweepCB L R).1 (sweepCB L R).2).2.1,
      (stepElemCB (sweepCB L R).1 (sweepCB L R).2).2.2) ≤
      2^9 * (stateFieldMax (.CB, L, R) + 1) := by
  have h := cb_fallback_bb_input_field_max_le_94M285 L R hT hBB
  omega


def symPairLen (p : List SymTok × List SymTok) : Nat := p.1.length + p.2.length

theorem bumpSymL_length_le (xs : List SymTok) : (bumpSymL xs).length ≤ xs.length + 5 := by
  induction xs with
  | nil => simp [bumpSymL]
  | cons t xs ih =>
    cases t with
    | item x => cases x <;> simp [bumpSymL, strictNat_eq]
    | repB1 k =>
      cases k with
      | zero => simp [bumpSymL]; omega
      | succ k => cases k <;> simp [bumpSymL, strictNat_eq]
    | rep2 p =>
      cases p with
      | zero => simp [bumpSymL]; omega
      | succ p => simp [bumpSymL, strictNat_eq]
    | rep12 m =>
      cases m with
      | zero => simp [bumpSymL]; omega
      | succ m => simp [bumpSymL, strictNat_eq]

theorem eatC2_length_le (k : Nat) (xs : List SymTok) :
    (eatC2 k xs).length ≤ xs.length + 1 := by
  simpa [eatC2] using
    (eatFuel_length_le [.item (.run 1), .item (.run 0), .item (.run 1)] .rep2 getRep2 4 k xs)

theorem eatC12_length_le (k : Nat) (xs : List SymTok) :
    (eatC12 k xs).length ≤ xs.length + 1 := by
  simpa [eatC12] using
    (eatFuel_length_le [.item (.run 1), .item (.run 0), .item (.run 1), .item (.run 0), .item (.run 1)] .rep12 getRep12 4 k xs)

theorem stripPrefixSym_length_suffix (pre xs rest : List SymTok)
    (h : stripPrefixSym pre xs = some rest) : rest.length ≤ xs.length := by
  have hx := stripPrefixSym_some pre xs rest h
  rw [hx, List.length_append]
  omega

theorem sweepCB_length_bound (L R : List SymTok) :
    symPairLen (sweepCB L R) ≤ L.length + R.length + 5 * R.length := by
  generalize hn : R.length = n
  induction n using Nat.strongRecOn generalizing R L with
  | ind n ih =>
    have hlen : R.length = n := hn
    cases R with
    | nil => simp [symPairLen, sweepCB] <;> omega
    | cons t R1 =>
      simp at hlen
      have hR1 : R1.length < n := by omega
      have hrecR1 (L' : List SymTok) :
          symPairLen (sweepCB L' R1) ≤ L'.length + R1.length + 5 * R1.length :=
        ih R1.length (by omega) L' R1 rfl
      cases t with
      | item x =>
        cases x with
        | zero => simp [symPairLen, sweepCB] <;> omega
        | run d =>
          cases d with
          | zero =>
            cases R1 with
            | nil => simp [symPairLen, sweepCB] <;> omega
            | cons t2 R2 =>
              simp at hlen
              have hR2 : R2.length < n := by omega
              have hrecR2 (L' : List SymTok) :
                  symPairLen (sweepCB L' R2) ≤ L'.length + R2.length + 5 * R2.length :=
                ih R2.length (by omega) L' R2 rfl
              cases t2 with
              | item y =>
                cases y with
                | zero => simp [symPairLen, sweepCB] <;> omega
                | run d2 =>
                  cases d2 with
                  | zero => simp [symPairLen, sweepCB] <;> omega
                  | succ d2 =>
                    cases d2 with
                    | zero =>
                      have hb := bumpSymL_length_le L
                      have hL' : (.item (.run 0) :: .item (.run 0) :: bumpSymL L).length ≤ L.length + 7 := by
                        simp
                        omega
                      have hEq : R2.length + 2 = n := by omega
                      calc
                        symPairLen (sweepCB L (.item (.run 0) :: .item (.run 1) :: R2)) =
                            symPairLen (sweepCB (.item (.run 0) :: .item (.run 0) :: bumpSymL L) R2) := by
                          simp [sweepCB, strictList_eq, symPairLen]
                        _ ≤ (.item (.run 0) :: .item (.run 0) :: bumpSymL L).length + R2.length + 5 * R2.length :=
                          hrecR2 (.item (.run 0) :: .item (.run 0) :: bumpSymL L)
                        _ ≤ L.length + n + 5 * n := by rw [← hEq]; omega
                    | succ d2 => simp [symPairLen, sweepCB] <;> omega
              | repB1 k => simp [symPairLen, sweepCB] <;> omega
              | rep2 p => simp [symPairLen, sweepCB] <;> omega
              | rep12 m => simp [symPairLen, sweepCB] <;> omega
          | succ d =>
            cases d with
            | zero =>
              have hb := bumpSymL_length_le L
              have hL' : (.item (.run 0) :: bumpSymL L).length ≤ L.length + 6 := by
                simp
                omega
              have hEq : R1.length + 1 = n := by omega
              calc
                symPairLen (sweepCB L (.item (.run 1) :: R1)) =
                    symPairLen (sweepCB (.item (.run 0) :: bumpSymL L) R1) := by
                  simp [sweepCB, strictList_eq, symPairLen]
                _ ≤ (.item (.run 0) :: bumpSymL L).length + R1.length + 5 * R1.length :=
                  hrecR1 (.item (.run 0) :: bumpSymL L)
                _ ≤ L.length + n + 5 * n := by rw [← hEq]; omega
            | succ d => simp [symPairLen, sweepCB] <;> omega
      | repB1 k =>
        cases hs : stripPrefixSym [.item (.run 0)] L with
        | none => simp [symPairLen, sweepCB, hs] <;> omega
        | some L1 =>
          have hprefix := stripPrefixSym_some _ L L1 hs
          have he := eatB1_length_le k L1
          have hL' : (.item (.run 0) :: eatB1 k L1).length ≤ L.length + 1 := by
            rw [hprefix, List.length_append]
            simp
            omega
          have hEq : R1.length + 1 = n := by omega
          calc
            symPairLen (sweepCB L (.repB1 k :: R1)) = symPairLen (sweepCB (.item (.run 0) :: eatB1 k L1) R1) := by
              simp [sweepCB, hs, strictList_eq, symPairLen]
            _ ≤ (.item (.run 0) :: eatB1 k L1).length + R1.length + 5 * R1.length :=
              hrecR1 (.item (.run 0) :: eatB1 k L1)
            _ ≤ L.length + n + 5 * n := by rw [← hEq]; omega
      | rep2 p =>
        cases hs : stripPrefixSym [.item (.run 0)] L with
        | none => simp [symPairLen, sweepCB, hs] <;> omega
        | some L1 =>
          have hprefix := stripPrefixSym_some _ L L1 hs
          have he := eatC2_length_le p L1
          have hL' : (.item (.run 0) :: eatC2 p L1).length ≤ L.length + 1 := by
            rw [hprefix, List.length_append]
            simp
            omega
          have hEq : R1.length + 1 = n := by omega
          calc
            symPairLen (sweepCB L (.rep2 p :: R1)) = symPairLen (sweepCB (.item (.run 0) :: eatC2 p L1) R1) := by
              simp [sweepCB, hs, strictList_eq, symPairLen]
            _ ≤ (.item (.run 0) :: eatC2 p L1).length + R1.length + 5 * R1.length :=
              hrecR1 (.item (.run 0) :: eatC2 p L1)
            _ ≤ L.length + n + 5 * n := by rw [← hEq]; omega
      | rep12 m =>
        cases hs : stripPrefixSym [.item (.run 0)] L with
        | none => simp [symPairLen, sweepCB, hs] <;> omega
        | some L1 =>
          have hprefix := stripPrefixSym_some _ L L1 hs
          have he := eatC12_length_le m L1
          have hL' : (.item (.run 0) :: eatC12 m L1).length ≤ L.length + 1 := by
            rw [hprefix, List.length_append]
            simp
            omega
          have hEq : R1.length + 1 = n := by omega
          calc
            symPairLen (sweepCB L (.rep12 m :: R1)) = symPairLen (sweepCB (.item (.run 0) :: eatC12 m L1) R1) := by
              simp [sweepCB, hs, strictList_eq, symPairLen]
            _ ≤ (.item (.run 0) :: eatC12 m L1).length + R1.length + 5 * R1.length :=
              hrecR1 (.item (.run 0) :: eatC12 m L1)
            _ ≤ L.length + n + 5 * n := by rw [← hEq]; omega

theorem sweepCB_length_le_six (L R : List SymTok) :
    symPairLen (sweepCB L R) ≤ 6 * (L.length + R.length) := by
  have h := sweepCB_length_bound L R
  omega

theorem stepElemCB_BB_length_bound (L R : List SymTok)
    (hmode : (stepElemCB L R).1 = .BB) :
    symPairLen ((stepElemCB L R).2.1, (stepElemCB L R).2.2) ≤ L.length + R.length + 6 := by
  cases R with
  | nil =>
      simp only [stepElemCB, strictList_eq] at hmode
      cases hmode
  | cons t R1 =>
    cases t with
    | item x =>
      cases x with
      | zero =>
          simp only [stepElemCB, strictList_eq] at hmode
          cases hmode
      | run d =>
        cases d with
        | zero =>
          cases R1 with
          | nil =>
            have hL := bumpSymL_length_le L
            simp [stepElemCB, stepElemCB_run0, strictList_eq, symPairLen]
            omega
          | cons t2 R2 =>
            cases t2 with
            | item y =>
              cases y with
              | zero =>
                have hL := bumpSymL_length_le L
                simp [stepElemCB, stepElemCB_run0, strictList_eq, symPairLen]
                omega
              | run d2 =>
                cases d2 with
                | zero =>
                  have hL := bumpSymL_length_le L
                  simp [stepElemCB, stepElemCB_run0, strictList_eq, symPairLen]
                  omega
                | succ d2 =>
                    simp only [stepElemCB, stepElemCB_run0, strictList_eq] at hmode
                    cases hmode
            | repB1 k => simp [stepElemCB, stepElemCB_run0] at hmode
            | rep2 p => simp [stepElemCB, stepElemCB_run0] at hmode
            | rep12 m => simp [stepElemCB, stepElemCB_run0] at hmode
        | succ d =>
          cases d with
          | zero =>
              simp only [stepElemCB, strictList_eq] at hmode
              cases hmode
          | succ d =>
            cases d with
            | zero =>
              have hL := bumpSymL_length_le L
              simp [stepElemCB, strictList_eq, symPairLen]
              omega
            | succ d =>
              have hL := bumpSymL_length_le L
              simp [stepElemCB, strictList_eq, symPairLen]
              omega
    | repB1 k => simp [stepElemCB] at hmode
    | rep2 p => simp [stepElemCB] at hmode
    | rep12 m => simp [stepElemCB] at hmode

theorem stepElemCB_after_sweep_570 (L R : List SymTok)
    (hT : L.length + R.length ≤ 94)
    (hBB : (stepElemCB (sweepCB L R).1 (sweepCB L R).2).1 = .BB) :
    symPairLen ((stepElemCB (sweepCB L R).1 (sweepCB L R).2).2.1,
      (stepElemCB (sweepCB L R).1 (sweepCB L R).2).2.2) ≤ 570 := by
  have hSweep := sweepCB_length_le_six L R
  have hSweep' : (sweepCB L R).1.length + (sweepCB L R).2.length ≤
      6 * (L.length + R.length) := by simpa [symPairLen] using hSweep
  have hElem := stepElemCB_BB_length_bound (sweepCB L R).1 (sweepCB L R).2 hBB
  omega

theorem cb_fallback_then_bb_sweep_field_max_le_2pow11 (L R : List SymTok)
    (hT : L.length + R.length ≤ 94)
    (hBB : (stepElemCB (sweepCB L R).1 (sweepCB L R).2).1 = .BB) :
    stateFieldMax
      (sweepBB
        (stepElemCB (sweepCB L R).1 (sweepCB L R).2).2.1
        (stepElemCB (sweepCB L R).1 (sweepCB L R).2).2.2) ≤
      2^11 * (stateFieldMax (.CB, L, R) + 1) := by
  let L2 := (stepElemCB (sweepCB L R).1 (sweepCB L R).2).2.1
  let R2 := (stepElemCB (sweepCB L R).1 (sweepCB L R).2).2.2
  have hSweep := sweepCB_num_sum_le_94M282 L R hT
  have hElem := stepElemCB_BB_num_sum_le (sweepCB L R).1 (sweepCB L R).2 hBB
  have hSweep' :
      listNumSum (sweepCB L R).1 + listNumSum (sweepCB L R).2 + 3 ≤
        94 * stateFieldMax (.CB, L, R) + 285 := by
    have hS : listNumSum (sweepCB L R).1 + listNumSum (sweepCB L R).2 ≤
        94 * stateFieldMax (.CB, L, R) + 282 := by
      simpa [symPairNumSum] using hSweep
    omega
  have hsum : listNumSum L2 + listNumSum R2 ≤
      94 * stateFieldMax (.CB, L, R) + 285 := by
    simpa [L2, R2, symPairNumSum] using Nat.le_trans hElem hSweep'
  have hlen := stepElemCB_after_sweep_570 L R hT hBB
  have hlenL : L2.length ≤ 570 := by
    simp [symPairLen, L2, R2] at hlen
    omega
  have hbb := sweepBB_field_max_le L2 R2
  calc
    stateFieldMax (sweepBB L2 R2) ≤
        listNumSum L2 + listNumSum R2 + 2 * L2.length + 5 := hbb
    _ ≤ 94 * stateFieldMax (.CB, L, R) + 285 + 2 * 570 + 5 := by omega
    _ ≤ 2^11 * (stateFieldMax (.CB, L, R) + 1) := by omega

#print axioms bumpSymL_num_sum_le
#print axioms eatC2_num_sum_le
#print axioms eatC12_num_sum_le
#print axioms sweepCB_num_sum_bound
#print axioms sweepCB_num_sum_le_94M282
#print axioms sweepCB_stateFieldMax_le_94M282
#print axioms stepElemCB_BB_num_sum_le
#print axioms cb_fallback_bb_input_field_max_le_94M285
#print axioms cb_fallback_bb_input_field_max_le_pow9
#print axioms stepElemCB_BB_length_bound
#print axioms stepElemCB_after_sweep_570
#print axioms cb_fallback_then_bb_sweep_field_max_le_2pow11

end BusyBeaver.SymRunAudit
