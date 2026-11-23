import BusyBeaver.BB6.Halt.M_1RB0LC_1LC0RE_1RF1LD_1LA0LB_1RD1RA_1LBHHH
import BusyBeaver.BB6.Halt.M_1RB1RC_1LC0LF_1RF0LD_0RE1LB_1RCHHH_1LD0RA

/-!
Copyright (c) 2026 FlareZ123. All rights reserved.
Minimal exact-source helper closure for the BB-sweep potential proof.
Extracted from the source-audit work while excluding unrelated legacy lemmas
whose exact-source proofs are still under repair.
-/

set_option maxRecDepth 200000

open BusyBeaver.SymRunEngine

namespace BusyBeaver.SymRunAudit
abbrev SymState := SymMode × List SymTok × List SymTok

def tokFieldMax : SymTok → Nat
  | .item .zero => 0
  | .item (.run n) => n
  | .repB1 n => n
  | .rep2 n => n
  | .rep12 n => n

def listFieldMax (xs : List SymTok) : Nat :=
  xs.foldl (fun a t => max a (tokFieldMax t)) 0

def stateFieldMax (s : SymState) : Nat :=
  max (listFieldMax s.2.1) (listFieldMax s.2.2)

theorem foldl_max_acc (xs : List SymTok) (a : Nat) :
    xs.foldl (fun b t => max b (tokFieldMax t)) a =
      max a (xs.foldl (fun b t => max b (tokFieldMax t)) 0) := by
  induction xs generalizing a with
  | nil => simp
  | cons t xs ih =>
      simp only [List.foldl_cons]
      rw [ih (max a (tokFieldMax t))]
      rw [ih (max 0 (tokFieldMax t))]
      omega

theorem listFieldMax_append (xs ys : List SymTok) :
    listFieldMax (xs ++ ys) = max (listFieldMax xs) (listFieldMax ys) := by
  simp only [listFieldMax, List.foldl_append]
  exact foldl_max_acc ys (xs.foldl (fun a t => max a (tokFieldMax t)) 0)

@[simp] theorem listFieldMax_cons (t : SymTok) (xs : List SymTok) :
    listFieldMax (t :: xs) = max (tokFieldMax t) (listFieldMax xs) := by
  simpa [listFieldMax] using (listFieldMax_append [t] xs)

def stateTokenCount (s : SymState) : Nat :=
  s.2.1.length + s.2.2.length

/-- Maxima over the starting state and every state reached by up to n symbolic transitions. -/

theorem bumpSymR_length_le (xs : List SymTok) : (bumpSymR xs).length ≤ xs.length + 5 := by
  induction xs with
  | nil => simp [bumpSymR]
  | cons t xs ih =>
    cases t with
    | item x => cases x <;> simp [bumpSymR, strictNat_eq]
    | repB1 k =>
      cases k with
      | zero => simp [bumpSymR]; omega
      | succ k => cases k <;> simp [bumpSymR, strictNat_eq]
    | rep2 p =>
      cases p with
      | zero => simp [bumpSymR]; omega
      | succ p => simp [bumpSymR, strictNat_eq]
    | rep12 m =>
      cases m with
      | zero => simp [bumpSymR]; omega
      | succ m => simp [bumpSymR, strictNat_eq]

theorem eatStep_some_length_le (blk : List SymTok) (getRep : SymTok → Option Nat)
    (k k' : Nat) (xs rest : List SymTok)
    (h : eatStep blk getRep k xs = some (k', rest)) : rest.length ≤ xs.length := by
  cases xs with
  | nil => simp [eatStep] at h
  | cons x xs1 =>
    unfold eatStep at h
    cases hget : getRep x with
    | some k2 =>
      simp [hget] at h
      rcases h with ⟨_, hr⟩
      subst rest
      simp
    | none =>
      cases hs : stripPrefixSym blk (x :: xs1) with
      | none => simp [hget, hs] at h
      | some rest2 =>
        simp [hget, hs] at h
        rcases h with ⟨_, hr⟩
        subst rest
        have hprefix := stripPrefixSym_some blk (x :: xs1) rest2 hs
        rw [hprefix, List.length_append]
        omega

theorem eatFuel_length_le (blk : List SymTok) (mkRep : Nat → SymTok)
    (getRep : SymTok → Option Nat) (fuel k : Nat) (xs : List SymTok) :
    (eatFuel blk mkRep getRep fuel k xs).length ≤ xs.length + 1 := by
  induction fuel generalizing k xs with
  | zero => simp [eatFuel]
  | succ fuel ih =>
    cases hs : eatStep blk getRep k xs with
    | none => simp [eatFuel, hs]
    | some pair =>
      rcases pair with ⟨k', rest⟩
      have hlen := eatStep_some_length_le blk getRep k k' xs rest hs
      simp [eatFuel, hs, strictNat_eq]
      exact Nat.le_trans (ih k' rest) (Nat.add_le_add_right hlen 1)

theorem eatB1_length_le (k : Nat) (xs : List SymTok) :
    (eatB1 k xs).length ≤ xs.length + 1 := by
  simpa [eatB1] using
    (eatFuel_length_le [.item (.run 0), .item (.run 1)] .repB1 getRepB1 4 k xs)

theorem eatB2_length_le (k : Nat) (xs : List SymTok) :
    (eatB2 k xs).length ≤ xs.length + 1 := by
  simpa [eatB2] using
    (eatFuel_length_le [.item (.run 0), .item (.run 1), .item (.run 1)] .rep2 getRep2 4 k xs)

theorem eatB12R_length_le (k : Nat) (xs : List SymTok) :
    (eatB12R k xs).length ≤ xs.length + 1 := by
  simpa [eatB12R] using
    (eatFuel_length_le [.item (.run 0), .item (.run 1), .item (.run 0), .item (.run 1), .item (.run 1)]
      .rep12 getRep12 4 k xs)

def tokNumSum : SymTok → Nat
  | .item .zero => 0
  | .item (.run d) => d
  | .repB1 k => k
  | .rep2 p => p
  | .rep12 m => m

theorem tokNumSum_eq_tokFieldMax (t : SymTok) : tokNumSum t = tokFieldMax t := by
  cases t with
  | item x => cases x <;> rfl
  | repB1 k => rfl
  | rep2 p => rfl
  | rep12 m => rfl

def listNumSum : List SymTok → Nat
  | [] => 0
  | t :: xs => tokNumSum t + listNumSum xs

theorem listNumSum_append (xs ys : List SymTok) :
    listNumSum (xs ++ ys) = listNumSum xs + listNumSum ys := by
  induction xs with
  | nil => simp [listNumSum]
  | cons t xs ih => simp [listNumSum, ih, Nat.add_assoc]

theorem listFieldMax_le_listNumSum (xs : List SymTok) :
    listFieldMax xs ≤ listNumSum xs := by
  induction xs with
  | nil => simp [listFieldMax, listNumSum]
  | cons t xs ih =>
    rw [listFieldMax_cons, listNumSum]
    rw [tokNumSum_eq_tokFieldMax t]
    simp only [Nat.max_le]
    constructor <;> omega

theorem bumpSymR_num_sum_le (xs : List SymTok) :
    listNumSum (bumpSymR xs) ≤ listNumSum xs + 3 := by
  induction xs with
  | nil => simp [bumpSymR, listNumSum, tokNumSum]
  | cons t xs ih =>
    cases t with
    | item x => cases x <;> simp [bumpSymR, listNumSum, tokNumSum] <;> omega
    | repB1 k =>
      cases k with
      | zero => simpa [bumpSymR, listNumSum, tokNumSum] using Nat.le_trans ih (by omega)
      | succ k =>
        cases k with
        | zero => simp [bumpSymR, listNumSum, tokNumSum] <;> omega
        | succ k => simp [bumpSymR, listNumSum, tokNumSum, strictNat_eq] <;> omega
    | rep2 p =>
      cases p with
      | zero => simpa [bumpSymR, listNumSum, tokNumSum] using Nat.le_trans ih (by omega)
      | succ p => simp [bumpSymR, listNumSum, tokNumSum, strictNat_eq] <;> omega
    | rep12 m =>
      cases m with
      | zero => simpa [bumpSymR, listNumSum, tokNumSum] using Nat.le_trans ih (by omega)
      | succ m => simp [bumpSymR, listNumSum, tokNumSum, strictNat_eq] <;> omega

theorem eatStep_num_sum_le (blk : List SymTok) (getRep : SymTok → Option Nat)
    (hblk : 1 ≤ listNumSum blk)
    (hget : ∀ x k2, getRep x = some k2 → tokNumSum x = k2)
    (k k' : Nat) (xs rest : List SymTok)
    (h : eatStep blk getRep k xs = some (k', rest)) :
    k' + listNumSum rest ≤ k + listNumSum xs := by
  cases xs with
  | nil => simp [eatStep] at h
  | cons x xs1 =>
    unfold eatStep at h
    cases hg : getRep x with
    | some k2 =>
      simp [hg] at h
      rcases h with ⟨rfl, rfl⟩
      simp [listNumSum, hget x k2 hg]
      omega
    | none =>
      cases hs : stripPrefixSym blk (x :: xs1) with
      | none => simp [hg, hs] at h
      | some rest2 =>
        simp [hg, hs] at h
        rcases h with ⟨rfl, rfl⟩
        have hprefix := stripPrefixSym_some blk (x :: xs1) rest2 hs
        rw [hprefix, listNumSum_append]
        omega

theorem eatFuel_num_sum_le (blk : List SymTok) (mkRep : Nat → SymTok)
    (getRep : SymTok → Option Nat)
    (hblk : 1 ≤ listNumSum blk)
    (hMk : ∀ k, tokNumSum (mkRep k) = k)
    (hget : ∀ x k2, getRep x = some k2 → tokNumSum x = k2)
    (fuel k : Nat) (xs : List SymTok) :
    listNumSum (eatFuel blk mkRep getRep fuel k xs) ≤ k + listNumSum xs := by
  induction fuel generalizing k xs with
  | zero => simp [eatFuel, listNumSum, hMk]
  | succ fuel ih =>
    cases hs : eatStep blk getRep k xs with
    | none => simp [eatFuel, hs, listNumSum, hMk]
    | some pair =>
      rcases pair with ⟨k', rest⟩
      have hstep := eatStep_num_sum_le blk getRep hblk hget k k' xs rest hs
      have hrec := ih k' rest
      simp [eatFuel, hs, strictNat_eq]
      exact Nat.le_trans hrec hstep

theorem getRepB1_num (x : SymTok) (k : Nat) (h : getRepB1 x = some k) :
    tokNumSum x = k := by
  cases x with
  | item x => simp [getRepB1] at h
  | repB1 n => simp [getRepB1] at h; simpa [tokNumSum] using h
  | rep2 p => simp [getRepB1] at h
  | rep12 m => simp [getRepB1] at h

theorem getRep2_num (x : SymTok) (k : Nat) (h : getRep2 x = some k) :
    tokNumSum x = k := by
  cases x with
  | item x => simp [getRep2] at h
  | repB1 n => simp [getRep2] at h
  | rep2 p => simp [getRep2] at h; simpa [tokNumSum] using h
  | rep12 m => simp [getRep2] at h

theorem getRep12_num (x : SymTok) (k : Nat) (h : getRep12 x = some k) :
    tokNumSum x = k := by
  cases x with
  | item x => simp [getRep12] at h
  | repB1 n => simp [getRep12] at h
  | rep2 p => simp [getRep12] at h
  | rep12 m => simp [getRep12] at h; simpa [tokNumSum] using h

theorem eatB1_num_sum_le (k : Nat) (xs : List SymTok) :
    listNumSum (eatB1 k xs) ≤ k + listNumSum xs := by
  simpa [eatB1] using
    (eatFuel_num_sum_le [.item (.run 0), .item (.run 1)] .repB1 getRepB1
      (by simp [listNumSum, tokNumSum]) (by intro n; simp [tokNumSum])
      getRepB1_num 4 k xs)

theorem eatB2_num_sum_le (k : Nat) (xs : List SymTok) :
    listNumSum (eatB2 k xs) ≤ k + listNumSum xs := by
  simpa [eatB2] using
    (eatFuel_num_sum_le [.item (.run 0), .item (.run 1), .item (.run 1)] .rep2 getRep2
      (by simp [listNumSum, tokNumSum]) (by intro n; simp [tokNumSum])
      getRep2_num 4 k xs)

theorem eatB12R_num_sum_le (k : Nat) (xs : List SymTok) :
    listNumSum (eatB12R k xs) ≤ k + listNumSum xs := by
  simpa [eatB12R] using
    (eatFuel_num_sum_le [.item (.run 0), .item (.run 1), .item (.run 0), .item (.run 1), .item (.run 1)]
      .rep12 getRep12 (by simp [listNumSum, tokNumSum]) (by intro n; simp [tokNumSum])
      getRep12_num 4 k xs)

theorem peelTok_num_sum_le (t : SymTok) (xs : List SymTok) :
    listNumSum (peelTok t xs) ≤ tokNumSum t + listNumSum xs + 2 := by
  cases t with
  | item x => simp [peelTok, tokNumSum, listNumSum]
  | repB1 k =>
    cases k with
    | zero => simp [peelTok, tokNumSum, listNumSum]
    | succ k =>
      cases k with
      | zero => simp [peelTok, tokNumSum, listNumSum]
      | succ k => simp [peelTok, tokNumSum, listNumSum, strictNat_eq] <;> omega
  | rep2 p =>
    cases p with
    | zero => simp [peelTok, tokNumSum, listNumSum]
    | succ p =>
      cases p with
      | zero => simp [peelTok, tokNumSum, listNumSum] <;> omega
      | succ p => simp [peelTok, tokNumSum, listNumSum, strictNat_eq] <;> omega
  | rep12 m =>
    cases m with
    | zero => simp [peelTok, tokNumSum, listNumSum]
    | succ m =>
      cases m with
      | zero => simp [peelTok, tokNumSum, listNumSum] <;> omega
      | succ m => simp [peelTok, tokNumSum, listNumSum, strictNat_eq] <;> omega

def symStateNumSum (s : SymMode × List SymTok × List SymTok) : Nat :=
  listNumSum s.2.1 + listNumSum s.2.2

theorem stepElemBB_num_sum_le (L R : List SymTok) :
    symStateNumSum (stepElemBB L R) ≤ listNumSum L + listNumSum R + 3 := by
  have hR := bumpSymR_num_sum_le R
  cases L with
  | nil =>
    simp [stepElemBB, strictList_eq, symStateNumSum, listNumSum]
    omega
  | cons t L1 =>
    cases t with
    | item x =>
      cases x with
      | zero => simp [stepElemBB, strictList_eq, symStateNumSum, listNumSum]; omega
      | run d =>
        cases d with
        | zero => simp [stepElemBB, symStateNumSum, listNumSum, tokNumSum]
        | succ d =>
          cases d with
          | zero => simp [stepElemBB, strictList_eq, symStateNumSum, listNumSum, tokNumSum]; omega
          | succ d =>
            cases d with
            | zero => simp [stepElemBB, strictList_eq, symStateNumSum, listNumSum, tokNumSum]; omega
            | succ d =>
              cases d with
              | zero => simp [stepElemBB, strictList_eq, symStateNumSum, listNumSum, tokNumSum]; omega
              | succ d => simp [stepElemBB, strictList_eq, strictNat_eq, symStateNumSum, listNumSum, tokNumSum]; omega
    | repB1 k => simp [stepElemBB, symStateNumSum, listNumSum, tokNumSum]
    | rep2 p => simp [stepElemBB, symStateNumSum, listNumSum, tokNumSum]
    | rep12 m => simp [stepElemBB, symStateNumSum, listNumSum, tokNumSum]

/-!
## BB-sweep combined field potential

The measure below is the sum of symbolic token count and numeric-field sum.
The induction charges a run-1 bump by at most eight units, while repeat-token
eats transfer the consumed repeat field to the returned suffix. Failed repeat
matches are terminal and are covered by the fixed +18 allowance.
-/

theorem peelTok_length_le (t : SymTok) (xs : List SymTok) :
    (peelTok t xs).length ≤ xs.length + 6 := by
  cases t with
  | item x => simp [peelTok]
  | repB1 k =>
    cases k with
    | zero => simp [peelTok]
    | succ k =>
      cases k with
      | zero => simp [peelTok]
      | succ k => simp [peelTok, strictNat_eq] <;> omega
  | rep2 p =>
    cases p with
    | zero => simp [peelTok]
    | succ p =>
      cases p with
      | zero => simp [peelTok]
      | succ p => simp [peelTok, strictNat_eq] <;> omega
  | rep12 m =>
    cases m with
    | zero => simp [peelTok]
    | succ m =>
      cases m with
      | zero => simp [peelTok]
      | succ m => simp [peelTok, strictNat_eq] <;> omega

theorem stepElemBB_length_le (L R : List SymTok) :
    stateTokenCount (stepElemBB L R) ≤ L.length + R.length + 7 := by
  have hR := bumpSymR_length_le R
  cases L with
  | nil =>
    simp [stepElemBB, stateTokenCount, strictList_eq]
    omega
  | cons t L1 =>
    cases t with
    | item x =>
      cases x with
      | zero =>
        simp [stepElemBB, stateTokenCount, strictList_eq]
        omega
      | run d =>
        cases d with
        | zero =>
          simp [stepElemBB, stateTokenCount, strictList_eq]
          omega
        | succ d =>
          cases d with
          | zero =>
            simp [stepElemBB, stateTokenCount, strictList_eq]
            omega
          | succ d =>
            cases d with
            | zero =>
              simp [stepElemBB, stateTokenCount, strictList_eq]
              omega
            | succ d =>
              cases d with
              | zero =>
                simp [stepElemBB, stateTokenCount, strictList_eq]
                omega
              | succ d =>
                simp [stepElemBB, stateTokenCount, strictList_eq, strictNat_eq]
                omega
    | repB1 k => simp [stepElemBB, stateTokenCount]
    | rep2 p => simp [stepElemBB, stateTokenCount]
    | rep12 m => simp [stepElemBB, stateTokenCount]

def symStateWeight (s : SymState) : Nat :=
  stateTokenCount s + symStateNumSum s

end BusyBeaver.SymRunAudit
