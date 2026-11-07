import JFirstBranch
import CryptidsTapeAdapter
import BusyBeaver.BB6.M_1RB0LF_1RC1RA_0RD0RB_1LEHHH_0LA1LE_1RD1LA
import Lean.Elab.Tactic.Omega

open BusyBeaver.M_1RB0LF_1RC1RA_0RD0RB_1LEHHH_0LA1LE_1RD1LA
open BB429JPhysical
open BB429JFirstBranch
open BB429PhysicalFrontier

namespace BB429JSourceBridge

abbrev Bit := Fin 2

def jPow01 (u : Nat) : List Bit :=
  (List.replicate u ([0, 1] : List Bit)).flatten

def jPow1 (w : Nat) : List Bit :=
  (List.replicate w ([1] : List Bit)).flatten

def jLeftList (u : Nat) : List Bit :=
  [1] ++ jPow01 u ++ [1, 1, 1, 1, 1]

def jRightList (w : Nat) : List Bit :=
  [1] ++ jPow1 w ++ [0, 1]

theorem getD_append {α : Type} (xs ys : List α) (n : Nat) (d : α) :
    (xs ++ ys).getD n d =
      if n < xs.length then xs.getD n d else ys.getD (n - xs.length) d := by
  induction xs generalizing n with
  | nil => simp
  | cons x xs ih =>
    cases n with
    | zero => simp
    | succ n =>
      simp only [List.cons_append, List.getD_cons_succ, List.length_cons]
      rw [ih]
      simp [Nat.succ_lt_succ_iff, Nat.succ_sub_succ_eq_sub]

theorem jPow01_eq_pow (u : Nat) : jPow01 u = ([0, 1] : List Bit) ^ u := rfl

theorem jPow01_succ (u : Nat) : jPow01 (u + 1) = [0, 1] ++ jPow01 u := rfl

theorem jPow1_eq_pow (u : Nat) : jPow1 u = ([1] : List Bit) ^ u := rfl

theorem jPow1_succ (u : Nat) : jPow1 (u + 1) = [1] ++ jPow1 u := rfl

theorem jPow01_length (u : Nat) : (jPow01 u).length = 2 * u := by
  induction u with
  | zero => rfl
  | succ u ih =>
    rw [jPow01_succ]
    simp [ih]
    omega

theorem jPow01_getD (u n : Nat) :
    (jPow01 u).getD n 0 =
      if n < 2 * u then (if n % 2 = 0 then 0 else 1) else 0 := by
  induction u generalizing n with
  | zero => simp [jPow01]
  | succ u ih =>
    rw [jPow01_succ, getD_append]
    cases n with
    | zero => simp
    | succ n =>
      cases n with
      | zero =>
        simp
        omega
      | succ n =>
        simp only [List.length_cons, List.length_nil]
        have hlt0 : ¬ n + 2 < 2 := by omega
        simp only [if_neg hlt0, Nat.add_sub_cancel_left]
        rw [ih]
        have hlt : n + 2 < 2 * (u + 1) ↔ n < 2 * u := by omega
        have hmod : (n + 2) % 2 = n % 2 := by omega
        simp [hlt, hmod]

theorem jPow1_getD (u n : Nat) :
    (jPow1 u).getD n 0 = (if n < u then 1 else 0) := by
  induction u generalizing n with
  | zero => simp [jPow1]
  | succ u ih =>
    rw [jPow1_succ]
    cases n with
    | zero => simp
    | succ n =>
      simp only [List.cons_append, List.getD_cons_succ]
      change (jPow1 u).getD n 0 = (if n + 1 < u + 1 then 1 else 0)
      rw [ih]
      have hlt : n + 1 < u + 1 ↔ n < u := by omega
      simp [hlt]

theorem jLeftList_getD_nested (u n : Nat) :
    (jLeftList u).getD n 0 =
      if n = 0 then 1 else if n ≤ 2 * u then (if n % 2 = 0 then 1 else 0)
      else if n ≤ 2 * u + 5 then 1 else 0 := by
  unfold jLeftList
  cases n with
  | zero => simp
  | succ n =>
    simp only [List.cons_append, List.getD_cons_succ]
    rw [getD_append]
    simp only [List.nil_append]
    have hlen : (jPow01 u).length = 2 * u := jPow01_length u
    rw [hlen]
    by_cases hn : n < 2 * u
    · rw [jPow01_getD]
      simp [hn]
      by_cases he : n % 2 = 0
      · have hnext : (n + 1) % 2 = 1 := by omega
        simp [he, hnext]
      · have hodd : n % 2 = 1 := by omega
        have hnext : (n + 1) % 2 = 0 := by omega
        simp [he, hodd, hnext]
    · have hval : ([1, 1, 1, 1, 1] : List Bit).getD (n - 2 * u) 0 =
          (if n - 2 * u < 5 then 1 else 0) := by
        by_cases hk : n - 2 * u < 5
        · have hcases : n - 2 * u = 0 ∨ n - 2 * u = 1 ∨ n - 2 * u = 2 ∨
              n - 2 * u = 3 ∨ n - 2 * u = 4 := by omega
          rcases hcases with h | h | h | h | h <;> simp [h, hk]
        · have hge : 5 ≤ n - 2 * u := by omega
          simp [List.getD, hge]
      have hge : 2 * u ≤ n := Nat.le_of_not_gt hn
      rw [hval]
      have hbound : n - 2 * u < 5 ↔ n ≤ 2 * u + 4 := by omega
      by_cases h : n - 2 * u < 5 <;> simp [h, hbound]

theorem jLeftList_getD (u n : Nat) :
    (jLeftList u).getD n 0 =
      (if n ≤ 2 * u + 5 ∧ (2 * u ≤ n ∨ n % 2 = 0) then 1 else 0) := by
  rw [jLeftList_getD_nested]
  by_cases h0 : n = 0
  · simp [h0]
  · by_cases hle : n ≤ 2 * u
    · by_cases he : n % 2 = 0
      · simp [h0, hle, he]
        omega
      · have hodd : n % 2 = 1 := by omega
        simp [h0, hle, he, hodd]
        omega
    · by_cases hbound : n ≤ 2 * u + 5
      · simp [h0, hle, hbound]
        omega
      · simp [h0, hle, hbound]

theorem jPow1_length (u : Nat) : (jPow1 u).length = u := by
  induction u with
  | zero => rfl
  | succ u ih =>
    rw [jPow1_succ]
    simp [ih]

theorem jRightList_getD (w n : Nat) :
    (jRightList w).getD n 0 = (if n ≤ w ∨ n = w + 2 then 1 else 0) := by
  unfold jRightList
  cases n with
  | zero => simp
  | succ n =>
    simp only [List.cons_append, List.getD_cons_succ]
    rw [getD_append]
    simp only [List.nil_append]
    rw [jPow1_length]
    by_cases hn : n < w
    · rw [jPow1_getD]
      simp [hn]
    · cases hdiff : n - w with
      | zero =>
        have heq : n = w := by omega
        simp [hn, hdiff, heq]
      | succ k =>
        cases k with
        | zero =>
          have heq : n + 1 = w + 2 := by omega
          simp [hn, hdiff, heq]
        | succ k =>
          have hge : w ≤ n := Nat.le_of_not_gt hn
          have hsum : w + (n - w) = n := Nat.add_sub_of_le hge
          rw [hdiff] at hsum
          have hne' : n ≠ w + 1 := by
            intro heq
            rw [heq] at hsum
            omega
          simp [hn, hdiff]
          exact hne'

@[simp] theorem jMark_zero (u w : Nat) : jMark u w 0 := by
  unfold jMark jHole
  left
  constructor
  · omega
  · constructor
    · omega
    · intro h
      rcases h with ⟨_, hneg, _⟩
      omega

theorem jMark_pos (u w n : Nat) :
    jMark u w ((n : Int) + 1) ↔ n ≤ w ∨ n = w + 2 := by
  unfold jMark jHole
  constructor
  · intro h
    rcases h with ⟨hlo, hhi, hn⟩ | heq
    · left
      omega
    · right
      omega
  · intro h
    rcases h with h | h
    · left
      constructor
      · omega
      · constructor
        · omega
        · intro hh
          rcases hh with ⟨_, hneg, _⟩
          omega
    · right
      omega

theorem jMark_neg (u w n : Nat) :
    jMark u w (-(n : Int) - 1) ↔ n ≤ 2 * u + 5 ∧ (2 * u ≤ n ∨ n % 2 = 0) := by
  unfold jMark jHole
  constructor
  · intro h
    rcases h with ⟨hlo, hhi, hn⟩ | heq
    · constructor
      · omega
      · by_cases hlt : n < 2 * u
        · right
          have hparity : n % 2 = 0 ∨ n % 2 = 1 := by omega
          rcases hparity with h0 | h1
          · exact h0
          · exfalso
            apply hn
            constructor
            · omega
            · constructor
              · omega
              · omega
        · left
          omega
    · exfalso
      omega
  · intro h
    rcases h with ⟨hbound, hcase⟩
    left
    constructor
    · omega
    · constructor
      · omega
      · intro hh
        rcases hh with ⟨hlo, hneg, hmod⟩
        rcases hcase with hlarge | heven
        · omega
        · have hparity : n % 2 = 1 := by omega
          omega

theorem jTape_zero (u w : Nat) : jTape u w 0 = true := by
  simp [jTape, jMark_zero]

theorem jTape_pos (u w n : Nat) :
    jTape u w ((n : Int) + 1) =
      (if n ≤ w ∨ n = w + 2 then true else false) := by
  unfold jTape
  by_cases h : jMark u w ((n : Int) + 1)
  · have h' : n ≤ w ∨ n = w + 2 := (jMark_pos u w n).mp h
    simp [h, h']
  · have h' : ¬ (n ≤ w ∨ n = w + 2) := by
      intro hh
      exact h ((jMark_pos u w n).mpr hh)
    simp [h, h']

theorem jTape_neg (u w n : Nat) :
    jTape u w (-(n : Int) - 1) =
      (if n ≤ 2 * u + 5 ∧ (2 * u ≤ n ∨ n % 2 = 0) then true else false) := by
  unfold jTape
  by_cases h : jMark u w (-(n : Int) - 1)
  · have h' : n ≤ 2 * u + 5 ∧ (2 * u ≤ n ∨ n % 2 = 0) := (jMark_neg u w n).mp h
    simp [h, h']
  · have h' : ¬ (n ≤ 2 * u + 5 ∧ (2 * u ≤ n ∨ n % 2 = 0)) := by
      intro hh
      exact h ((jMark_neg u w n).mpr hh)
    simp [h, h']

@[simp] theorem listBlank_nth_mk (l : List Bit) (n : Nat) :
    (ConjectureMachines.ListBlank.mk l).nth n = l.getD n 0 := by
  induction n generalizing l with
  | zero =>
    cases l with
    | nil => simp [ConjectureMachines.ListBlank.nth_zero,
        ConjectureMachines.ListBlank.head_mk]
    | cons a l => simp [ConjectureMachines.ListBlank.nth_zero,
        ConjectureMachines.ListBlank.head_mk]
  | succ n ih =>
    rw [ConjectureMachines.ListBlank.nth_succ,
      ConjectureMachines.ListBlank.tail_mk]
    rw [ih]
    cases l with
    | nil => simp
    | cons a l => simp [List.getD]

def sourceJCfg (u w : Nat) : ConjectureMachines.Cfg 6 2 :=
  ⟨0, ⟨1,
    ConjectureMachines.ListBlank.mk (jLeftList u),
    ConjectureMachines.ListBlank.mk (jRightList w)⟩⟩

theorem sourceListBlank_toTuring_mk (l : List Bit) :
    (ConjectureMachines.ListBlank.mk l).toTuring = Turing.ListBlank.mk l := rfl

theorem sourceJCfg_toBB (u w : Nat) :
    (sourceJCfg u w).toBB = highLevelEncode (.J u w) := by
  have hdefault : (default : Turing.ListBlank Bit) = Turing.ListBlank.mk [] := rfl
  have hpow0 : ([0, 1] : List Bit) ^ 0 = [] := by decide
  dsimp only [sourceJCfg, ConjectureMachines.Cfg.toBB,
    ConjectureMachines.Tape.toTuring]
  simp only [sourceListBlank_toTuring_mk]
  dsimp only [highLevelEncode, toState, encode, BusyBeaver.Cfg.headRight]
  simp only [jLeftList, jRightList, jPow01_eq_pow, jPow1_eq_pow,
    Turing.ListBlank.append_mk, Turing.ListBlank.head_mk,
    Turing.ListBlank.tail_mk, Turing.ListBlank.head_cons,
    BusyBeaver.SixState.A, hdefault, List.append_assoc, List.append_nil,
    List.nil_append, List.cons_append, hpow0,
    List.headI_cons, List.tail_cons]

private def sourceBit (a : Bit) : Bool := a.val == 1

def sourceTapeToRelative (t : ConjectureMachines.Tape Bit) : BB6.Bridge.Tape :=
  ⟨sourceBit t.head,
    fun n => sourceBit (t.left.nth n),
    fun n => sourceBit (t.right.nth n)⟩

def sourceJPosition (u w : Nat) (head : Int) : BB6.ConjectureBridge.Positioned :=
  ⟨sourceJCfg u w, head⟩

theorem sourceJPosition_toRelative (u w : Nat) (head : Int) :
    BB6.ConjectureBridge.toRelative (sourceJPosition u w head) =
      ⟨0, head, sourceTapeToRelative (sourceJCfg u w).tape⟩ := rfl

@[simp] theorem jTapeAt_zero (u w : Nat) : jTapeAt u w 0 = jTape u w := by
  funext x
  simp [jTapeAt]

theorem sourceJPosition_toAbsolute (u w : Nat) (head : Int) :
    BB6.Bridge.toAbsolute (BB6.ConjectureBridge.toRelative (sourceJPosition u w head)) =
      { state := BB6Bubble.A, head := head, tape := jTapeAt u w head } := by
  rw [sourceJPosition_toRelative]
  apply BB429JFirstBranch.config_ext
  · apply Fin.ext
    simp [BB6.Bridge.toAbsolute, BB6Bubble.A]
  · rfl
  · funext x
    cases hix : x - head with
    | ofNat n =>
      cases n with
      | zero =>
        simp [hix, BB6.Bridge.toAbsolute, BB6.Bridge.symbol, sourceTapeToRelative,
          sourceBit, sourceJCfg, jTapeAt, jTape_zero]
      | succ n =>
        simp only [hix, BB6.Bridge.toAbsolute, BB6.Bridge.symbol, sourceTapeToRelative,
          sourceBit, sourceJCfg, listBlank_nth_mk]
        rw [jTapeAt, hix]
        have hpos : Int.ofNat (n + 1) = (n : Int) + 1 := by rfl
        rw [jRightList_getD, hpos, jTape_pos]
        by_cases h : n ≤ w ∨ n = w + 2 <;> simp [h]
    | negSucc n =>
      simp only [hix, BB6.Bridge.toAbsolute, BB6.Bridge.symbol, sourceTapeToRelative,
        sourceBit, sourceJCfg, listBlank_nth_mk]
      rw [jTapeAt, hix]
      have hneg : Int.negSucc n = -(n : Int) - 1 := by
        rw [Int.negSucc_eq]
        omega
      rw [jLeftList_getD, hneg, jTape_neg]
      by_cases h : n ≤ 2 * u + 5 ∧ (2 * u ≤ n ∨ n % 2 = 0) <;> simp [h]

theorem toAgent8_machine_eq :
    BB6.ConjectureBridge.toAgent8 machine = BB429PhysicalFrontier.target429 := by
  funext s
  rcases s with ⟨q, b⟩
  fin_cases q <;> cases b <;> decide

theorem source_j_first_branch_physical (u w : Nat) (hw : 2 * u + 3 ≤ w) :
    (BB6.ConjectureBridge.run machine (4 * u * u + 10 * u + 27)
      (sourceJPosition u w 0)).map
      (fun p => BB6.Bridge.toAbsolute (BB6.ConjectureBridge.toRelative p)) =
      some (BB6.Bridge.toAbsolute
        (BB6.ConjectureBridge.toRelative
          (sourceJPosition (2 * u + 3) (w - (2 * u + 3)) (2 * u + 3)))) := by
  calc
    _ = (BB6.Bridge.run (BB6.ConjectureBridge.toAgent8 machine)
          (4 * u * u + 10 * u + 27)
          (BB6.ConjectureBridge.toRelative (sourceJPosition u w 0))).map
          BB6.Bridge.toAbsolute := by
      rw [BB6.ConjectureBridge.run_toRelative]
      rw [Option.map_map]
      rfl
    _ = _ := by
      rw [← BB6.Bridge.run_absolute]
      rw [toAgent8_machine_eq, sourceJPosition_toAbsolute]
      simpa only [jTapeAt_zero] using BB429JFirstBranch.j_first_branch u w hw

theorem source_j_fatal_branch (u w : Nat) (hw : w + 1 = 2 * u) :
    BB6.ConjectureBridge.run machine (4 * u * u + 10 * u + 27)
      (sourceJPosition u w 0) = none := by
  have hmap :
      (BB6.ConjectureBridge.run machine (4 * u * u + 10 * u + 27)
        (sourceJPosition u w 0)).map
        (fun p => BB6.Bridge.toAbsolute (BB6.ConjectureBridge.toRelative p)) = none := by
    calc
      _ = (BB6.Bridge.run (BB6.ConjectureBridge.toAgent8 machine)
            (4 * u * u + 10 * u + 27)
            (BB6.ConjectureBridge.toRelative (sourceJPosition u w 0))).map
            BB6.Bridge.toAbsolute := by
        rw [BB6.ConjectureBridge.run_toRelative]
        rw [Option.map_map]
        rfl
      _ = none := by
        rw [← BB6.Bridge.run_absolute]
        rw [toAgent8_machine_eq, sourceJPosition_toAbsolute]
        simpa only [jTapeAt_zero] using BB429JFirstBranch.j_fatal_branch u w hw
  exact Option.map_eq_none_iff.mp hmap

#print axioms sourceJCfg_toBB
#print axioms sourceJPosition_toAbsolute
#print axioms source_j_first_branch_physical
#print axioms source_j_fatal_branch

end BB429JSourceBridge
