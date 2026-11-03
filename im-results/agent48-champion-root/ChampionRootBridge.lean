import RootShift
import Lean.Elab.Tactic.Omega

namespace BB6Coverage.Agent48Champion

/-!
Source-authentic 6-step blank-root bridge for the published champion family.
The raw 12 entries below are the TM63 table from
ccz181078/busycoq@3f302b87f5fb933c46e97672ffbb6907f373fb6e,
verify/SOBCv5.v line 10750; the champion table is the wiki's TM1.
This file imports the unchanged original BB6Coverage infinite-tape semantics.
No assertion about the external Rocq proof is admitted as a Lean axiom.
-/

/-- Published BusyCoq TM63: 1RB---_1LC0RF_1RE0LD_0LC1RB_1RA1RE_1RE0RD. -/
def tm2 : Machine := fun (q,b) =>
 match q.val,b with
 | 0,false => some ⟨true,true,1⟩
 | 0,true  => none
 | 1,false => some ⟨true,false,2⟩
 | 1,true  => some ⟨false,true,5⟩
 | 2,false => some ⟨true,true,4⟩
 | 2,true  => some ⟨false,false,3⟩
 | 3,false => some ⟨false,false,2⟩
 | 3,true  => some ⟨true,true,1⟩
 | 4,false => some ⟨true,true,0⟩
 | 4,true  => some ⟨true,true,4⟩
 | 5,false => some ⟨true,true,4⟩
 | 5,true  => some ⟨false,true,3⟩
 | _,_ => none

/-- Exact finite-list representation of the currently written ones. -/
structure FConfig where
  state : Fin 6
  head : Int
  marked : List Int
  deriving DecidableEq, Repr

def embed (c : FConfig) : Config :=
 { state := c.state, head := c.head, tape := fun x => decide (x ∈ c.marked) }

def fMove (c : FConfig) (t : Move) : FConfig :=
 { state := t.next, head := c.head + (if t.right then 1 else -1),
   marked := if t.write then c.head :: (c.marked.filter (· != c.head))
     else c.marked.filter (· != c.head) }

private theorem embed_fMove (c : FConfig) (t : Move) :
    embed (fMove c t) = applyMove (embed c) t := by
  cases c with
  | mk q h marks =>
    cases t with
    | mk w d q' =>
      cases w <;> cases d <;>
        simp only [embed, fMove, applyMove] <;>
        apply congrArg (fun f : Int → Bool => Config.mk q' _ f) <;>
        funext x <;>
        (by_cases hx : x = h <;> simp [hx])

def fStep (m : Machine) (c : FConfig) : Option FConfig :=
 (m (c.state, decide (c.head ∈ c.marked))).map (fMove c)

def fRun (m : Machine) : Nat → FConfig → Option FConfig
 | 0, c => some c
 | n+1, c => (fRun m n c).bind (fStep m)

private theorem embed_fStep (m : Machine) (c : FConfig) :
    (fStep m c).map embed = rawStep m (embed c) := by
  simp only [fStep, rawStep, readSlot, embed, Option.map_map]
  congr 1
  funext t
  simpa only [Function.comp_def, embed] using embed_fMove c t

private theorem embed_fRun (m : Machine) (n : Nat) (c : FConfig) :
    (fRun m n c).map embed = run m n (embed c) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    simp only [fRun, run]
    rw [← ih]
    cases h : fRun m n c with
    | none => simp [h]
    | some d => simp [h, embed_fStep]

def fBlankAt (s : Fin 6) : FConfig := ⟨s,0,[]⟩

/-- Finite decidable witness; both sides are literally the same list configuration. -/
theorem join_finite :
    fRun tm2 15 (fBlankAt 4) = fRun tm2 9 (fBlankAt 0) := by decide

/-- Equality of original bi-infinite tape configurations, not only finite samples. -/
theorem join_source :
    run tm2 15 (blankAt 4) = run tm2 9 blank := by
  have h := congrArg (Option.map embed) join_finite
  rw [embed_fRun, embed_fRun] at h
  simpa [fBlankAt, embed, blankAt, blank] using h

/-- The state-E root always follows the original state-A root by six raw steps. -/
theorem all_join (n:Nat) :
    run tm2 (15+n) (blankAt 4) = run tm2 (9+n) blank := by
  rw [run_append, run_append, join_source]

theorem halts_offset (n:Nat) :
    HaltsAfterAt tm2 4 (15+n) ↔ HaltsAfter tm2 (9+n) := by
  unfold HaltsAfterAt HaltsAfter
  rw [all_join n, show 15+n+1=15+(n+1) by omega,
      show 9+n+1=9+(n+1) by omega, all_join (n+1)]

/-- Canonical champion TM1: 1RB1RA_1RC---_1LD0RF_1RA0LE_0LD1RC_1RA0RE.
The source wiki convention uses 1RZ on B1; the local Transition none
represents the halting query and preserves step-count semantics. -/
def championTable : Machine := fun (q,b) =>
 match q.val,b with
 | 0,false => some ⟨true,true,1⟩
 | 0,true  => some ⟨true,true,0⟩
 | 1,false => some ⟨true,true,2⟩
 | 1,true  => none
 | 2,false => some ⟨true,false,3⟩
 | 2,true  => some ⟨false,true,5⟩
 | 3,false => some ⟨true,true,0⟩
 | 3,true  => some ⟨false,false,4⟩
 | 4,false => some ⟨false,false,3⟩
 | 4,true  => some ⟨true,true,2⟩
 | 5,false => some ⟨true,true,0⟩
 | 5,true  => some ⟨false,true,4⟩
 | _,_ => none

def championForward (s : Fin 6) : Fin 6 :=
  match s.val with
  | 0 => 4 | 1 => 0 | 2 => 1 | 3 => 2 | 4 => 3 | _ => 5

def championBackward (s : Fin 6) : Fin 6 :=
  match s.val with
  | 0 => 1 | 1 => 2 | 2 => 3 | 3 => 4 | 4 => 0 | _ => 5

def championPerm : StatePerm where
  forward := championForward
  backward := championBackward
  leftInverse := by decide
  rightInverse := by decide

theorem championPermA : championPerm.forward 0 = 4 := by decide

/-- Literal 12-cell equality; fixes the precise root A↔E correspondence. -/
theorem champion_renamed : renameTable championPerm championTable = tm2 := by
  funext s
  rcases s with ⟨q,b⟩
  have hq : q = (0:Fin 6) ∨ q = 1 ∨ q = 2 ∨ q = 3 ∨ q = 4 ∨ q = 5 := by
    have lt := q.isLt
    omega
  rcases hq with h | h | h | h | h | h <;> subst q <;> cases b <;> decide

theorem blankAtZero : blankAt (0:Fin 6) = blank := by rfl

/-- The actual champion A-blank root has a six-step offset relative to TM63 A. -/
theorem champion_halts_offset (n:Nat) :
    HaltsAfter championTable (15+n) ↔ HaltsAfter tm2 (9+n) := by
  have hRoot : HaltsAfterAt tm2 4 (15+n) ↔ HaltsAfter championTable (15+n) := by
    simpa only [champion_renamed, championPermA, HaltsAfterAt, HaltsAfter,
      blankAtZero] using rename_haltsAt_iff championPerm championTable 0 (15+n)
  exact hRoot.symm.trans (halts_offset n)

/-- The common configuration is live after nine A-root transitions. -/
theorem tm2_nine_config :
    run tm2 9 blank = some (embed ⟨4,3,[2,0,-1,-2]⟩) := by
  have hf : fRun tm2 9 (fBlankAt 0) =
      some (⟨4,3,[2,0,-1,-2]⟩ : FConfig) := by decide
  have hr := embed_fRun tm2 9 (fBlankAt 0)
  rw [hf] at hr
  simpa [fBlankAt, embed, blank] using hr.symm

theorem tm2_nine_live : (run tm2 9 blank).isSome = true := by
  rw [tm2_nine_config]
  rfl

theorem tm2_min_halt (n : Nat) (h : HaltsAfter tm2 n) : 9 ≤ n := by
  by_cases hge : 9 ≤ n
  · exact hge
  have hle : n+1 ≤ 9 := by omega
  have hsum : 9 = n+1+(9-(n+1)) := by omega
  have hn : run tm2 9 blank = none := by
    rw [hsum]
    exact run_none_add tm2 blank (n+1) (9-(n+1)) h.2
  have hlive := tm2_nine_live
  rw [hn] at hlive
  cases hlive

theorem fBlankAt_root (s : Fin 6) : embed (fBlankAt s) = blankAt s := by
  simp [embed, fBlankAt, blankAt]

theorem champion_fifteen_live : (run championTable 15 blank).isSome = true := by
  have hf : (fRun championTable 15 (fBlankAt 0)).isSome = true := by decide
  have hrun := embed_fRun championTable 15 (fBlankAt 0)
  have hroot : (fRun championTable 15 (fBlankAt 0)).map embed =
      run championTable 15 blank := by
    rw [fBlankAt_root, blankAtZero] at hrun
    exact hrun
  rw [← hroot]
  simpa using hf

theorem champion_min_halt (n : Nat) (h : HaltsAfter championTable n) : 15 ≤ n := by
  by_cases hge : 15 ≤ n
  · exact hge
  have hle : n+1 ≤ 15 := by omega
  have hsum : 15 = n+1+(15-(n+1)) := by omega
  have hn : run championTable 15 blank = none := by
    rw [hsum]
    exact run_none_add championTable blank (n+1) (15-(n+1)) h.2
  have hlive := champion_fifteen_live
  rw [hn] at hlive
  cases hlive

/-- Root-correct global halting iff, without assuming any result about TM63. -/
theorem champion_halts_iff_tm2 :
    (∃ n, HaltsAfter championTable n) ↔ (∃ n, HaltsAfter tm2 n) := by
  constructor
  · rintro ⟨n,hn⟩
    have ge := champion_min_halt n hn
    obtain ⟨k,hk⟩ := Nat.exists_eq_add_of_le ge
    have hn' : HaltsAfter championTable (15+k) := by
      simpa only [hk] using hn
    exact ⟨9+k, (champion_halts_offset k).mp hn'⟩
  · rintro ⟨n,hn⟩
    have ge := tm2_min_halt n hn
    obtain ⟨k,hk⟩ := Nat.exists_eq_add_of_le ge
    have hn' : HaltsAfter tm2 (9+k) := by
      simpa only [hk] using hn
    exact ⟨15+k, (champion_halts_offset k).mpr hn'⟩

#print axioms join_source
#print axioms all_join
#print axioms champion_renamed
#print axioms champion_halts_offset
#print axioms champion_halts_iff_tm2
end BB6Coverage.Agent48Champion
