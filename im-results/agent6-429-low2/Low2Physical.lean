import Low2Stage
import JPhysicalPrefix
import BB429PhysicalBridge
import Lean.Elab.Tactic.Omega

set_option maxHeartbeats 30000000
set_option maxRecDepth 8192

namespace BB429Low2Physical
open BB6Coverage BB6Bubble BB429PhysicalFrontier BB429JPhysical
open BB429OddExcursion BB429SourceE1Return BB429Low2Stage
open BB429FinishScanEDelta BB429PhysicalBridge

/-- The exact tape after v of the v+1 negative-even bubble repairs. -/
private theorem stage_tape_character (v : Nat) (x : Int) :
    negFill (jTape (v+1) (2*v)) v x =
      decide ((-2*(v:Int)-8 ≤ x ∧ x ≤ 2*(v:Int)+1 ∧
        x ≠ -2*(v:Int)-2) ∨ x=2*(v:Int)+3) := by
  have hp : (negFillTest v x ∨ jMark (v+1) (2*v) x) ↔
      ((-2*(v:Int)-8 ≤ x ∧ x ≤ 2*(v:Int)+1 ∧
        x ≠ -2*(v:Int)-2) ∨ x=2*(v:Int)+3) := by
    unfold negFillTest jMark jHole
    omega
  unfold negFill jTape
  by_cases hfill : negFillTest v x
  · simp [hfill, hp.mp (Or.inl hfill)]
  · by_cases hJ : jMark (v+1) (2*v) x
    · simp [hfill,hJ,hp.mp (Or.inr hJ)]
    · have hn : ¬((-2*(v:Int)-8 ≤ x ∧ x ≤ 2*(v:Int)+1 ∧
          x ≠ -2*(v:Int)-2) ∨ x=2*(v:Int)+3) := by
        intro hh
        rcases hp.mpr hh with hz | hj
        · exact hfill hz
        · exact hJ hj
      simp [hfill,hJ,hn]

private theorem getD_append {α : Type} (xs ys : List α) (j : Nat) (d : α) :
    (xs ++ ys).getD j d =
      if j < xs.length then xs.getD j d else ys.getD (j-xs.length) d := by
  induction xs generalizing j with
  | nil => simp
  | cons a xs ih =>
    cases j with
    | zero => simp
    | succ j => simpa using ih j

private theorem ones_getD (n j : Nat) :
    (ones n).getD j false = decide (j < n) := by
  induction n generalizing j with
  | zero => simp [ones]
  | succ n ih =>
    cases j with
    | zero => simp [ones]
    | succ j => simpa [ones,List.replicate_succ] using ih j

private theorem tail_getD (k : Nat) :
    ([true,false] ++ ones 6).getD k false =
      decide (k < 8 ∧ k ≠ 1) := by
  cases k with
  | zero => rfl
  | succ k =>
    cases k with
    | zero => rfl
    | succ k =>
      change (ones 6).getD k false = decide (k+2 < 8 ∧ k+2 ≠ 1)
      rw [ones_getD]
      have h : (k<6) ↔ (k+2<8 ∧ k+2≠1) := by omega
      simp [h]

private theorem stage_left_char (v j : Nat) :
    (stage v).left.getD j false =
      decide (j < 4*v+8 ∧ j ≠ 4*v+1) := by
  change (ones (4*v) ++ ([true,false] ++ ones 6)).getD j false = _
  rw [getD_append]
  have hlen : (ones (4*v)).length = 4*v := by simp [ones]
  rw [hlen]
  by_cases hj : j < 4*v
  · rw [if_pos hj,ones_getD]
    have hgoal : (j < 4*v+8 ∧ j ≠ 4*v+1) := by omega
    simp [hj,hgoal]
  · rw [if_neg hj,tail_getD]
    have hgoal : ((j-4*v < 8 ∧ j-4*v ≠ 1) ↔
      (j < 4*v+8 ∧ j ≠ 4*v+1)) := by omega
    simp [hgoal]

private theorem stage_right_char (j : Nat) :
    ([true,false,true] : List Bool).getD j false =
      decide (j=0 ∨ j=2) := by
  cases j with
  | zero => rfl
  | succ j =>
    cases j with
    | zero => rfl
    | succ j =>
      cases j with
      | zero => rfl
      | succ j => simp

/-- Exact whole-tape identification of the v-bubble intermediate checkpoint. -/
theorem stage_tape_rep (v : Nat) :
    negFill (jTape (v+1) (2*v)) v (2*(v:Int)) = true ∧
    (∀ j : Nat,
      negFill (jTape (v+1) (2*v)) v (2*(v:Int)-((j:Int)+1)) =
        (stage v).left.getD j false) ∧
    (∀ j : Nat,
      negFill (jTape (v+1) (2*v)) v (2*(v:Int)+((j:Int)+1)) =
        (stage v).right.getD j false) := by
  constructor
  · rw [stage_tape_character]
    have h : (-2*(v:Int)-8 ≤ 2*(v:Int) ∧
        2*(v:Int) ≤ 2*(v:Int)+1 ∧
        2*(v:Int) ≠ -2*(v:Int)-2) := by omega
    simp [h]
  constructor
  · intro j
    rw [stage_tape_character,stage_left_char]
    have hp : ((-2*(v:Int)-8 ≤ 2*(v:Int)-((j:Int)+1) ∧
         2*(v:Int)-((j:Int)+1) ≤ 2*(v:Int)+1 ∧
         2*(v:Int)-((j:Int)+1) ≠ -2*(v:Int)-2) ∨
         2*(v:Int)-((j:Int)+1)=2*(v:Int)+3) ↔
         (j<4*v+8 ∧ j ≠ 4*v+1) := by omega
    simp only [hp]
  · intro j
    change negFill (jTape (v+1) (2*v)) v (2*(v:Int)+((j:Int)+1)) =
      ([true,false,true] : List Bool).getD j false
    rw [stage_tape_character,stage_right_char]
    have hp : ((-2*(v:Int)-8 ≤ 2*(v:Int)+((j:Int)+1) ∧
         2*(v:Int)+((j:Int)+1) ≤ 2*(v:Int)+1 ∧
         2*(v:Int)+((j:Int)+1) ≠ -2*(v:Int)-2) ∨
         2*(v:Int)+((j:Int)+1)=2*(v:Int)+3) ↔
         (j=0 ∨ j=2) := by omega
    simp only [hp]

theorem stage_represented (v : Nat) :
    Represents (stage v)
      {state:=A,head:=2*(v:Int),
       tape:=negFill (jTape (v+1) (2*v)) v} := by
  obtain ⟨hc,hl,hr⟩ := stage_tape_rep v
  exact ⟨rfl,hc,hl,hr⟩

private theorem low2_holes (v i : Nat) (hi : i < v) :
    jTape (v+1) (2*v) (-2*((i+1:Nat):Int)) = false := by
  have hj : ¬jMark (v+1) (2*v) (-2*((i+1:Nat):Int)) := by
    unfold jMark jHole
    omega
  change (if jMark (v+1) (2*v) (-2*((i+1:Nat):Int)) then true else false) = false
  exact if_neg hj

private theorem low2_odds (v : Nat) (x : Int)
    (hlo : -2*(v:Int)<x) (hhi : x<0) (hodd : x%2≠0) :
    jTape (v+1) (2*v) x = true := by
  have hj : jMark (v+1) (2*v) x := by
    unfold jMark jHole
    left
    omega
  simp [jTape,hj]

private theorem low2_right (v : Nat) (x : Int)
    (hlo : 0≤x) (hhi : x≤2*(v:Int)) :
    jTape (v+1) (2*v) x = true := by
  have hj : jMark (v+1) (2*v) x := by
    unfold jMark jHole
    left
    omega
  simp [jTape,hj]

private theorem physical_compose (m n : Nat) (a b c : Config)
    (h1 : BB6Coverage.run target429 m a = some b)
    (h2 : BB6Coverage.run target429 n b = some c) :
    BB6Coverage.run target429 (m+n) a = some c := by
  rw [BB6Bubble.run_add', h1]
  exact h2

/-- All-parameter original six-state full-tape low-J deficit-two return.
    The input is the canonical prepared J(v+1,2v), v>=0. No blank-origin
    reachability or nonhalting is asserted here. -/
theorem low2_raw (v : Nat) :
    ∃ c', BB6Coverage.run target429 (4*v*v+22*v+79)
      {state:=A,head:=0,tape:=jTape (v+1) (2*v)} = some c' ∧
      Represents (junc 0 0 (4*v+12)) c' := by
  have hfirst : BB6Coverage.run target429 (4*v*v+2*v)
      {state:=A,head:=0,tape:=jTape (v+1) (2*v)} =
      some {state:=A,head:=2*(v:Int),
            tape:=negFill (jTape (v+1) (2*v)) v} := by
    exact multi_bubble_prefix target429 v v
      (jTape (v+1) (2*v)) (by omega)
      (by decide) (by decide) (by decide) (by decide)
      (low2_holes v) (low2_odds v) (low2_right v)
  obtain ⟨c',hsecond,hrep⟩ := source_run_rep (20*v+79)
      (stage v)
      {state:=A,head:=2*(v:Int),
       tape:=negFill (jTape (v+1) (2*v)) v}
      (stage_represented v) (junc 0 0 (4*v+12)) (stage_to_junc v)
  refine ⟨c', ?_, hrep⟩
  have htotal := physical_compose (4*v*v+2*v) (20*v+79)
      {state:=A,head:=0,tape:=jTape (v+1) (2*v)}
      {state:=A,head:=2*(v:Int),tape:=negFill (jTape (v+1) (2*v)) v}
      c' hfirst hsecond
  have htime : (4*v*v+2*v)+(20*v+79) = 4*v*v+22*v+79 := by omega
  simpa only [htime] using htotal

#print axioms stage_tape_rep
#print axioms stage_represented
#print axioms low2_raw
end BB429Low2Physical
