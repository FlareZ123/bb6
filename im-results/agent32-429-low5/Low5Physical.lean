import Low5Delta
import JPhysicalPrefix
import BB429DeltaPhysicalBridge
import Lean.Elab.Tactic.Omega

set_option maxHeartbeats 30000000
set_option maxRecDepth 8192

namespace BB429Low5Physical
open BB6Coverage BB6Bubble BB429PhysicalFrontier BB429JPhysical
open BB429OddExcursion BB429SourceE1Return BB429Low5Delta
open BB429FinishScanEDelta BB429PhysicalBridge

private theorem stage5_tape_character (v : Nat) (x : Int) :
    negFill (jTape (v+3) (2*v+1)) (v+1) x =
      decide ((-2*(v:Int)-12 ≤ x ∧ x ≤ 2*(v:Int)+2 ∧
        x ≠ -2*(v:Int)-4 ∧ x ≠ -2*(v:Int)-6) ∨ x=2*(v:Int)+4) := by
  have hp : (negFillTest (v+1) x ∨ jMark (v+3) (2*v+1) x) ↔
      ((-2*(v:Int)-12 ≤ x ∧ x ≤ 2*(v:Int)+2 ∧
        x ≠ -2*(v:Int)-4 ∧ x ≠ -2*(v:Int)-6) ∨ x=2*(v:Int)+4) := by
    unfold negFillTest jMark jHole
    omega
  unfold negFill jTape
  by_cases hfill : negFillTest (v+1) x
  · simp [hfill, hp.mp (Or.inl hfill)]
  · by_cases hJ : jMark (v+3) (2*v+1) x
    · simp [hfill,hJ,hp.mp (Or.inr hJ)]
    · have hn : ¬((-2*(v:Int)-12 ≤ x ∧ x ≤ 2*(v:Int)+2 ∧
          x ≠ -2*(v:Int)-4 ∧ x ≠ -2*(v:Int)-6) ∨ x=2*(v:Int)+4) := by
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
    ([true,false,true,false] ++ ones 6).getD k false =
      decide (k < 10 ∧ k ≠ 1 ∧ k ≠ 3) := by
  cases k with
  | zero => rfl
  | succ k =>
    cases k with
    | zero => rfl
    | succ k =>
      cases k with
      | zero => rfl
      | succ k =>
        cases k with
        | zero => rfl
        | succ k =>
          change (ones 6).getD k false =
              decide (k+4 < 10 ∧ k+4 ≠ 1 ∧ k+4 ≠ 3)
          rw [ones_getD]
          have hp : (k < 6) ↔
              (k+4 < 10 ∧ k+4 ≠ 1 ∧ k+4 ≠ 3) := by omega
          simp [hp]

private theorem stage5_left_char (v j : Nat) :
    (stage5 v).left.getD j false =
      decide (j < 4*v+14 ∧ j ≠ 4*v+5 ∧ j ≠ 4*v+7) := by
  change (ones (4*v+4) ++ ([true,false,true,false] ++ ones 6)).getD j false = _
  rw [getD_append]
  have hlen : (ones (4*v+4)).length = 4*v+4 := by simp [ones]
  rw [hlen]
  by_cases hj : j < 4*v+4
  · rw [if_pos hj,ones_getD]
    have hgoal : (j < 4*v+14 ∧ j ≠ 4*v+5 ∧ j ≠ 4*v+7) := by omega
    simp [hj,hgoal]
  · rw [if_neg hj,tail_getD]
    have hgoal : ((j-(4*v+4) < 10 ∧
          j-(4*v+4) ≠ 1 ∧ j-(4*v+4) ≠ 3) ↔
          (j < 4*v+14 ∧ j ≠ 4*v+5 ∧ j ≠ 4*v+7)) := by omega
    simp [hgoal]

private theorem stage5_right_char (j : Nat) :
    ([false,true] : List Bool).getD j false = decide (j=1) := by
  cases j with
  | zero => rfl
  | succ j => cases j <;> rfl

/-- Exact support, including both infinite blank tails, after v+1 bubble repairs. -/
theorem stage5_tape_rep (v : Nat) :
    negFill (jTape (v+3) (2*v+1)) (v+1) (2*(v:Int)+2) = true ∧
    (∀ j : Nat,
      negFill (jTape (v+3) (2*v+1)) (v+1) ((2*(v:Int)+2)-((j:Int)+1)) =
        (stage5 v).left.getD j false) ∧
    (∀ j : Nat,
      negFill (jTape (v+3) (2*v+1)) (v+1) ((2*(v:Int)+2)+((j:Int)+1)) =
        (stage5 v).right.getD j false) := by
  constructor
  · rw [stage5_tape_character]
    have h : (-2*(v:Int)-12 ≤ 2*(v:Int)+2 ∧
        2*(v:Int)+2 ≤ 2*(v:Int)+2 ∧
        2*(v:Int)+2 ≠ -2*(v:Int)-4 ∧ 2*(v:Int)+2 ≠ -2*(v:Int)-6) := by omega
    simp [h]
  constructor
  · intro j
    rw [stage5_tape_character,stage5_left_char]
    have hp : ((-2*(v:Int)-12 ≤ (2*(v:Int)+2)-((j:Int)+1) ∧
         (2*(v:Int)+2)-((j:Int)+1) ≤ 2*(v:Int)+2 ∧
         (2*(v:Int)+2)-((j:Int)+1) ≠ -2*(v:Int)-4 ∧
         (2*(v:Int)+2)-((j:Int)+1) ≠ -2*(v:Int)-6) ∨
         (2*(v:Int)+2)-((j:Int)+1)=2*(v:Int)+4) ↔
         (j<4*v+14 ∧ j ≠ 4*v+5 ∧ j ≠ 4*v+7) := by omega
    simp only [hp]
  · intro j
    change negFill (jTape (v+3) (2*v+1)) (v+1) ((2*(v:Int)+2)+((j:Int)+1)) =
      ([false,true] : List Bool).getD j false
    rw [stage5_tape_character,stage5_right_char]
    have hp : ((-2*(v:Int)-12 ≤ (2*(v:Int)+2)+((j:Int)+1) ∧
         (2*(v:Int)+2)+((j:Int)+1) ≤ 2*(v:Int)+2 ∧
         (2*(v:Int)+2)+((j:Int)+1) ≠ -2*(v:Int)-4 ∧
         (2*(v:Int)+2)+((j:Int)+1) ≠ -2*(v:Int)-6) ∨
         (2*(v:Int)+2)+((j:Int)+1)=2*(v:Int)+4) ↔
         (j=1) := by omega
    simp only [hp]

theorem stage5_represented (v : Nat) :
    Represents (stage5 v)
      {state:=A,head:=2*(v:Int)+2,
       tape:=negFill (jTape (v+3) (2*v+1)) (v+1)} := by
  obtain ⟨hc,hl,hr⟩ := stage5_tape_rep v
  exact ⟨rfl,hc,hl,hr⟩

private theorem low5_holes (v i : Nat) (hi : i < v+1) :
    jTape (v+3) (2*v+1) (-2*((i+1:Nat):Int)) = false := by
  have hj : ¬jMark (v+3) (2*v+1) (-2*((i+1:Nat):Int)) := by
    unfold jMark jHole
    omega
  change (if jMark (v+3) (2*v+1) (-2*((i+1:Nat):Int)) then true else false) = false
  exact if_neg hj

private theorem low5_odds (v : Nat) (x : Int)
    (hlo : -2*((v+1:Nat):Int)<x) (hhi : x<0) (hodd : x%2≠0) :
    jTape (v+3) (2*v+1) x = true := by
  have hj : jMark (v+3) (2*v+1) x := by
    unfold jMark jHole
    left
    omega
  simp [jTape,hj]

private theorem low5_right (v : Nat) (x : Int)
    (hlo : 0≤x) (hhi : x≤2*((v+1:Nat):Int)) :
    jTape (v+3) (2*v+1) x = true := by
  have hj : jMark (v+3) (2*v+1) x := by
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

/-- Complete original-table prepared J(v+3,2v+1) to J(6,4v+2)
    physical return, exact primitive cost and signed head position. -/
theorem low5_raw_head (v : Nat) :
    ∃ c', BB6Coverage.run target429 (4*v*v+22*v+100)
      {state:=A,head:=0,tape:=jTape (v+3) (2*v+1)} = some c' ∧
      Represents (junc 6 0 (4*v+2)) c' ∧
      c'.head = 2 - ((2*v : Nat) : Int) := by
  have hfirst : BB6Coverage.run target429
      (4*(v+1)*(v+1)+2*(v+1))
      {state:=A,head:=0,tape:=jTape (v+3) (2*v+1)} =
      some {state:=A,head:=2*(v:Int)+2,
            tape:=negFill (jTape (v+3) (2*v+1)) (v+1)} := by
    have hhead_cast : 2*((v+1:Nat):Int) = 2*(v:Int)+2 := by omega
    simpa only [hhead_cast] using
      (multi_bubble_prefix target429 (v+1) (v+1)
        (jTape (v+3) (2*v+1)) (by omega)
        (by decide) (by decide) (by decide) (by decide)
        (low5_holes v) (low5_odds v) (low5_right v))
  obtain ⟨c',hsecond,hrep,hhead⟩ :=
      BB429DeltaPhysicalBridge.source_runWithDelta_rep (12*v+94)
        (stage5 v)
        {state:=A,head:=2*(v:Int)+2,
         tape:=negFill (jTape (v+3) (2*v+1)) (v+1)}
        (stage5_represented v) (junc 6 0 (4*v+2))
        (-((4*v : Nat) : Int)) (stage5_to_junc_delta v)
  have htotal := physical_compose
      (4*(v+1)*(v+1)+2*(v+1)) (12*v+94)
      {state:=A,head:=0,tape:=jTape (v+3) (2*v+1)}
      {state:=A,head:=2*(v:Int)+2,
       tape:=negFill (jTape (v+3) (2*v+1)) (v+1)}
      c' hfirst hsecond
  have htime : (4*(v+1)*(v+1)+2*(v+1))+(12*v+94) =
      4*v*v+22*v+100 := by
    simp [Nat.add_mul, Nat.mul_add]
    omega
  have hhead' : c'.head = 2 - ((2*v:Nat):Int) := by
    have hh := hhead
    simp only at hh
    omega
  exact ⟨c', by simpa only [htime] using htotal, hrep, hhead'⟩

#print axioms stage5_tape_rep
#print axioms stage5_represented
#print axioms low5_raw_head
end BB429Low5Physical
