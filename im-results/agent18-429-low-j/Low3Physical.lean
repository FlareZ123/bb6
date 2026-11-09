import Low3Stage
import JPhysicalPrefix
import BB429PhysicalBridge
import Lean.Elab.Tactic.Omega

set_option maxHeartbeats 30000000
set_option maxRecDepth 8192

namespace BB429Low3Physical
open BB6Coverage BB6Bubble BB429PhysicalFrontier BB429JPhysical
open BB429OddExcursion BB429SourceE1Return BB429Low3Stage
open BB429FinishScanEDelta BB429PhysicalBridge

private theorem stage3_tape_character (v : Nat) (x : Int) :
    negFill (jTape (v+2) (2*v+1)) (v+1) x =
      decide ((-2*(v:Int)-10 ≤ x ∧ x ≤ 2*(v:Int)+2 ∧
        x ≠ -2*(v:Int)-4) ∨ x=2*(v:Int)+4) := by
  have hp : (negFillTest (v+1) x ∨ jMark (v+2) (2*v+1) x) ↔
      ((-2*(v:Int)-10 ≤ x ∧ x ≤ 2*(v:Int)+2 ∧
        x ≠ -2*(v:Int)-4) ∨ x=2*(v:Int)+4) := by
    unfold negFillTest jMark jHole
    omega
  unfold negFill jTape
  by_cases hfill : negFillTest (v+1) x
  · simp [hfill, hp.mp (Or.inl hfill)]
  · by_cases hJ : jMark (v+2) (2*v+1) x
    · simp [hfill,hJ,hp.mp (Or.inr hJ)]
    · have hn : ¬((-2*(v:Int)-10 ≤ x ∧ x ≤ 2*(v:Int)+2 ∧
          x ≠ -2*(v:Int)-4) ∨ x=2*(v:Int)+4) := by
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

private theorem stage3_left_char (v j : Nat) :
    (stage3 v).left.getD j false =
      decide (j < 4*v+12 ∧ j ≠ 4*v+5) := by
  change (ones (4*v+4) ++ ([true,false] ++ ones 6)).getD j false = _
  rw [getD_append]
  have hlen : (ones (4*v+4)).length = 4*v+4 := by simp [ones]
  rw [hlen]
  by_cases hj : j < 4*v+4
  · rw [if_pos hj,ones_getD]
    have hgoal : (j < 4*v+12 ∧ j ≠ 4*v+5) := by omega
    simp [hj,hgoal]
  · rw [if_neg hj,tail_getD]
    have hgoal : ((j-(4*v+4) < 8 ∧ j-(4*v+4) ≠ 1) ↔
      (j < 4*v+12 ∧ j ≠ 4*v+5)) := by omega
    simp [hgoal]

private theorem stage3_right_char (j : Nat) :
    ([false,true] : List Bool).getD j false = decide (j=1) := by
  cases j with
  | zero => rfl
  | succ j => cases j <;> rfl

/-- Identify every cell of the intermediate physical tape, including
    all cells outside the finite zipper's support. -/
theorem stage3_tape_rep (v : Nat) :
    negFill (jTape (v+2) (2*v+1)) (v+1) (2*(v:Int)+2) = true ∧
    (∀ j : Nat,
      negFill (jTape (v+2) (2*v+1)) (v+1) ((2*(v:Int)+2)-((j:Int)+1)) =
        (stage3 v).left.getD j false) ∧
    (∀ j : Nat,
      negFill (jTape (v+2) (2*v+1)) (v+1) ((2*(v:Int)+2)+((j:Int)+1)) =
        (stage3 v).right.getD j false) := by
  constructor
  · rw [stage3_tape_character]
    have h : (-2*(v:Int)-10 ≤ 2*(v:Int)+2 ∧
        2*(v:Int)+2 ≤ 2*(v:Int)+2 ∧
        2*(v:Int)+2 ≠ -2*(v:Int)-4) := by omega
    simp [h]
  constructor
  · intro j
    rw [stage3_tape_character,stage3_left_char]
    have hp : ((-2*(v:Int)-10 ≤ (2*(v:Int)+2)-((j:Int)+1) ∧
         (2*(v:Int)+2)-((j:Int)+1) ≤ 2*(v:Int)+2 ∧
         (2*(v:Int)+2)-((j:Int)+1) ≠ -2*(v:Int)-4) ∨
         (2*(v:Int)+2)-((j:Int)+1)=2*(v:Int)+4) ↔
         (j<4*v+12 ∧ j ≠ 4*v+5) := by omega
    simp only [hp]
  · intro j
    change negFill (jTape (v+2) (2*v+1)) (v+1) ((2*(v:Int)+2)+((j:Int)+1)) =
      ([false,true] : List Bool).getD j false
    rw [stage3_tape_character,stage3_right_char]
    have hp : ((-2*(v:Int)-10 ≤ (2*(v:Int)+2)+((j:Int)+1) ∧
         (2*(v:Int)+2)+((j:Int)+1) ≤ 2*(v:Int)+2 ∧
         (2*(v:Int)+2)+((j:Int)+1) ≠ -2*(v:Int)-4) ∨
         (2*(v:Int)+2)+((j:Int)+1)=2*(v:Int)+4) ↔
         (j=1) := by omega
    simp only [hp]

theorem stage3_represented (v : Nat) :
    Represents (stage3 v)
      {state:=A,head:=2*(v:Int)+2,
       tape:=negFill (jTape (v+2) (2*v+1)) (v+1)} := by
  obtain ⟨hc,hl,hr⟩ := stage3_tape_rep v
  exact ⟨rfl,hc,hl,hr⟩

private theorem low3_holes (v i : Nat) (hi : i < v+1) :
    jTape (v+2) (2*v+1) (-2*((i+1:Nat):Int)) = false := by
  have hj : ¬jMark (v+2) (2*v+1) (-2*((i+1:Nat):Int)) := by
    unfold jMark jHole
    omega
  change (if jMark (v+2) (2*v+1) (-2*((i+1:Nat):Int)) then true else false) = false
  exact if_neg hj

private theorem low3_odds (v : Nat) (x : Int)
    (hlo : -2*((v+1:Nat):Int)<x) (hhi : x<0) (hodd : x%2≠0) :
    jTape (v+2) (2*v+1) x = true := by
  have hj : jMark (v+2) (2*v+1) x := by
    unfold jMark jHole
    left
    omega
  simp [jTape,hj]

private theorem low3_right (v : Nat) (x : Int)
    (hlo : 0≤x) (hhi : x≤2*((v+1:Nat):Int)) :
    jTape (v+2) (2*v+1) x = true := by
  have hj : jMark (v+2) (2*v+1) x := by
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

/-- Uniform physical #429 return from prepared J(v+2,2v+1) after
    exactly 4v²+22v+54 successful primitive instructions. -/
theorem low3_raw (v : Nat) :
    ∃ c', BB6Coverage.run target429 (4*v*v+22*v+54)
      {state:=A,head:=0,tape:=jTape (v+2) (2*v+1)} = some c' ∧
      Represents (junc 0 0 (4*v+10)) c' := by
  have hfirst : BB6Coverage.run target429
      (4*(v+1)*(v+1)+2*(v+1))
      {state:=A,head:=0,tape:=jTape (v+2) (2*v+1)} =
      some {state:=A,head:=2*(v:Int)+2,
            tape:=negFill (jTape (v+2) (2*v+1)) (v+1)} := by
    simpa only [Nat.cast_add, Nat.cast_one, mul_add, mul_one] using
      (multi_bubble_prefix target429 (v+1) (v+1)
        (jTape (v+2) (2*v+1)) (by omega)
        (by decide) (by decide) (by decide) (by decide)
        (low3_holes v) (low3_odds v) (low3_right v))
  obtain ⟨c',hsecond,hrep⟩ := source_run_rep (12*v+48)
      (stage3 v)
      {state:=A,head:=2*(v:Int)+2,
       tape:=negFill (jTape (v+2) (2*v+1)) (v+1)}
      (stage3_represented v) (junc 0 0 (4*v+10)) (stage3_to_junc v)
  refine ⟨c', ?_, hrep⟩
  have htotal := physical_compose
      (4*(v+1)*(v+1)+2*(v+1)) (12*v+48)
      {state:=A,head:=0,tape:=jTape (v+2) (2*v+1)}
      {state:=A,head:=2*(v:Int)+2,
       tape:=negFill (jTape (v+2) (2*v+1)) (v+1)}
      c' hfirst hsecond
  have htime : (4*(v+1)*(v+1)+2*(v+1))+(12*v+48) =
      4*v*v+22*v+54 := by
    simp [Nat.add_mul, Nat.mul_add]
    omega
  simpa only [htime] using htotal

#print axioms stage3_tape_rep
#print axioms stage3_represented
#print axioms low3_raw
end BB429Low3Physical
