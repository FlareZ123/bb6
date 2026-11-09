import LowOddSource
import JPhysicalPrefix
import BB429DeltaPhysicalBridge
import Lean.Elab.Tactic.Omega

set_option maxHeartbeats 30000000
set_option maxRecDepth 8192

namespace BB429LowOddPhysical
open BB6Coverage BB6Bubble BB429PhysicalFrontier BB429JPhysical
open BB429OddExcursion BB429SourceE1Return BB429SourceE1Delta
open BB429FinishScanEDelta BB429PhysicalBridge BB429LowOddSource

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

private theorem tens_getD (m j : Nat) :
    (tens m).getD j false = decide (j < 2*m ∧ j%2=0) := by
  induction m generalizing j with
  | zero => simp [tens]
  | succ m ih =>
    cases j with
    | zero => rfl
    | succ j =>
      cases j with
      | zero => rfl
      | succ j =>
        change (tens m).getD j false =
          decide (j+2 < 2*(m+1) ∧ (j+2)%2=0)
        rw [ih]
        have h : (j<2*m ∧ j%2=0) ↔
          (j+2<2*(m+1) ∧ (j+2)%2=0) := by omega
        simp [h]

private theorem tens_length (m : Nat) : (tens m).length = 2*m := by
  induction m with
  | zero => rfl
  | succ m ih => simp [tens,ih]; omega

private theorem stageOdd_left_char (v n j : Nat) :
    (stageOdd v n).left.getD j false =
      decide (j < 4*v+4*n+14 ∧
        ¬(4*v+4 ≤ j ∧ j<4*v+4*n+8 ∧ j%2=1)) := by
  change (ones (4*v+4) ++ (tens (2*(n+1)) ++ ones 6)).getD j false = _
  rw [getD_append]
  have hlen : (ones (4*v+4)).length = 4*v+4 := by simp [ones]
  rw [hlen]
  by_cases hj : j<4*v+4
  · rw [if_pos hj,ones_getD]
    have hp : j < 4*v+4*n+14 ∧
      ¬(4*v+4 ≤ j ∧ j<4*v+4*n+8 ∧ j%2=1) := by omega
    simp [hj,hp]
  · rw [if_neg hj,getD_append]
    have hlen2 : (tens (2*(n+1))).length=4*n+4 := by
      rw [tens_length]
      omega
    rw [hlen2]
    by_cases ht : j-(4*v+4)<4*n+4
    · rw [if_pos ht,tens_getD]
      have hp :
          ((j-(4*v+4))<2*(2*(n+1)) ∧ ((j-(4*v+4))%2=0)) ↔
          (j < 4*v+4*n+14 ∧
            ¬(4*v+4 ≤ j ∧ j<4*v+4*n+8 ∧ j%2=1)) := by omega
      simp [hp]
    · rw [if_neg ht,ones_getD]
      have hp : j-(4*v+4)-(4*n+4)<6 ↔
          (j < 4*v+4*n+14 ∧
            ¬(4*v+4 ≤ j ∧ j<4*v+4*n+8 ∧ j%2=1)) := by omega
      simp [hp]

/-- The complete two-counter marked-set formula after v+1 bubble repairs,
    covering every cell of the bi-infinite tape. -/
private theorem stageOdd_tape_character (v n : Nat) (x : Int) :
  negFill (jTape (v+2*n+3) (2*v+1)) (v+1) x =
    decide (((-2*(v:Int)-4*(n:Int)-12 ≤ x ∧ x ≤ 2*(v:Int)+2 ∧
      ¬(-2*(v:Int)-4*(n:Int)-6 ≤ x ∧
        x ≤ -2*(v:Int)-4 ∧ x%2=0)) ∨
       x=2*(v:Int)+4)) := by
  have hp : (negFillTest (v+1) x ∨ jMark (v+2*n+3) (2*v+1) x) ↔
      (((-2*(v:Int)-4*(n:Int)-12 ≤ x ∧ x ≤ 2*(v:Int)+2 ∧
        ¬(-2*(v:Int)-4*(n:Int)-6 ≤ x ∧
          x ≤ -2*(v:Int)-4 ∧ x%2=0)) ∨
         x=2*(v:Int)+4)) := by
    unfold negFillTest jMark jHole
    omega
  unfold negFill jTape
  by_cases hfill : negFillTest (v+1) x
  · simp only [if_pos hfill]
    exact (decide_eq_true (hp.mp (Or.inl hfill))).symm
  · by_cases hj : jMark (v+2*n+3) (2*v+1) x
    · simp only [if_neg hfill, if_pos hj]
      exact (decide_eq_true (hp.mp (Or.inr hj))).symm
    · have hn : ¬(((-2*(v:Int)-4*(n:Int)-12 ≤ x ∧ x ≤ 2*(v:Int)+2 ∧
        ¬(-2*(v:Int)-4*(n:Int)-6 ≤ x ∧
          x ≤ -2*(v:Int)-4 ∧ x%2=0)) ∨
         x=2*(v:Int)+4)) := by
        intro hh
        rcases hp.mpr hh with hz | hj'
        · exact hfill hz
        · exact hj hj'
      simp only [if_neg hfill, if_neg hj]
      exact (decide_eq_false hn).symm

private theorem stageOdd_rep_left (v n j : Nat) :
  negFill (jTape (v+2*n+3) (2*v+1)) (v+1)
      ((2*(v:Int)+2)-((j:Int)+1)) =
    (stageOdd v n).left.getD j false := by
  rw [stageOdd_tape_character,stageOdd_left_char]
  apply decide_eq_decide.mpr
  omega

private theorem stageOdd_rep_right (v n j : Nat) :
  negFill (jTape (v+2*n+3) (2*v+1)) (v+1)
      ((2*(v:Int)+2)+((j:Int)+1)) =
    (stageOdd v n).right.getD j false := by
  rw [stageOdd_tape_character]
  have hr : ([false,true] : List Bool).getD j false = decide (j=1) := by
    cases j with
    | zero => rfl
    | succ j => cases j <;> rfl
  change _ = ([false,true] : List Bool).getD j false
  rw [hr]
  apply decide_eq_decide.mpr
  omega

private theorem stageOdd_rep_center (v n : Nat) :
  negFill (jTape (v+2*n+3) (2*v+1)) (v+1) (2*(v:Int)+2) = true := by
  rw [stageOdd_tape_character]
  have hp : (-2*(v:Int)-4*(n:Int)-12 ≤ 2*(v:Int)+2 ∧
      2*(v:Int)+2 ≤ 2*(v:Int)+2 ∧
      ¬(-2*(v:Int)-4*(n:Int)-6 ≤ 2*(v:Int)+2 ∧
        2*(v:Int)+2 ≤ -2*(v:Int)-4 ∧ (2*(v:Int)+2)%2=0)) := by omega
  exact decide_eq_true (Or.inl hp)

theorem stageOdd_represented (v n : Nat) :
    Represents (stageOdd v n)
      {state:=A,head:=2*(v:Int)+2,
       tape:=negFill (jTape (v+2*n+3) (2*v+1)) (v+1)} := by
  exact ⟨rfl,stageOdd_rep_center v n,stageOdd_rep_left v n,
    stageOdd_rep_right v n⟩

private theorem lowOdd_holes (v n i : Nat) (hi : i < v+1) :
    jTape (v+2*n+3) (2*v+1) (-2*((i+1:Nat):Int)) = false := by
  have hj : ¬jMark (v+2*n+3) (2*v+1)
      (-2*((i+1:Nat):Int)) := by
    unfold jMark jHole
    omega
  change (if jMark (v+2*n+3) (2*v+1)
      (-2*((i+1:Nat):Int)) then true else false) = false
  exact if_neg hj

private theorem lowOdd_odds (v n : Nat) (x : Int)
    (hlo : -2*((v+1:Nat):Int)<x) (hhi : x<0) (hodd : x%2≠0) :
    jTape (v+2*n+3) (2*v+1) x = true := by
  have hj : jMark (v+2*n+3) (2*v+1) x := by
    unfold jMark jHole
    left
    omega
  simp [jTape,hj]

private theorem lowOdd_right (v n : Nat) (x : Int)
    (hlo : 0≤x) (hhi : x≤2*((v+1:Nat):Int)) :
    jTape (v+2*n+3) (2*v+1) x = true := by
  have hj : jMark (v+2*n+3) (2*v+1) x := by
    unfold jMark jHole
    left
    omega
  simp [jTape,hj]

private theorem physical_compose (m n : Nat) (a b c : Config)
    (h1 : BB6Coverage.run target429 m a = some b)
    (h2 : BB6Coverage.run target429 n b = some c) :
    BB6Coverage.run target429 (m+n) a = some c := by
  rw [BB6Bubble.run_add',h1]
  exact h2

/-- Original table, exact physical primitive steps, all infinite tape
    cells and head translation. All odd deficits 4k+1 with k>=1. -/
theorem lowOdd_raw_head (v n : Nat) :
    ∃ c', BB6Coverage.run target429 (4*v*v+22*v+22*n+100)
      {state:=A,head:=0,tape:=jTape (v+2*n+3) (2*v+1)} = some c' ∧
      Represents (junc (2*n+6) 0 (4*v+2)) c' ∧
      c'.head = 2 - ((2*v : Nat) : Int) := by
  have hfirst : BB6Coverage.run target429
      (4*(v+1)*(v+1)+2*(v+1))
      {state:=A,head:=0,tape:=jTape (v+2*n+3) (2*v+1)} =
      some {state:=A,head:=2*(v:Int)+2,
            tape:=negFill (jTape (v+2*n+3) (2*v+1)) (v+1)} := by
    have hhead_cast : 2*((v+1:Nat):Int) = 2*(v:Int)+2 := by omega
    simpa only [hhead_cast] using
      (multi_bubble_prefix target429 (v+1) (v+1)
        (jTape (v+2*n+3) (2*v+1)) (by omega)
        (by decide) (by decide) (by decide) (by decide)
        (lowOdd_holes v n) (lowOdd_odds v n) (lowOdd_right v n))
  obtain ⟨c',hsecond,hrep,hhead⟩ :=
      BB429DeltaPhysicalBridge.source_runWithDelta_rep (12*v+22*n+94)
        (stageOdd v n)
        {state:=A,head:=2*(v:Int)+2,
         tape:=negFill (jTape (v+2*n+3) (2*v+1)) (v+1)}
        (stageOdd_represented v n) (junc (2*n+6) 0 (4*v+2))
        (-((4*v : Nat) : Int)) (stageOdd_to_junc_delta v n)
  have htotal := physical_compose
      (4*(v+1)*(v+1)+2*(v+1)) (12*v+22*n+94)
      {state:=A,head:=0,tape:=jTape (v+2*n+3) (2*v+1)}
      {state:=A,head:=2*(v:Int)+2,
       tape:=negFill (jTape (v+2*n+3) (2*v+1)) (v+1)}
      c' hfirst hsecond
  have htime : (4*(v+1)*(v+1)+2*(v+1))+(12*v+22*n+94) =
      4*v*v+22*v+22*n+100 := by
    simp [Nat.add_mul, Nat.mul_add]
    omega
  have hhead' : c'.head = 2 - ((2*v:Nat):Int) := by
    have hh := hhead
    simp only at hh
    omega
  exact ⟨c',by simpa only [htime] using htotal,hrep,hhead'⟩

#print axioms stageOdd_represented
#print axioms lowOdd_raw_head
end BB429LowOddPhysical
