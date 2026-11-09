import Low42Delta
import JPhysicalPrefix
import BB429DeltaPhysicalBridge
import Lean.Elab.Tactic.Omega

set_option maxHeartbeats 30000000
set_option maxRecDepth 8192

namespace BB429Low42Physical
open BB6Bubble BB429JPhysical BB429Low42
open BB429OddExcursion BB429SourceE1Return

private theorem stage_tape_character (j k : Nat) (x : Int) :
  negFill (jTape (j+2*k+1) (2*j)) j x =
    decide (((-2*(j:Int)-4*(k:Int)-8 ≤ x ∧ x ≤ 2*(j:Int)+1) ∧
      ¬(-2*(j:Int)-4*(k:Int)-2 ≤ x ∧ x ≤ -2*(j:Int)-2 ∧ x%2=0))
      ∨ x=2*(j:Int)+3) := by
  have hp : (negFillTest j x ∨ jMark (j+2*k+1) (2*j) x) ↔
      (((-2*(j:Int)-4*(k:Int)-8 ≤ x ∧ x ≤ 2*(j:Int)+1) ∧
        ¬(-2*(j:Int)-4*(k:Int)-2 ≤ x ∧ x ≤ -2*(j:Int)-2 ∧ x%2=0))
        ∨ x=2*(j:Int)+3) := by
    unfold negFillTest jMark jHole
    omega
  unfold negFill jTape
  by_cases hfill : negFillTest j x
  · have ht : decide (((-2*(j:Int)-4*(k:Int)-8 ≤ x ∧ x ≤ 2*(j:Int)+1) ∧
        ¬(-2*(j:Int)-4*(k:Int)-2 ≤ x ∧ x ≤ -2*(j:Int)-2 ∧ x%2=0))
        ∨ x=2*(j:Int)+3) = true :=
      decide_eq_true_iff.mpr (hp.mp (Or.inl hfill))
    simp only [if_pos hfill, ht]
  · by_cases hJ : jMark (j+2*k+1) (2*j) x
    · have ht : decide (((-2*(j:Int)-4*(k:Int)-8 ≤ x ∧ x ≤ 2*(j:Int)+1) ∧
          ¬(-2*(j:Int)-4*(k:Int)-2 ≤ x ∧ x ≤ -2*(j:Int)-2 ∧ x%2=0))
          ∨ x=2*(j:Int)+3) = true :=
        decide_eq_true_iff.mpr (hp.mp (Or.inr hJ))
      simp only [if_neg hfill, if_pos hJ, ht]
    · have hn : ¬ (((-2*(j:Int)-4*(k:Int)-8 ≤ x ∧ x ≤ 2*(j:Int)+1) ∧
          ¬(-2*(j:Int)-4*(k:Int)-2 ≤ x ∧ x ≤ -2*(j:Int)-2 ∧ x%2=0))
          ∨ x=2*(j:Int)+3) := by
        intro hh
        rcases hp.mpr hh with hz | hj
        · exact hfill hz
        · exact hJ hj
      have hf : decide (((-2*(j:Int)-4*(k:Int)-8 ≤ x ∧ x ≤ 2*(j:Int)+1) ∧
          ¬(-2*(j:Int)-4*(k:Int)-2 ≤ x ∧ x ≤ -2*(j:Int)-2 ∧ x%2=0))
          ∨ x=2*(j:Int)+3) = false :=
        decide_eq_false hn
      simp only [if_neg hfill, if_neg hJ, hf]

private theorem getD_append {α : Type} (xs ys : List α) (i : Nat) (d : α) :
  (xs ++ ys).getD i d =
    if i < xs.length then xs.getD i d else ys.getD (i-xs.length) d := by
  induction xs generalizing i with
  | nil => simp
  | cons a xs ih =>
    cases i with
    | zero => simp
    | succ i => simpa using ih i

private theorem ones_getD (n i : Nat) :
  (ones n).getD i false = decide (i < n) := by
  induction n generalizing i with
  | zero => simp [ones]
  | succ n ih =>
    cases i with
    | zero => simp [ones]
    | succ i => simpa [ones,List.replicate_succ] using ih i

private theorem tens_getD (n i : Nat) :
  (tens n).getD i false = decide (i < 2*n ∧ i%2=0) := by
  induction n generalizing i with
  | zero => simp [tens]
  | succ n ih =>
    cases i with
    | zero => rfl
    | succ i =>
      cases i with
      | zero => rfl
      | succ i =>
        change (tens n).getD i false =
          decide (i+2 < 2*(n+1) ∧ (i+2)%2=0)
        rw [ih]
        have hp : (i < 2*n ∧ i%2=0) ↔
            (i+2 < 2*(n+1) ∧ (i+2)%2=0) := by omega
        simp only [hp]

private theorem tens_length (n : Nat) : (tens n).length = 2*n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    change (true :: false :: tens n).length = 2*(n+1)
    simp only [List.length_cons, ih]
    omega

private theorem tail_getD (k i : Nat) :
  (tens (2*k+1) ++ ones 6).getD i false =
    decide (i < 4*k+8 ∧ (i < 4*k+2 → i%2=0)) := by
  rw [getD_append]
  have hlen : (tens (2*k+1)).length = 4*k+2 := by
    rw [tens_length]
    omega
  rw [hlen]
  by_cases hi : i < 4*k+2
  · rw [if_pos hi, tens_getD]
    have hp : (i < 2*(2*k+1) ∧ i%2=0) ↔
        (i < 4*k+8 ∧ (i < 4*k+2 → i%2=0)) := by omega
    simp only [hp]
  · rw [if_neg hi,ones_getD]
    have hp : (i-(4*k+2) < 6) ↔
        (i < 4*k+8 ∧ (i < 4*k+2 → i%2=0)) := by omega
    simp only [hp]

private theorem stage_left_char (j k i : Nat) :
  (stage42 j k).left.getD i false =
    decide (i < 4*j+4*k+8 ∧
      ¬(4*j ≤ i ∧ i < 4*j+4*k+2 ∧ i%2=1)) := by
  change ((ones (4*j) ++ tens (2*k+1)) ++ ones 6).getD i false = _
  rw [List.append_assoc]
  rw [getD_append]
  have hlen : (ones (4*j)).length = 4*j := by simp [ones]
  rw [hlen]
  by_cases hi : i < 4*j
  · rw [if_pos hi,ones_getD]
    have hp : (i<4*j) ↔
        (i < 4*j+4*k+8 ∧
          ¬(4*j ≤ i ∧ i < 4*j+4*k+2 ∧ i%2=1)) := by omega
    simp only [hp]
  · rw [if_neg hi,tail_getD]
    have hp : (i-4*j < 4*k+8 ∧
      (i-4*j < 4*k+2 → (i-4*j)%2=0)) ↔
      (i < 4*j+4*k+8 ∧
        ¬(4*j ≤ i ∧ i < 4*j+4*k+2 ∧ i%2=1)) := by omega
    simp only [hp]

private theorem stage_right_char (i : Nat) :
  ([true,false,true] : List Bool).getD i false =
    decide (i=0 ∨ i=2) := by
  cases i with
  | zero => rfl
  | succ i =>
    cases i with
    | zero => rfl
    | succ i =>
      cases i with
      | zero => rfl
      | succ i => simp

/-- The bubble checkpoint equals the source chart on every integer tape cell. -/
theorem stage_tape_rep (j k : Nat) :
  negFill (jTape (j+2*k+1) (2*j)) j (2*(j:Int)) = true ∧
  (∀ i : Nat,
    negFill (jTape (j+2*k+1) (2*j)) j
      (2*(j:Int)-((i:Int)+1)) =
      (stage42 j k).left.getD i false) ∧
  (∀ i : Nat,
    negFill (jTape (j+2*k+1) (2*j)) j
      (2*(j:Int)+((i:Int)+1)) =
      (stage42 j k).right.getD i false) := by
  constructor
  · rw [stage_tape_character]
    have hp : -2*(j:Int)-4*(k:Int)-8 ≤ 2*(j:Int) ∧
        2*(j:Int) ≤ 2*(j:Int)+1 ∧
        ¬(-2*(j:Int)-4*(k:Int)-2 ≤ 2*(j:Int) ∧
          2*(j:Int) ≤ -2*(j:Int)-2 ∧ (2*(j:Int))%2=0) := by omega
    exact decide_eq_true_iff.mpr (Or.inl ⟨⟨hp.1,hp.2.1⟩,hp.2.2⟩)
  constructor
  · intro i
    rw [stage_tape_character, stage_left_char]
    have hp : (((-2*(j:Int)-4*(k:Int)-8 ≤
        2*(j:Int)-((i:Int)+1) ∧
        2*(j:Int)-((i:Int)+1) ≤ 2*(j:Int)+1) ∧
        ¬(-2*(j:Int)-4*(k:Int)-2 ≤ 2*(j:Int)-((i:Int)+1) ∧
          2*(j:Int)-((i:Int)+1) ≤ -2*(j:Int)-2 ∧
          (2*(j:Int)-((i:Int)+1))%2=0)) ∨
         2*(j:Int)-((i:Int)+1)=2*(j:Int)+3) ↔
        (i < 4*j+4*k+8 ∧
          ¬(4*j ≤ i ∧ i < 4*j+4*k+2 ∧ i%2=1)) := by omega
    simp only [hp]
  · intro i
    change negFill (jTape (j+2*k+1) (2*j)) j
        (2*(j:Int)+((i:Int)+1)) =
      ([true,false,true]:List Bool).getD i false
    rw [stage_tape_character,stage_right_char]
    have hp : (((-2*(j:Int)-4*(k:Int)-8 ≤
        2*(j:Int)+((i:Int)+1) ∧
        2*(j:Int)+((i:Int)+1) ≤ 2*(j:Int)+1) ∧
        ¬(-2*(j:Int)-4*(k:Int)-2 ≤ 2*(j:Int)+((i:Int)+1) ∧
          2*(j:Int)+((i:Int)+1) ≤ -2*(j:Int)-2 ∧
          (2*(j:Int)+((i:Int)+1))%2=0)) ∨
        2*(j:Int)+((i:Int)+1)=2*(j:Int)+3) ↔
        (i=0 ∨ i=2) := by omega
    simp only [hp]

theorem stage_represented (j k : Nat) :
  BB429PhysicalBridge.Represents (stage42 j k)
    {state:=BB6Bubble.A,head:=2*(j:Int),
     tape:=negFill (jTape (j+2*k+1) (2*j)) j} := by
  obtain ⟨hc,hl,hr⟩ := stage_tape_rep j k
  exact ⟨rfl,hc,hl,hr⟩

private theorem low42_holes (j k i : Nat) (hi : i < j) :
  jTape (j+2*k+1) (2*j) (-2*((i+1:Nat):Int)) = false := by
  have hj : ¬jMark (j+2*k+1) (2*j) (-2*((i+1:Nat):Int)) := by
    unfold jMark jHole
    omega
  change (if jMark (j+2*k+1) (2*j) (-2*((i+1:Nat):Int))
    then true else false) = false
  exact if_neg hj

private theorem low42_odds (j k : Nat) (x : Int)
    (hlo : -2*(j:Int)<x) (hhi : x<0) (hodd : x%2≠0) :
  jTape (j+2*k+1) (2*j) x = true := by
  have hj : jMark (j+2*k+1) (2*j) x := by
    unfold jMark jHole
    left
    omega
  simp [jTape,hj]

private theorem low42_right (j k : Nat) (x : Int)
    (hlo : 0≤x) (hhi : x≤2*(j:Int)) :
  jTape (j+2*k+1) (2*j) x = true := by
  have hj : jMark (j+2*k+1) (2*j) x := by
    unfold jMark jHole
    left
    omega
  simp [jTape,hj]

private theorem physical_compose (m n : Nat) (a b c : BB6Coverage.Config)
    (h1 : BB6Coverage.run BB429PhysicalFrontier.target429 m a = some b)
    (h2 : BB6Coverage.run BB429PhysicalFrontier.target429 n b = some c) :
  BB6Coverage.run BB429PhysicalFrontier.target429 (m+n) a = some c := by
  rw [BB6Bubble.run_add',h1]
  exact h2

/-- Original six-state infinite-tape return from J(j+2k+1,2j), k>=1,
    with exact successful instruction count and absolute head coordinate.
    Prepared input only: no blank-origin reachability or nonhalting result. -/
theorem low42_raw_head (j m : Nat) :
  ∃ c', BB6Coverage.run BB429PhysicalFrontier.target429
    (4*j*j+22*j+18*(m+1)+79)
    {state:=BB6Bubble.A,head:=0,
     tape:=jTape (j+2*(m+1)+1) (2*j)} = some c' ∧
    BB429PhysicalBridge.Represents
      (BB429FinishScanEDelta.junc 0 0 (4*j+4*(m+1)+12)) c' ∧
    c'.head = -((2*j+4*(m+1)+5:Nat):Int) := by
  let k := m+1
  have hfirst : BB6Coverage.run BB429PhysicalFrontier.target429
      (4*j*j+2*j)
      {state:=BB6Bubble.A,head:=0,
       tape:=jTape (j+2*k+1) (2*j)} =
      some {state:=BB6Bubble.A,head:=2*(j:Int),
        tape:=negFill (jTape (j+2*k+1) (2*j)) j} := by
    exact BB6Bubble.multi_bubble_prefix BB429PhysicalFrontier.target429 j j
      (jTape (j+2*k+1) (2*j)) (by omega)
      (by decide) (by decide) (by decide) (by decide)
      (low42_holes j k) (low42_odds j k) (low42_right j k)
  obtain ⟨c',hsecond,hrep,hhead⟩ :=
    BB429DeltaPhysicalBridge.source_runWithDelta_rep
      (20*j+18*k+79) (stage42 j k)
      {state:=BB6Bubble.A,head:=2*(j:Int),
       tape:=negFill (jTape (j+2*k+1) (2*j)) j}
      (stage_represented j k)
      (BB429FinishScanEDelta.junc 0 0 (4*j+4*k+12))
      (-((4*j+4*k+5:Nat):Int)) (low42_source j m)
  have htotal := physical_compose (4*j*j+2*j) (20*j+18*k+79)
      {state:=BB6Bubble.A,head:=0,tape:=jTape (j+2*k+1) (2*j)}
      {state:=BB6Bubble.A,head:=2*(j:Int),
       tape:=negFill (jTape (j+2*k+1) (2*j)) j} c' hfirst hsecond
  have ht : (4*j*j+2*j)+(20*j+18*k+79) =
      4*j*j+22*j+18*(m+1)+79 := by
    dsimp [k]
    omega
  have hh : c'.head = -((2*j+4*(m+1)+5:Nat):Int) := by
    dsimp [k] at hhead
    omega
  exact ⟨c', by simpa only [ht] using htotal, hrep, hh⟩

#print axioms stage_tape_rep
#print axioms stage_represented
#print axioms low42_raw_head
end BB429Low42Physical
