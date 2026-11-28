import Q0151FiniteModel

set_option maxHeartbeats 0
namespace BB6.Agent5Q0151UnitRunSaturation
open BB6.Agent5Q0151FiniteModel

/-!
For every abstract segment whose two mode images are at least -1, adding
more than one 10-pair does not change its abstract value compared with
adding exactly one. This is the missing algebraic part of saturation of
unbounded q0-151 macro parameters. It is not a claim of concrete nonhalting.
-/

def turn (s : SegmentSummary) : SegmentSummary :=
  segAppend s [true,false]

theorem dnext_one (g : Int) (hg : -1 ≤ g) :
    dnext g 1 = g := by
  by_cases h : g < 0
  · have he : g = -1 := by omega
    subst g
    decide
  · simp [dnext,h]

theorem dnext_lower (g : Int) (n : Nat) (hg : -1 ≤ g) :
    -1 ≤ dnext g n := by
  by_cases hneg : g < 0
  · simp [dnext,hneg]
  · by_cases h1 : n % 4 = 1
    · simpa [dnext,hneg,h1] using hg
    · by_cases h0 : n % 4 = 0
      · simp [dnext,hneg,h1,h0]
      · by_cases h2 : n % 4 = 2
        · by_cases hg1 : g = 1
          · simp [dnext,hneg,h1,h0,h2,hg1]
          · simp [dnext,hneg,h1,h0,h2,hg1]
        · simp [dnext,hneg,h1,h0,h2]

theorem plus_one_pos (n : Nat) : 0 < plus n 1 := by
  unfold plus
  by_cases h0 : n = 0
  · simp [h0]
  · simp only [if_neg h0]
    have h1 : ¬ (1 : Nat) = 0 := by decide
    simp only [if_neg h1]
    by_cases h : n + 1 ≤ 4
    · simp only [if_pos h]
      omega
    · simp only [if_neg h]
      omega

theorem turn_eq (s : SegmentSummary) :
    turn s =
      if s.first = 0 then
        ⟨plus s.last 1,0,1,0⟩
      else
        ⟨s.first,dnext s.imageN (plus s.last 1),
          dnext s.imageP (plus s.last 1),0⟩ := by
  have h : ¬ plus s.last 1 = 0 := Nat.ne_of_gt (plus_one_pos s.last)
  simp [turn,segAppend,segBit,segClosed,h]

theorem turn_first_pos (s : SegmentSummary) :
    (turn s).first ≠ 0 := by
  rw [turn_eq]
  by_cases h : s.first = 0
  · simp [h,plus_one_pos]
  · simp [h]

theorem turn_last_zero (s : SegmentSummary) :
    (turn s).last = 0 := by
  rw [turn_eq]
  split <;> rfl

theorem turn_lower_N (s : SegmentSummary) (h : -1 ≤ s.imageN) :
    -1 ≤ (turn s).imageN := by
  rw [turn_eq]
  by_cases hf : s.first = 0
  · simp [hf]
  · simpa [hf] using dnext_lower s.imageN (plus s.last 1) h

theorem turn_lower_P (s : SegmentSummary) (h : -1 ≤ s.imageP) :
    -1 ≤ (turn s).imageP := by
  rw [turn_eq]
  by_cases hf : s.first = 0
  · simp [hf]
  · simpa [hf] using dnext_lower s.imageP (plus s.last 1) h

theorem turn_fixed (s : SegmentSummary)
    (hf : s.first ≠ 0) (hl : s.last = 0)
    (hn : -1 ≤ s.imageN) (hp : -1 ≤ s.imageP) :
    turn s = s := by
  rw [turn_eq]
  cases s with
  | mk first imageN imageP last =>
    dsimp at hf hl hn hp
    subst last
    simp [hf,plus,dnext_one imageN hn,dnext_one imageP hp]

theorem turn_idempotent (s : SegmentSummary)
    (hn : -1 ≤ s.imageN) (hp : -1 ≤ s.imageP) :
    turn (turn s) = turn s := by
  exact turn_fixed (turn s) (turn_first_pos s) (turn_last_zero s)
    (turn_lower_N s hn) (turn_lower_P s hp)

def repeatTurn (s : SegmentSummary) : Nat → SegmentSummary
  | 0 => s
  | n+1 => repeatTurn (turn s) n

theorem repeatTurn_succ (s : SegmentSummary)
    (hn : -1 ≤ s.imageN) (hp : -1 ≤ s.imageP) (n : Nat) :
    repeatTurn s (n+1) = turn s := by
  induction n generalizing s with
  | zero => rfl
  | succ n ih =>
      change repeatTurn (turn s) (n+1) = turn s
      rw [ih (turn s) (turn_lower_N s hn) (turn_lower_P s hp),
        turn_idempotent s hn hp]

theorem segAppend_append (s : SegmentSummary) (xs ys : List Bool) :
    segAppend s (xs ++ ys) = segAppend (segAppend s xs) ys := by
  simp [segAppend,List.foldl_append]

theorem altWord_succ (n : Nat) :
    altWord (n+1) = [true,false] ++ altWord n := by
  simp [altWord,List.replicate_succ,List.flatten_cons]

theorem segment_alt_repeat (s : SegmentSummary) (n : Nat) :
    segAppend s (altWord n) = repeatTurn s n := by
  induction n generalizing s with
  | zero => rfl
  | succ n ih =>
      rw [altWord_succ,segAppend_append]
      change segAppend (turn s) (altWord n) = repeatTurn (turn s) n
      exact ih (turn s)

theorem segment_alt_saturation (s : SegmentSummary)
    (hn : -1 ≤ s.imageN) (hp : -1 ≤ s.imageP) (n : Nat) :
    segAppend s (altWord (n+1)) = segAppend s [true,false] := by
  rw [segment_alt_repeat,repeatTurn_succ s hn hp n]
  rfl

#print axioms turn_idempotent
#print axioms segment_alt_saturation
end BB6.Agent5Q0151UnitRunSaturation
