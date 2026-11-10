import ChampionRootBridge
import Lean.Elab.Tactic.Omega

namespace BB6Coverage.Agent48Champion

/-!
A source-connected counted sweep for the actual 12-entry BusyCoq TM63.
Uses the unchanged original \`BB6Coverage.run\`, \`Config\`, \`applyMove\`,
and \`Agent48Champion.tm2\` from the champion root proof.
This is one rigorously timed physical submacro, not an exact champion score.

At state D, with a one under the head and a zero immediately to its right,
three ordinary transitions carry the zero one cell left. Repeating over an
arbitrary contiguous block of marked cells costs exactly three moves per cell,
without any condition on the rest of the infinite tape.
-/

def holeThree (T : Int → Bool) (h : Int) : Int → Bool :=
  fun x => if x = h+1 then true else if x = h then false else T x

private theorem lookup31 :
    tm2 ((3 : Fin 6), true) = some ⟨true,true,1⟩ := by rfl
private theorem lookup10 :
    tm2 ((1 : Fin 6), false) = some ⟨true,false,2⟩ := by rfl
private theorem lookup21 :
    tm2 ((2 : Fin 6), true) = some ⟨false,false,3⟩ := by rfl

theorem counted_three_left (T : Int → Bool) (h : Int)
    (ht : T h = true) (hr : T (h+1) = false) :
    run tm2 3 ⟨3,h,T⟩ = some ⟨3,h-1,holeThree T h⟩ := by
  have hne : h + 1 ≠ h := by omega
  have hround : h + 1 + (-1) = h := by omega
  simp [run, rawStep, readSlot, applyMove, ht, hr, hround, hne,
    lookup31, lookup10, lookup21]
  constructor
  · omega
  · funext x
    by_cases hx1 : x = h+1
    · have hx0 : x ≠ h := by omega
      simp [holeThree, hx1, hx0]
    · by_cases hx0 : x = h <;> simp [holeThree, hx1, hx0] <;> omega

def sweptLeft : Nat → (Int → Bool) → Int → (Int → Bool)
  | 0, T, _ => T
  | n+1, T, h => sweptLeft n (holeThree T h) (h-1)

def leftOnes (T : Int → Bool) (h : Int) (n : Nat) : Prop :=
  ∀ i : Nat, i<n → T (h-(i:Int)) = true

private theorem leftOnes_tail (T : Int → Bool) (h : Int) (n : Nat)
    (hon : leftOnes T h (n+1)) :
    leftOnes (holeThree T h) (h-1) n := by
  intro i hi
  have hold := hon (i+1) (by omega)
  have neq1 : h-1-(i:Int) ≠ h+1 := by omega
  have neq2 : h-1-(i:Int) ≠ h := by omega
  have heq : h-1-(i:Int) = h-((i+1:Int)) := by omega
  unfold holeThree
  rw [if_neg neq1, if_neg neq2, heq]
  exact hold

/-- Exactly \`3*n\` successful original TM63 transitions sweep left over a
contiguous run of \`n\` ones, starting with a zero immediately to the right.
The exact entire resulting physical tape is \`sweptLeft\`; no bounded window
and no finite-tape approximation occur in the statement. -/
theorem counted_left_sweep (n : Nat) (T : Int → Bool) (h : Int)
    (hon : leftOnes T h n) (hr : T (h+1) = false) :
    run tm2 (3*n) ⟨3,h,T⟩ =
      some ⟨3,h-(n:Int),sweptLeft n T h⟩ := by
  induction n generalizing T h with
  | zero => simp [run,sweptLeft]
  | succ n ih =>
    have ht : T h = true := by simpa using hon 0 (by omega)
    have hstep := counted_three_left T h ht hr
    have hon' : leftOnes (holeThree T h) (h-1) n :=
      leftOnes_tail T h n hon
    have hr' : holeThree T h ((h-1)+1) = false := by
      have hne : h ≠ h+1 := by omega
      simp [holeThree, hne, show (h-1)+1=h by omega]
    have htail := ih (holeThree T h) (h-1) hon' hr'
    have hnum : 3 * (n+1) = 3 + 3*n := by omega
    rw [hnum,run_append,hstep]
    simp only [Option.bind_some]
    rw [htail]
    have hhead : h-1-(n:Int) = h-((n+1:Int)) := by omega
    simpa [sweptLeft,hhead]

#print axioms counted_three_left
#print axioms counted_left_sweep

end BB6Coverage.Agent48Champion
