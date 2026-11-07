import BB429Burst

namespace BB429TurnaroundCore
open BB429Burst

abbrev State := Nat × Nat

def burstExit : Nat → Nat → State × Nat
  | u, w =>
    if h : 2*u+3 ≤ w then
      let r := burstExit (2*u+3) (w-2*u-3)
      (r.1, r.2+1)
    else
      ((u,w),0)
termination_by u w => w
decreasing_by
  omega

theorem firstRun_shift (u w u' w' n : Nat)
    (hstep : firstStep (u,w) = some (u',w')) :
    firstRun (n+1) (u,w) = firstRun n (u',w') := by
  induction n with
  | zero =>
    simp [firstRun, hstep]
  | succ n ih =>
    change (firstRun (n+1) (u,w)).bind firstStep =
      (firstRun n (u',w')).bind firstStep
    rw [ih]

theorem burstExit_spec (u w : Nat) :
    let r := burstExit u w
    firstRun r.2 (u,w) = some r.1 ∧ ¬ (2*r.1.1+3 ≤ r.1.2) := by
  induction w using Nat.strongRecOn generalizing u with
  | ind w ih =>
    generalize hdef : burstExit u w = r
    rw [burstExit.eq_1] at hdef
    by_cases h : 2*u+3 ≤ w
    · have hlt : w-2*u-3 < w := by omega
      have hr := ih (w-2*u-3) hlt (2*u+3)
      simp [h] at hdef
      cases hdef
      dsimp at hr
      rcases hr with ⟨hrun,hstop⟩
      constructor
      · have hs : firstStep (u,w) = some (2*u+3,w-2*u-3) := by
          simp [firstStep,h]
        rw [firstRun_shift u w (2*u+3) (w-2*u-3) (burstExit (2*u+3) (w-2*u-3)).2 hs]
        exact hrun
      · exact hstop
    · simp [h] at hdef
      cases hdef
      constructor
      · rfl
      · simpa using h

theorem burstExit_formula (u w : Nat) :
    let r := burstExit u w
    r.1.1 + 3 = (u+3)*2^r.2 ∧
    2*r.1.1+r.1.2 = 2*u+w+3*r.2 := by
  let r := burstExit u w
  have hspec := burstExit_spec u w
  dsimp [r] at hspec
  obtain ⟨hrun,hstop⟩ := hspec
  exact prefix_formula u w r.2 r.1.1 r.1.2 hrun

theorem burstExit_maximal (u w : Nat) :
    let r := burstExit u w
    2*r.1.1+3 > r.1.2 := by
  have hspec := burstExit_spec u w
  omega

#print axioms burstExit_spec
#print axioms burstExit_formula
#print axioms burstExit_maximal

end BB429TurnaroundCore
