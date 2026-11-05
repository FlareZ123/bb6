import BB429Rank
import Lean.Elab.Tactic.Omega

namespace BB429No11Odd
set_option maxRecDepth 30000
set_option maxHeartbeats 10000000

/-- The exact accelerator has no transition whose first target counter is 4. -/
theorem no_parent_four (x y b : Nat) :
    BB429.next (x,y) ≠ some (4,b) := by
  intro hs
  simp only [BB429.next] at hs
  repeat' (split at hs <;> try contradiction)
  all_goals simp_all [Prod.mk.injEq, Option.some.injEq]
  all_goals omega

/-- Any reachable section with first counter 4 would require an impossible
    incoming transition, since the blank section begins with counter 0. -/
theorem rooted_no_four (n b : Nat) :
    BB429.run n (0,0) ≠ some (4,b) := by
  intro h
  cases n with
  | zero => simp [BB429.run] at h
  | succ n =>
    simp only [BB429.run] at h
    cases hp : BB429.run n (0,0) with
    | none => simp [hp] at h
    | some p =>
      simp only [hp,Option.bind_some] at h
      exact no_parent_four p.1 p.2 b h

/-- A target with counter 11 and odd second counter must enter through
    the first subtraction branch from first counter 4. -/
theorem incoming_eleven_odd (x y b : Nat)
    (hs : BB429.next (x,y)=some (11,b))
    (hb : b%2=1) : x=4 ∧ y=b+11 := by
  simp only [BB429.next] at hs
  repeat' (split at hs <;> try contradiction)
  all_goals simp_all [Prod.mk.injEq,Option.some.injEq]
  all_goals omega

/-- Globally for the blank-root machine, counter 11 can only be entered
    with even second counter. -/
theorem rooted_eleven_even (n b : Nat)
    (h : BB429.run n (0,0)=some (11,b)) : b%2=0 := by
  by_contra ho
  have hb : b%2=1 := by omega
  cases n with
  | zero => simp [BB429.run] at h
  | succ n =>
    simp only [BB429.run] at h
    cases hp : BB429.run n (0,0) with
    | none => simp [hp] at h
    | some p =>
      simp only [hp,Option.bind_some] at h
      obtain ⟨hx,hy⟩ := incoming_eleven_odd p.1 p.2 b h hb
      have hf : BB429.run n (0,0)=some (4,p.2) := by
        have heq : p=(4,p.2) := Prod.ext hx rfl
        rw [heq] at hp
        exact hp
      exact rooted_no_four n p.2 hf

#print axioms no_parent_four
#print axioms incoming_eleven_odd
#print axioms rooted_eleven_even
end BB429No11Odd
