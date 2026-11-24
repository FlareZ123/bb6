import CLine
namespace BB6Agent6.C

/-- Reuse the authoritative original-source transition map. This keeps the
    finite certificate tied definitionally to the same CLine semantics used
    by the source reachability proof, rather than duplicating its matcher. -/
abbrev next : Nat × Nat × Nat → Option (Nat × Nat × Nat) :=
  BB6CLine.nextC

def run : Nat → Nat × Nat × Nat → Option (Nat × Nat × Nat)
  | 0,s => some s
  | n+1,s => (run n s).bind next

/-- All states with first two coordinates zero have no predecessor. -/
theorem no_incoming_zero_zero_large (s : Nat × Nat × Nat) (c : Nat)
    (hc : 4 ≤ c) : next s ≠ some (0,0,c) := by
  rcases s with ⟨a,k,d⟩
  rcases d with _ | _ | _ | _ | d
  · rcases a with _ | _ | a
    · simp [next]
    · rcases k with _ | k <;> simp [next]
    · simp [next]
  · simp [next]
  · simp [next]
  · simp [next]
  · rcases a with _ | a
    · by_cases hk : k%2=0
      · simp [next,hk]
      · simp [next,hk]
    · simp [next]

/-- Exclude j=0 in the published sparse feeder family. -/
theorem blank_ne_feeder_zero (n : Nat) :
    run n (5,0,1) ≠ some (0,0,10) := by
  cases n with
  | zero => simp [run]
  | succ n =>
    intro h
    simp only [run] at h
    cases hr : run n (5,0,1) with
    | none => simp [hr] at h
    | some s =>
      simp only [hr, Option.bind_some] at h
      exact no_incoming_zero_zero_large s 10 (by omega) h

#print axioms BB6Agent6.C.blank_ne_feeder_zero
end BB6Agent6.C
