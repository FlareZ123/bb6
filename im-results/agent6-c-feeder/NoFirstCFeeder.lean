import Std
namespace BB6Agent6.C

/-- Exact copy of the public Cryptids 3-counter acceleration used by Agent 8. -/
def next : Nat × Nat × Nat → Option (Nat × Nat × Nat)
  | (a,k,1) => some (a,k+1,0)
  | (_,_,2) => none
  | (a,k,3) => some (a,k+2,1)
  | (0,k,0) => some (1,0,2*k+2)
  | (1,0,0) => some (5,0,1)
  | (1,k+1,0) => some (2,2,2*k+1)
  | (a+2,k,0) => some (a,1,2*k+1)
  | (0,k,d+4) => if k%2=0 then
       some (4*(k/2)+2,2,d+1) else some (4*(k/2)+5,0,d+4)
  | (a+1,k,d+4) => some (a,k+1,d+3)

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
