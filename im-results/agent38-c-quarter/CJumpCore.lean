import CQuarter

namespace BB6Agent38

/-- Every legal high-sector sweep of length q is a genuine iteration of
    the published accelerated map, including the exact transition count. -/
theorem run_sweep (q a k c : Nat) (ha : q ≤ a) (hc : q + 3 ≤ c) :
    run q (some (a,k,c)) = some (a-q,k+q,c-q) := by
  induction q generalizing a k c with
  | zero => simp [run]
  | succ q ih =>
      have ha1 : 1 ≤ a := by omega
      have hc4 : 4 ≤ c := by omega
      obtain ⟨a',rfl⟩ : ∃ a' : Nat, a = a'+1 := ⟨a-1, by omega⟩
      obtain ⟨d,rfl⟩ : ∃ d : Nat, c = d+4 := ⟨c-4, by omega⟩
      have hs : q ≤ a' := by omega
      have ht : q+3 ≤ d+3 := by omega
      have hone : nextC (a'+1,k,d+4) = some (a',k+1,d+3) := rfl
      simp only [run,Option.bind_some,hone]
      rw [ih a' (k+1) (d+3) hs ht]
      simp only [Option.some.injEq, Prod.mk.injEq]
      omega

/-- An arithmetic shortcut, with the number of original accelerator calls
    returned alongside its final state. -/
def jump (s : S) : Nat × Option S :=
  let (a,k,c) := s
  if 0 < a ∧ 3 < c then
    let q := min a (c-3)
    (q, some (a-q,k+q,c-q))
  else (1, nextC s)

theorem jump_sound (s : S) : run (jump s).1 (some s) = (jump s).2 := by
  rcases s with ⟨a,k,c⟩
  by_cases h : 0<a ∧ 3<c
  · let q := min a (c-3)
    have hqa : q ≤ a := Nat.min_le_left _ _
    have hqc : q+3 ≤ c := by
      have hq := Nat.min_le_right a (c-3)
      dsimp [q]
      omega
    simpa [jump,h,q] using run_sweep q a k c hqa hqc
  · simp [jump,h,run]

def path : Nat → S → Nat × Option S
  | 0, s => (0,some s)
  | n+1,s =>
      let j := jump s
      match j.2 with
      | none => (j.1, none)
      | some t =>
          let p := path n t
          (p.1+j.1, p.2)

theorem run_add (m n : Nat) (o : Option S) :
    run (m+n) o = run m (run n o) := by
  induction n generalizing o with
  | zero => simp [run]
  | succ n ih =>
      rw [Nat.add_succ]
      change run (m+n) (o.bind nextC) = run m (run n (o.bind nextC))
      exact ih _

/-- The kernel-checked shortcut trace reproduces the uncompressed run
    at its exact accumulated original accelerator step count. -/
theorem path_sound (n : Nat) (s : S) :
    run (path n s).1 (some s) = (path n s).2 := by
  induction n generalizing s with
  | zero => rfl
  | succ n ih =>
      cases hj : jump s with
      | mk q o =>
          have hstep : run q (some s) = o := by
            simpa [hj] using jump_sound s
          cases o with
          | none =>
              simp only [path,hj,Prod.snd,Prod.fst]
              exact hstep
          | some t =>
              have hr : run (path n t).1 (some t) = (path n t).2 := ih t
              simp only [path,hj,Prod.snd,Prod.fst]
              rw [run_add,hstep]
              exact hr

#print axioms path_sound
#print axioms jump_sound
end BB6Agent38
