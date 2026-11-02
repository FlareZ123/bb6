import CLine

namespace BB6CLine

private def initial : Nat × Nat × Nat := (5,0,1)
private def advance (o : Option (Nat × Nat × Nat)) : Option (Nat × Nat × Nat) :=
  o.bind nextC

/-- Explicit option iteration, equivalent to the CollatzHalts definition. -/
private def iter : Nat → Option (Nat × Nat × Nat)
  | 0 => some initial
  | n+1 => advance (iter n)

private theorem iter_zero : iter 0 = some initial := by rfl
private theorem iter_succ (n:Nat):iter (n+1)=advance (iter n):=by rfl

private theorem iter_some_reachable (n:Nat) (s:Nat×Nat×Nat)
    (h:iter n=some s):Reach s:=by
  induction n generalizing s with
  | zero =>
      have hh:s=initial := by simpa [iter] using h.symm
      rw [hh]
      exact Reach.init
  | succ n ih =>
      rw [iter_succ] at h
      cases hp:iter n with
      | none => simp [advance,hp] at h
      | some p =>
          have ht:nextC p=some s:=by simpa [advance,hp] using h
          exact Reach.next p s (ih p hp) ht

private theorem reached_iter_some (s:Nat×Nat×Nat) (h:Reach s):
    ∃ n, iter n=some s:=by
  induction h with
  | init => exact ⟨0,rfl⟩
  | next p q hp ht ih =>
      obtain ⟨n,hn⟩:=ih
      refine ⟨n+1,?_⟩
      rw [iter_succ,hn]
      simpa [advance] using ht

/-- Exact agreement of the reachability and option-iteration stop semantics. -/
theorem stops_iff_option_iterate :
    (∃ s, Reach s ∧ nextC s=none) ↔
    (∃ n, (iter n).isNone) := by
  constructor
  · rintro ⟨s,hr,ht⟩
    obtain ⟨n,hn⟩:=reached_iter_some s hr
    refine ⟨n+1,?_⟩
    rw [iter_succ,hn]
    simpa [advance,ht]
  · rintro ⟨n,hn⟩
    induction n with
    | zero => simp [iter] at hn
    | succ n ih =>
        rw [iter_succ] at hn
        cases hp:iter n with
        | none => exact ih (by simpa [hp] using hn)
        | some s =>
            have hs:nextC s=none := by
              simpa [advance,hp] using hn
            exact ⟨s,iter_some_reachable n s hp,hs⟩

#print axioms BB6CLine.stops_iff_option_iterate
end BB6CLine
