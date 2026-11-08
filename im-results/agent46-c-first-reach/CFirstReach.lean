import CSectionComputable
import SectionReachBridge
import Lean.Elab.Tactic.Omega

namespace BB6.Agent46CFirstReach
open BB6.Agent8Section BB6.Agent8TotalC BB6.Agent8ComputableC

private theorem raw_reach_to_run {s : Nat × Nat × Nat}
    (hs : BB6CLine.Reach s) :
    ∃ n, run BB6CLine.nextC n (some (5,0,1)) = some s := by
  induction hs with
  | init => exact ⟨0,rfl⟩
  | next s t hs ht ih =>
      obtain ⟨n,hn⟩ := ih
      refine ⟨n+1, ?_⟩
      change (run BB6CLine.nextC n (some (5,0,1))).bind BB6CLine.nextC = some t
      simp [hn,ht]

private theorem raw_run_to_reach (n : Nat) (s : Nat × Nat × Nat)
    (hs : BB6CLine.Reach s) (t : Nat × Nat × Nat)
    (h : run BB6CLine.nextC n (some s) = some t) :
    BB6CLine.Reach t := by
  induction n generalizing s with
  | zero =>
      have he : s=t := by simpa [run] using h
      subst t
      exact hs
  | succ n ih =>
      rw [run_succ_head] at h
      cases hstep : BB6CLine.nextC s with
      | none => simp [hstep,run_none] at h
      | some u =>
          have hu := BB6CLine.Reach.next s u hs hstep
          exact ih u hu (by simpa [hstep] using h)

/-- Exact equality of the authentic blank-reachable c=0 slice and the
    first-hit scanner section orbit. No spurious or missing section visits. -/
theorem c0_reach_iff_fast_section (a k : Nat) :
    BB6CLine.Reach (a,k,0) ↔
       ∃ m, run fastNext m (some (5,1)) = some (a,k) := by
  have hinj : Function.Injective embed := by
    intro p q h
    rcases p with ⟨x,y⟩
    rcases q with ⟨x',y'⟩
    simp only [embed,Prod.mk.injEq] at h ⊢
    exact ⟨h.1,h.2.1⟩
  have hfirst : ∀ p j q, 1 ≤ j → j < fastTime p →
      run BB6CLine.nextC j (some (embed p)) ≠ some (embed q) := by
    intro p j q hj hlt heq
    have h := fastNext_first p j hj hlt
    rw [heq] at h
    simp [BB6.Agent8Scan.finish, BB6.Agent8ComputableC.decode, embed] at h
  constructor
  · intro hr
    obtain ⟨n,hn⟩ := raw_reach_to_run hr
    cases n with
    | zero => simp [run] at hn
    | succ n =>
        have hroot : BB6CLine.nextC (5,0,1) = some (embed (5,1)) := rfl
        have hh : run BB6CLine.nextC n (some (embed (5,1))) =
              some (embed (a,k)) := by
          rw [run_succ_head] at hn
          change run BB6CLine.nextC n ((some (5,0,1)).bind BB6CLine.nextC) = some (a,k,0) at hn
          simp only [Option.bind_some,hroot] at hn
          simpa [embed] using hn
        exact BB6.Agent46SectionReach.raw_reach_of_first
          BB6CLine.nextC embed fastTime fastNext hinj
          (fun p => (fastTime_bounds p).1) fastNext_exact hfirst n (5,1) (a,k) hh
  · rintro ⟨m,hm⟩
    obtain ⟨n,hn⟩ := BB6.Agent46SectionReach.raw_of_section
      BB6CLine.nextC embed fastTime fastNext fastNext_exact m (5,1) (a,k) hm
    have hstart : BB6CLine.Reach (embed (5,1)) :=
      BB6CLine.Reach.next (5,0,1) (embed (5,1)) BB6CLine.Reach.init rfl
    exact raw_run_to_reach n (embed (5,1)) hstart (embed (a,k)) hn

#print axioms c0_reach_iff_fast_section
end BB6.Agent46CFirstReach
