import CSectionComputable
import Lean.Elab.Tactic.Omega

namespace BB6.Agent8SectionRank
open BB6.Agent8Section BB6.Agent8ComputableC BB6.Agent8TotalC

private def rank (s : Nat × Nat × Nat) : Nat := s.1+2*s.2.1+s.2.2

private theorem rank_step_mono (s t : Nat × Nat × Nat)
    (h : BB6CLine.nextC s = some t) : rank s ≤ rank t := by
  rcases s with ⟨a,k,c⟩
  rcases c with _|_|_|_|d
  · rcases a with _|_|a
    · simp only [BB6CLine.nextC,Option.some.injEq] at h
      subst t; simp only [rank]; omega
    · rcases k with _|k
      · simp only [BB6CLine.nextC,Option.some.injEq] at h
        subst t; simp only [rank]; omega
      · simp only [BB6CLine.nextC,Option.some.injEq] at h
        subst t; simp only [rank]; omega
    · simp only [BB6CLine.nextC,Option.some.injEq] at h
      subst t; simp only [rank]; omega
  · simp only [BB6CLine.nextC,Option.some.injEq] at h
    subst t; simp only [rank]; omega
  · simp [BB6CLine.nextC] at h
  · simp only [BB6CLine.nextC,Option.some.injEq] at h
    subst t; simp only [rank]; omega
  · rcases a with _|a
    · by_cases he : k%2=0
      · simp only [BB6CLine.nextC,he,↓reduceIte,Option.some.injEq] at h
        subst t; simp only [rank]; omega
      · simp only [BB6CLine.nextC,he,↓reduceIte,Option.some.injEq] at h
        subst t; simp only [rank]; omega
    · simp only [BB6CLine.nextC,Option.some.injEq] at h
      subst t; simp only [rank]; omega

private theorem rank_run_mono (n : Nat) (s t : Nat × Nat × Nat)
    (h : run BB6CLine.nextC n (some s) = some t) : rank s ≤ rank t := by
  induction n generalizing s t with
  | zero =>
      simp only [run,Option.some.injEq] at h
      subst t
      omega
  | succ n ih =>
      rw [run_succ_head] at h
      cases hs : BB6CLine.nextC s with
      | none => simp [hs,run_none] at h
      | some u =>
          have hr : rank u ≤ rank t := by
            apply ih u t
            simpa [hs] using h
          have hf : rank s ≤ rank u := rank_step_mono s u hs
          omega

private theorem c0_first_strict (a k : Nat) :
    ∃ t : Nat × Nat × Nat, BB6CLine.nextC (a,k,0)=some t ∧
       rank (a,k,0) + 1 ≤ rank t := by
  rcases a with _|_|a
  · refine ⟨(1,0,2*k+2),rfl,?_⟩
    simp [rank]
    omega
  · rcases k with _|k
    · refine ⟨(5,0,1),rfl,?_⟩
      simp [rank]
    · refine ⟨(2,2,2*k+1),rfl,?_⟩
      simp [rank]
      omega
  · refine ⟨(a,1,2*k+1),rfl,?_⟩
    simp [rank]
    omega

/-- Each successful original c=0 first return strictly gains weighted rank. -/
theorem fastNext_rank_strict (a k aa kk : Nat)
    (h : fastNext (a,k) = some (aa,kk)) :
    a+2*k+1 ≤ aa+2*kk := by
  obtain ⟨t,hf,hstrict⟩ := c0_first_strict a k
  have hs := fastNext_exact (a,k)
  simp only [h,Option.map_some] at hs
  have hp := (fastTime_bounds (a,k)).1
  have he : (fastTime (a,k)-1)+1 = fastTime (a,k) := by omega
  rw [←he,run_succ_head] at hs
  change run BB6CLine.nextC (fastTime (a,k)-1) (BB6CLine.nextC (a,k,0)) =
     some (aa,kk,0) at hs
  rw [hf] at hs
  have hm := rank_run_mono (fastTime (a,k)-1) t (aa,kk,0) hs
  simp only [rank] at hm hstrict
  omega

/-- The first m successful section returns increase the rank by at least m.
    Thus reaching a fixed reset gateway has a linear-in-index return budget. -/
theorem section_gate_cutoff (m j : Nat)
    (h : run fastNext m (some (5,1)) = some (2*j+1,3*j+4)) :
    m ≤ 8*j+2 := by
  have all : ∀ m : Nat, ∀ p q : Nat × Nat,
      run fastNext m (some p) = some q →
      p.1+2*p.2+m ≤ q.1+2*q.2 := by
    intro m
    induction m with
    | zero =>
        intro p q hr
        simp only [run,Option.some.injEq] at hr
        subst q
        omega
    | succ m ih =>
        intro p q hr
        rw [run_succ_head] at hr
        cases hn : fastNext p with
        | none => simp [hn,run_none] at hr
        | some r =>
            have hstep := fastNext_rank_strict p.1 p.2 r.1 r.2 hn
            have htail := ih r q (by simpa [hn] using hr)
            omega
  have hz := all m (5,1) (2*j+1,3*j+4) h
  omega

#print axioms fastNext_rank_strict
#print axioms section_gate_cutoff
end BB6.Agent8SectionRank
