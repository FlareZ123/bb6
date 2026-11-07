import M32SectionEmbedding
import SectionFirstReturn
import CReachBridge

namespace BB6.Agent15

open BB6.Agent46

private theorem sectionRun_add {α : Type} (f : α → Option α) (n m : Nat) (s : Option α) :
    BB6.Agent8Section.run f (n+m) s =
      BB6.Agent8Section.run f m (BB6.Agent8Section.run f n s) := by
  induction m with
  | zero => rfl
  | succ m ih =>
      rw [Nat.add_succ]
      change (BB6.Agent8Section.run f (n+m) s).bind f =
        (BB6.Agent8Section.run f m (BB6.Agent8Section.run f n s)).bind f
      rw [ih]

private theorem agent46_run_add (n m : Nat) (s : Option (Nat × Nat × Nat)) :
    BB6.Agent46.run (n+m) s = BB6.Agent46.run m (BB6.Agent46.run n s) := by
  simpa only [BB6.Agent46.run_eq] using
    (sectionRun_add BB6CLine.nextC n m s)

private theorem agent46_run_none (n : Nat) :
    BB6.Agent46.run n (none : Option (Nat × Nat × Nat)) = none := by
  rw [BB6.Agent46.run_eq]
  induction n with
  | zero => rfl
  | succ n ih => simp [BB6.Agent8Section.run, ih]

private theorem cReach_next {a k a' k' : Nat} (h : CReach a k)
    (hs : BB6.Agent46.secNext (a,k)=some (a',k')) : CReach a' k' := by
  rcases h with ⟨m,hm⟩
  refine ⟨m+1, ?_⟩
  have hstep : BB6.Agent8Section.run BB6.Agent46.secNext 1 (some (a,k))=some (a',k') := by
    simp [BB6.Agent8Section.run,hs]
  calc
    BB6.Agent8Section.run BB6.Agent46.secNext (m+1) (some (5,1)) =
        BB6.Agent8Section.run BB6.Agent46.secNext 1
          (BB6.Agent8Section.run BB6.Agent46.secNext m (some (5,1))) := by
      simpa using (sectionRun_add BB6.Agent46.secNext m 1 (some (5,1)))
    _ = BB6.Agent8Section.run BB6.Agent46.secNext 1 (some (a,k)) := by rw [hm]
    _ = some (a',k') := hstep

private theorem section_returns_preserve_CReach :
    ∀ n, ∀ a k b c,
      CReach a k →
      BB6.Agent46.run n (some (a,k,0)) = some (b,c,0) →
      CReach b c := by
  intro n
  refine Nat.strongRecOn n ?_
  intro n ih a k b c hreach hrun
  by_cases hn0 : n=0
  · subst n
    simp only [BB6.Agent46.run] at hrun
    simp only [Option.some.injEq, Prod.mk.injEq] at hrun
    rcases hrun with ⟨rfl,rfl,_⟩
    exact hreach
  · have htpos : 0<BB6.Agent46.secTime (a,k) := by
      have hp := BB6.Agent46.sec_positive a k
      omega
    by_cases hlt : n<BB6.Agent46.secTime (a,k)
    · have hno := section_no_early_c0 a k n (by omega) hlt b c
      exact False.elim (hno hrun)
    · have hle : BB6.Agent46.secTime (a,k)≤n := by omega
      have hsec := BB6.Agent46.section_exact a k
      cases hnext : BB6.Agent46.secNext (a,k) with
      | none =>
          have hsecNone : BB6.Agent46.run (BB6.Agent46.secTime (a,k))
              (some (a,k,0))=none := by
            rw [hnext] at hsec
            simpa using hsec
          have hsplit : n=BB6.Agent46.secTime (a,k)+(n-BB6.Agent46.secTime (a,k)) := by omega
          have hrunNone : BB6.Agent46.run n (some (a,k,0))=none := by
            calc
              BB6.Agent46.run n (some (a,k,0)) =
                  BB6.Agent46.run (BB6.Agent46.secTime (a,k)+(n-BB6.Agent46.secTime (a,k)))
                    (some (a,k,0)) := congrArg (fun m => BB6.Agent46.run m (some (a,k,0))) hsplit
              _ = BB6.Agent46.run (n-BB6.Agent46.secTime (a,k))
                    (BB6.Agent46.run (BB6.Agent46.secTime (a,k)) (some (a,k,0))) :=
                    agent46_run_add _ _ _
              _ = none := by rw [hsecNone,agent46_run_none]
          rw [hrunNone] at hrun
          cases hrun
      | some p =>
          have hsecSome : BB6.Agent46.run (BB6.Agent46.secTime (a,k))
              (some (a,k,0))=some (p.1,p.2,0) := by
            rw [hnext] at hsec
            simpa [BB6.Agent46.embed0] using hsec
          have hreachNext : CReach p.1 p.2 := cReach_next hreach hnext
          have hsplit : n=BB6.Agent46.secTime (a,k)+(n-BB6.Agent46.secTime (a,k)) := by omega
          have htail : BB6.Agent46.run (n-BB6.Agent46.secTime (a,k))
              (some (p.1,p.2,0))=some (b,c,0) := by
            calc
              BB6.Agent46.run (n-BB6.Agent46.secTime (a,k)) (some (p.1,p.2,0)) =
                  BB6.Agent46.run (n-BB6.Agent46.secTime (a,k))
                    (BB6.Agent46.run (BB6.Agent46.secTime (a,k)) (some (a,k,0))) := by rw [hsecSome]
              _ = BB6.Agent46.run (BB6.Agent46.secTime (a,k)+(n-BB6.Agent46.secTime (a,k)))
                    (some (a,k,0)) := (agent46_run_add _ _ _).symm
              _ = some (b,c,0) := by rw [hsplit]; exact hrun
          have hlt' : n-BB6.Agent46.secTime (a,k)<n := by omega
          exact ih (n-BB6.Agent46.secTime (a,k)) hlt' p.1 p.2 b c hreachNext htail

private theorem runN_eq_agent8 (n : Nat) (s : Option (Nat × Nat × Nat)) :
    BB6.CReachBridge.runN n s = BB6.Agent8Section.run BB6CLine.nextC n s := by
  induction n with
  | zero => rfl
  | succ n ih =>
      simp [BB6.CReachBridge.runN, BB6.CReachBridge.stepC, BB6.Agent8Section.run, ih]

theorem m32_section_reach_reflects {a k : Nat}
    (h : BB6CLine.Reach (a,k,0)) : CReach a k := by
  obtain ⟨n,hn⟩ := BB6.CReachBridge.run_of_reachable h
  have hrun8 : BB6.Agent8Section.run BB6CLine.nextC n (some (5,0,1))=some (a,k,0) := by
    rw [← runN_eq_agent8 n (some (5,0,1))]
    exact hn
  have hnpos : 0<n := by
    by_cases hn0 : n=0
    · subst n
      simp [BB6.Agent8Section.run, Option.some.injEq,Prod.mk.injEq] at hrun8
      omega
    · omega
  have hfirst : BB6.Agent8Section.run BB6CLine.nextC 1 (some (5,0,1))=some (5,1,0) := by
    simp [BB6.Agent8Section.run,BB6CLine.nextC]
  have hsplit : n=1+(n-1) := by omega
  have htail8 : BB6.Agent8Section.run BB6CLine.nextC (n-1) (some (5,1,0))=some (a,k,0) := by
    calc
      BB6.Agent8Section.run BB6CLine.nextC (n-1) (some (5,1,0)) =
          BB6.Agent8Section.run BB6CLine.nextC (n-1)
            (BB6.Agent8Section.run BB6CLine.nextC 1 (some (5,0,1))) := by rw [hfirst]
      _ = BB6.Agent8Section.run BB6CLine.nextC (1+(n-1)) (some (5,0,1)) :=
          (sectionRun_add BB6CLine.nextC 1 (n-1) (some (5,0,1))).symm
      _ = BB6.Agent8Section.run BB6CLine.nextC n (some (5,0,1)) :=
          congrArg (fun m => BB6.Agent8Section.run BB6CLine.nextC m (some (5,0,1))) hsplit.symm
      _ = some (a,k,0) := hrun8
  have htail46 : BB6.Agent46.run (n-1) (some (5,1,0))=some (a,k,0) := by
    simpa only [BB6.Agent46.run_eq] using htail8
  have hstart : CReach 5 1 := by
    refine ⟨0, ?_⟩
    rfl
  exact section_returns_preserve_CReach (n-1) 5 1 a k hstart htail46

theorem m32_section_reach_iff {a k : Nat} :
    CReach a k ↔ BB6CLine.Reach (a,k,0) :=
  ⟨m32_section_reach_embeds, m32_section_reach_reflects⟩

#print axioms m32_section_reach_reflects
#print axioms m32_section_reach_iff

end BB6.Agent15