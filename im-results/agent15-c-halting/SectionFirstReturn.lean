import FastSectionHalting
import BounceFirstReturn
import Lean.Elab.Tactic.Omega

namespace BB6.Agent15

open BB6.Agent46

abbrev SectionState := Nat × Nat × Nat

private theorem section_run_step_commute (n : Nat) :
    ∀ s : Option SectionState,
      BB6.Agent46.run n (s.bind BB6CLine.nextC) =
        (BB6.Agent46.run n s).bind BB6CLine.nextC := by
  induction n with
  | zero => intro s; rfl
  | succ n ih =>
      intro s
      change BB6.Agent46.run n ((s.bind BB6CLine.nextC).bind BB6CLine.nextC) =
        (BB6.Agent46.run n (s.bind BB6CLine.nextC)).bind BB6CLine.nextC
      exact ih (s.bind BB6CLine.nextC)

private theorem section_run_add (n m : Nat) (s : Option SectionState) :
    BB6.Agent46.run (n+m) s = BB6.Agent46.run m (BB6.Agent46.run n s) := by
  induction m with
  | zero => simp [BB6.Agent46.run]
  | succ m ih =>
      rw [Nat.add_succ]
      calc
        BB6.Agent46.run (n+m+1) s = BB6.Agent46.run (n+m) (s.bind BB6CLine.nextC) := rfl
        _ = (BB6.Agent46.run (n+m) s).bind BB6CLine.nextC := section_run_step_commute (n+m) s
        _ = (BB6.Agent46.run m (BB6.Agent46.run n s)).bind BB6CLine.nextC :=
          congrArg (fun z => z.bind BB6CLine.nextC) ih
        _ = BB6.Agent46.run m ((BB6.Agent46.run n s).bind BB6CLine.nextC) :=
          (section_run_step_commute m (BB6.Agent46.run n s)).symm
        _ = BB6.Agent46.run (m+1) (BB6.Agent46.run n s) := rfl

private theorem first_high_step (a k : Nat) (ha : 2≤a) (hk : 1≤k) :
    BB6.Agent46.run 1 (some (a,k,0)) = some (a-2,1,2*k+1) := by
  obtain ⟨u,rfl⟩ : ∃ u, a=u+2 := ⟨a-2,by omega⟩
  simp [BB6.Agent46.run, BB6CLine.nextC]

private theorem first_one_step (k : Nat) (hk : 1≤k) :
    BB6.Agent46.run 1 (some (1,k,0)) = some (2,2,2*k-1) := by
  obtain ⟨u,rfl⟩ : ∃ u, k=u+1 := ⟨k-1,by omega⟩
  simp [BB6.Agent46.run, BB6CLine.nextC]
  omega

private theorem run_not_zero_of_pos {n : Nat} {start : Option SectionState} {s : SectionState}
    (hrun : BB6.Agent46.run n start = some s) (hc : 0<s.2.2) :
    ∀ x y, BB6.Agent46.run n start ≠ some (x,y,0) := by
  intro x y hEq
  rw [hrun] at hEq
  have hcEq : s.2.2=0 := by
    injection hEq with hs
    simpa using congrArg (fun z : SectionState => z.2.2) hs
  omega

theorem section_no_early_c0 (a k n : Nat) (hn : 0<n)
    (hlt : n<BB6.Agent46.secTime (a,k)) :
    ∀ x y, BB6.Agent46.run n (some (a,k,0)) ≠ some (x,y,0) := by
  by_cases ha0 : a=0
  · subst a
    by_cases hk0 : k=0
    · subst k
      intro x y
      have hnEq : n=1 := by simp [BB6.Agent46.secTime,BB6.Agent46.exactSection] at hlt; omega
      subst n
      have hrun : BB6.Agent46.run 1 (some (0,0,0))=some (1,0,2) := by simp [BB6.Agent46.run,BB6CLine.nextC]
      exact run_not_zero_of_pos hrun (by change 0<2; omega) x y
    · by_cases hk1 : k=1
      · subst k
        intro x y
        have hcases : n=1 ∨ n=2 ∨ n=3 := by
          have hbound : n<4 := by simpa [BB6.Agent46.secTime,BB6.Agent46.exactSection] using hlt
          omega
        rcases hcases with h1|h2|h3
        · subst n
          have hrun : BB6.Agent46.run 1 (some (0,1,0))=some (1,0,4) := by simp [BB6.Agent46.run,BB6CLine.nextC]
          exact run_not_zero_of_pos hrun (by change 0<4; omega) x y
        · subst n
          have hrun : BB6.Agent46.run 2 (some (0,1,0))=some (0,1,3) := by
            simp [BB6.Agent46.run,BB6CLine.nextC]
          exact run_not_zero_of_pos hrun (by change 0<3; omega) x y
        · subst n
          have hrun : BB6.Agent46.run 3 (some (0,1,0))=some (0,3,1) := by
            simp [BB6.Agent46.run,BB6CLine.nextC]
          exact run_not_zero_of_pos hrun (by change 0<1; omega) x y
      · have hk2 : 2≤k := by omega
        intro x y
        have htime : BB6.Agent46.secTime (0,k)=2+(BB6.Agent46.bounce 1 (2*k+1)).1 := by
          simp [BB6.Agent46.secTime,BB6.Agent46.exactSection,hk0,hk1]
        rw [htime] at hlt
        have hfirst : BB6.Agent46.run 1 (some (0,k,0))=some (1,0,2*k+2) := by simp [BB6.Agent46.run,BB6CLine.nextC]
        have hpre : BB6.Agent46.run 2 (some (0,k,0))=some (0,1,2*k+1) := by
          calc
            BB6.Agent46.run 2 (some (0,k,0)) = BB6.Agent46.run 1 (BB6.Agent46.run 1 (some (0,k,0))) := by simpa using (section_run_add 1 1 (some (0,k,0)))
            _ = BB6.Agent46.run 1 (some (1,0,2*k+2)) := by rw [hfirst]
            _ = some (0,1,2*k+1) := by
              have hcdecomp : 2*k+2=(2*k-2)+4 := by omega
              rw [hcdecomp]
              simp [BB6.Agent46.run,BB6CLine.nextC]
              omega
        by_cases h1 : n=1
        · subst n
          exact run_not_zero_of_pos hfirst (by change 0<2*k+2; omega) x y
        · by_cases h2 : n=2
          · subst n
            exact run_not_zero_of_pos hpre (by change 0<2*k+1; omega) x y
          · have hn3 : 3≤n := by omega
            let j := n-2
            have hj1 : 1≤j := by dsimp [j]; omega
            have hsplit : n=2+j := by dsimp [j]; omega
            have hjlt : j<(BB6.Agent46.bounce 1 (2*k+1)).1 := by
              rw [hsplit] at hlt
              omega
            have htail : BB6.Agent46.run n (some (0,k,0))=BB6.Agent46.run j (some (0,1,2*k+1)) := by
              calc
                BB6.Agent46.run n (some (0,k,0)) = BB6.Agent46.run (2+j) (some (0,k,0)) := congrArg (fun m => BB6.Agent46.run m (some (0,k,0))) hsplit
                _ = BB6.Agent46.run j (BB6.Agent46.run 2 (some (0,k,0))) := by simpa using (section_run_add 2 j (some (0,k,0)))
                _ = BB6.Agent46.run j (some (0,1,2*k+1)) := by rw [hpre]
            intro hEq
            rw [htail] at hEq
            exact bounce_no_early_c0 (2*k+1) (by omega) 1 j hjlt x y hEq
  · by_cases ha1 : a=1
    · subst a
      by_cases hk4 : 4≤k
      · intro x y
        have hk0 : k≠0 := by omega
        have hk1 : k≠1 := by omega
        have hk2 : k≠2 := by omega
        have hk3 : k≠3 := by omega
        have htime : BB6.Agent46.secTime (1,k)=3+(BB6.Agent46.bounce 4 (2*k-3)).1 := by
          simp [BB6.Agent46.secTime,BB6.Agent46.exactSection,ha0,hk0,hk1,hk2,hk3]
        rw [htime] at hlt
        have hfirst := first_one_step k (by omega)
        have htwo : BB6.Agent46.run 2 (some (1,k,0))=some (1,3,2*k-2) := by
          calc
            BB6.Agent46.run 2 (some (1,k,0)) = BB6.Agent46.run 1 (BB6.Agent46.run 1 (some (1,k,0))) := by simpa using (section_run_add 1 1 (some (1,k,0)))
            _ = BB6.Agent46.run 1 (some (2,2,2*k-1)) := by rw [hfirst]
            _ = some (1,3,2*k-2) := by
              have hh := run_high 1 2 2 (2*k-1) (by omega) (by omega)
              exact hh
        have hpre : BB6.Agent46.run 3 (some (1,k,0))=some (0,4,2*k-3) := by
          calc
            BB6.Agent46.run 3 (some (1,k,0)) = BB6.Agent46.run 2 (BB6.Agent46.run 1 (some (1,k,0))) := by simpa using (section_run_add 1 2 (some (1,k,0)))
            _ = BB6.Agent46.run 2 (some (2,2,2*k-1)) := by rw [hfirst]
            _ = some (0,4,2*k-3) := by
              have hh := run_high 2 2 2 (2*k-1) (by omega) (by omega)
              exact hh
        by_cases h1 : n=1
        · subst n
          exact run_not_zero_of_pos hfirst (by change 0<2*k-1; omega) x y
        · by_cases h2 : n=2
          · subst n
            exact run_not_zero_of_pos htwo (by change 0<2*k-2; omega) x y
          · by_cases h3 : n=3
            · subst n
              exact run_not_zero_of_pos hpre (by change 0<2*k-3; omega) x y
            · have hn4 : 4≤n := by omega
              let j := n-3
              have hj1 : 1≤j := by dsimp [j]; omega
              have hsplit : n=3+j := by dsimp [j]; omega
              have hjlt : j<(BB6.Agent46.bounce 4 (2*k-3)).1 := by
                rw [hsplit] at hlt
                omega
              have htail : BB6.Agent46.run n (some (1,k,0))=BB6.Agent46.run j (some (0,4,2*k-3)) := by
                calc
                  BB6.Agent46.run n (some (1,k,0)) = BB6.Agent46.run (3+j) (some (1,k,0)) := congrArg (fun m => BB6.Agent46.run m (some (1,k,0))) hsplit
                  _ = BB6.Agent46.run j (BB6.Agent46.run 3 (some (1,k,0))) := by simpa using (section_run_add 3 j (some (1,k,0)))
                  _ = BB6.Agent46.run j (some (0,4,2*k-3)) := by rw [hpre]
              intro hEq
              rw [htail] at hEq
              exact bounce_no_early_c0 (2*k-3) (by omega) 4 j hjlt x y hEq
      · have hkCases : k=0 ∨ k=1 ∨ k=2 ∨ k=3 := by omega
        intro x y
        rcases hkCases with h0|h1|h2|h3
        · subst k
          have hnEq : n=1 := by simp [BB6.Agent46.secTime,BB6.Agent46.exactSection] at hlt; omega
          subst n
          have hrun : BB6.Agent46.run 1 (some (1,0,0))=some (5,0,1) := by simp [BB6.Agent46.run,BB6CLine.nextC]
          exact run_not_zero_of_pos hrun (by change 0<1; omega) x y
        · subst k
          have hnEq : n=1 := by simp [BB6.Agent46.secTime,BB6.Agent46.exactSection] at hlt; omega
          subst n
          have hrun : BB6.Agent46.run 1 (some (1,1,0))=some (2,2,1) := by simp [BB6.Agent46.run,BB6CLine.nextC]
          exact run_not_zero_of_pos hrun (by change 0<1; omega) x y
        · subst k
          have hcases : n=1 ∨ n=2 := by
            have hbound : n<3 := by simpa [BB6.Agent46.secTime,BB6.Agent46.exactSection] using hlt
            omega
          rcases hcases with h1|h2
          · subst n
            have hrun : BB6.Agent46.run 1 (some (1,2,0))=some (2,2,3) := by simp [BB6.Agent46.run,BB6CLine.nextC]
            exact run_not_zero_of_pos hrun (by change 0<3; omega) x y
          · subst n
            have hrun : BB6.Agent46.run 2 (some (1,2,0))=some (2,4,1) := by simp [BB6.Agent46.run,BB6CLine.nextC]
            exact run_not_zero_of_pos hrun (by change 0<1; omega) x y
        · subst k
          have hcases : n=1 ∨ n=2 ∨ n=3 ∨ n=4 := by
            have hbound : n<5 := by simpa [BB6.Agent46.secTime,BB6.Agent46.exactSection] using hlt
            omega
          rcases hcases with h1|h2|h3|h4
          · subst n
            have hrun : BB6.Agent46.run 1 (some (1,3,0))=some (2,2,5) := by simp [BB6.Agent46.run,BB6CLine.nextC]
            exact run_not_zero_of_pos hrun (by change 0<5; omega) x y
          · subst n
            have hrun : BB6.Agent46.run 2 (some (1,3,0))=some (1,3,4) := by simp [BB6.Agent46.run,BB6CLine.nextC]
            exact run_not_zero_of_pos hrun (by change 0<4; omega) x y
          · subst n
            have hrun : BB6.Agent46.run 3 (some (1,3,0))=some (0,4,3) := by simp [BB6.Agent46.run,BB6CLine.nextC]
            exact run_not_zero_of_pos hrun (by change 0<3; omega) x y
          · subst n
            have hrun : BB6.Agent46.run 4 (some (1,3,0))=some (0,6,1) := by simp [BB6.Agent46.run,BB6CLine.nextC]
            exact run_not_zero_of_pos hrun (by change 0<1; omega) x y
    · have ha2 : 2≤a := by omega
      by_cases hk0 : k=0
      · subst k
        intro x y
        have hnEq : n=1 := by simp [BB6.Agent46.secTime,BB6.Agent46.exactSection,ha0,ha1] at hlt; omega
        subst n
        have hrun : BB6.Agent46.run 1 (some (a,0,0))=some (a-2,1,1) := by
          obtain ⟨u,rfl⟩ : ∃u, a=u+2 := ⟨a-2,by omega⟩
          simp [BB6.Agent46.run,BB6CLine.nextC]
        exact run_not_zero_of_pos hrun (by change 0<1; omega) x y
      · have hkpos : 1≤k := by omega
        by_cases hdom : 2*k≤a
        · by_cases hk1 : k=1
          · subst k
            intro x y
            have hcases : n=1 ∨ n=2 := by
              have hbound : n<3 := by simpa [BB6.Agent46.secTime,BB6.Agent46.exactSection,ha0,ha1,hk0,hdom] using hlt
              omega
            rcases hcases with h1|h2
            · subst n
              have hrun := first_high_step a 1 ha2 (by omega)
              exact run_not_zero_of_pos hrun (by change 0<3; omega) x y
            · subst n
              have hfirst := first_high_step a 1 ha2 (by omega)
              have hrun : BB6.Agent46.run 2 (some (a,1,0))=some (a-2,3,1) := by
                calc
                  BB6.Agent46.run 2 (some (a,1,0)) = BB6.Agent46.run 1 (BB6.Agent46.run 1 (some (a,1,0))) := by simpa using (section_run_add 1 1 (some (a,1,0)))
                  _ = BB6.Agent46.run 1 (some (a-2,1,3)) := by rw [hfirst]
                  _ = some (a-2,3,1) := by simp [BB6.Agent46.run,BB6CLine.nextC]
              exact run_not_zero_of_pos hrun (by change 0<1; omega) x y
          · have hk2 : 2≤k := by omega
            intro x y
            have hfirst := first_high_step a k ha2 hkpos
            have hlt' : n<2*k+1 := by simpa [BB6.Agent46.secTime,BB6.Agent46.exactSection,ha0,ha1,hk0,hdom] using hlt
            by_cases hlast : n=2*k
            · subst n
              have hmid : BB6.Agent46.run (2*k-2) (some (a-2,1,2*k+1))=some (a-2*k,2*k-1,3) := by
                have hh := run_high (2*k-2) (a-2) 1 (2*k+1) (by omega) (by omega)
                have hA : a-2-(2*k-2)=a-2*k := by omega
                have hK : 1+(2*k-2)=2*k-1 := by omega
                have hC : 2*k+1-(2*k-2)=3 := by omega
                simpa [hA,hK,hC] using hh
              have hnum : 2*k=1+(2*k-2)+1 := by omega
              have hrun : BB6.Agent46.run (2*k) (some (a,k,0))=some (a-2*k,2*k+1,1) := by
                calc
                  BB6.Agent46.run (2*k) (some (a,k,0)) = BB6.Agent46.run ((1+(2*k-2))+1) (some (a,k,0)) := congrArg (fun m => BB6.Agent46.run m (some (a,k,0))) hnum
                  _ = BB6.Agent46.run 1 (BB6.Agent46.run (1+(2*k-2)) (some (a,k,0))) := by simpa using (section_run_add (1+(2*k-2)) 1 (some (a,k,0)))
                  _ = BB6.Agent46.run 1 (BB6.Agent46.run (2*k-2) (BB6.Agent46.run 1 (some (a,k,0)))) := by simpa using congrArg (fun z => BB6.Agent46.run 1 z) (section_run_add 1 (2*k-2) (some (a,k,0)))
                  _ = BB6.Agent46.run 1 (BB6.Agent46.run (2*k-2) (some (a-2,1,2*k+1))) := by rw [hfirst]
                  _ = BB6.Agent46.run 1 (some (a-2*k,2*k-1,3)) := by rw [hmid]
                  _ = some (a-2*k,2*k+1,1) := by simp [BB6.Agent46.run,BB6CLine.nextC]; omega
              exact run_not_zero_of_pos hrun (by change 0<1; omega) x y
            · have hbound : n≤2*k-1 := by omega
              have hrun : BB6.Agent46.run n (some (a,k,0))=
                  some (a-2-(n-1),1+(n-1),2*k+1-(n-1)) := by
                have hfirst := first_high_step a k ha2 hkpos
                have hhigh := run_high (n-1) (a-2) 1 (2*k+1) (by omega) (by omega)
                calc
                  BB6.Agent46.run n (some (a,k,0)) = BB6.Agent46.run (1+(n-1)) (some (a,k,0)) := congrArg (fun m => BB6.Agent46.run m (some (a,k,0))) (by omega)
                  _ = BB6.Agent46.run (n-1) (BB6.Agent46.run 1 (some (a,k,0))) := by simpa using (section_run_add 1 (n-1) (some (a,k,0)))
                  _ = BB6.Agent46.run (n-1) (some (a-2,1,2*k+1)) := by rw [hfirst]
                  _ = some (a-2-(n-1),1+(n-1),2*k+1-(n-1)) := hhigh
              exact run_not_zero_of_pos hrun (by change 0<2*k+1-(n-1); omega) x y
        · have hnon : a<2*k := by omega
          intro x y
          have hdom' : ¬2*k≤a := by omega
          have htime : BB6.Agent46.secTime (a,k)=(a-1)+(BB6.Agent46.bounce (a-1) (2*k-a+3)).1 := by
            simp [BB6.Agent46.secTime,BB6.Agent46.exactSection,ha0,ha1,hk0,hdom']
          rw [htime] at hlt
          have hfirst := first_high_step a k ha2 hkpos
          have hhigh : BB6.Agent46.run (a-2) (some (a-2,1,2*k+1))=some (0,a-1,2*k-a+3) := by
            have hh := run_high (a-2) (a-2) 1 (2*k+1) (by omega) (by omega)
            have hK : 1+(a-2)=a-1 := by omega
            have hC : 2*k+1-(a-2)=2*k-a+3 := by omega
            simpa [hK,hC] using hh
          have hpre : BB6.Agent46.run (a-1) (some (a,k,0))=some (0,a-1,2*k-a+3) := by
            calc
              BB6.Agent46.run (a-1) (some (a,k,0)) = BB6.Agent46.run (1+(a-2)) (some (a,k,0)) := congrArg (fun m => BB6.Agent46.run m (some (a,k,0))) (by omega)
              _ = BB6.Agent46.run (a-2) (BB6.Agent46.run 1 (some (a,k,0))) := by simpa using (section_run_add 1 (a-2) (some (a,k,0)))
              _ = BB6.Agent46.run (a-2) (some (a-2,1,2*k+1)) := by rw [hfirst]
              _ = some (0,a-1,2*k-a+3) := hhigh
          by_cases hshort : n≤a-1
          · have hrun : BB6.Agent46.run n (some (a,k,0))=
                some (a-2-(n-1),1+(n-1),2*k+1-(n-1)) := by
              have hhigh' := run_high (n-1) (a-2) 1 (2*k+1) (by omega) (by omega)
              calc
                BB6.Agent46.run n (some (a,k,0)) = BB6.Agent46.run (1+(n-1)) (some (a,k,0)) := congrArg (fun m => BB6.Agent46.run m (some (a,k,0))) (by omega)
                _ = BB6.Agent46.run (n-1) (BB6.Agent46.run 1 (some (a,k,0))) := by simpa using (section_run_add 1 (n-1) (some (a,k,0)))
                _ = BB6.Agent46.run (n-1) (some (a-2,1,2*k+1)) := by rw [hfirst]
                _ = some (a-2-(n-1),1+(n-1),2*k+1-(n-1)) := hhigh'
            exact run_not_zero_of_pos hrun (by change 0<2*k+1-(n-1); omega) x y
          · let j := n-(a-1)
            have hj1 : 1≤j := by dsimp [j]; omega
            have hsplit : n=(a-1)+j := by dsimp [j]; omega
            have hjlt : j<(BB6.Agent46.bounce (a-1) (2*k-a+3)).1 := by
              rw [hsplit] at hlt
              omega
            have htail : BB6.Agent46.run n (some (a,k,0))=BB6.Agent46.run j (some (0,a-1,2*k-a+3)) := by
              calc
                BB6.Agent46.run n (some (a,k,0)) = BB6.Agent46.run ((a-1)+j) (some (a,k,0)) := congrArg (fun m => BB6.Agent46.run m (some (a,k,0))) hsplit
                _ = BB6.Agent46.run j (BB6.Agent46.run (a-1) (some (a,k,0))) := by simpa using (section_run_add (a-1) j (some (a,k,0)))
                _ = BB6.Agent46.run j (some (0,a-1,2*k-a+3)) := by rw [hpre]
            intro hEq
            rw [htail] at hEq
            exact bounce_no_early_c0 (2*k-a+3) (by omega) (a-1) j hjlt x y hEq


#print axioms section_no_early_c0

end BB6.Agent15