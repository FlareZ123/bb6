import FastSectionProof

namespace BB6.Agent15

open BB6.Agent46

private theorem run_step_commute (n : Nat) :
    ∀ s : Option (Nat × Nat × Nat),
      run n (s.bind BB6CLine.nextC) = (run n s).bind BB6CLine.nextC := by
  induction n with
  | zero =>
      intro s
      rfl
  | succ n ih =>
      intro s
      simp [run, ih]

private theorem run_add (n m : Nat) :
    ∀ s : Option (Nat × Nat × Nat),
      run (n+m) s = run m (run n s) := by
  induction m with
  | zero =>
      intro s
      simp [run]
  | succ m ih =>
      intro s
      rw [Nat.add_succ]
      change run (n+m) (s.bind BB6CLine.nextC) =
        run m ((run n s).bind BB6CLine.nextC)
      rw [ih]
      rw [run_step_commute n s]

private theorem run_odd_prefix (k c t : Nat)
    (hodd : k%2=1) (hc : 4≤c)
    (ht : t≤2*k+3) (htc : t+3≤c) :
    run (t+1) (some (0,k,c)) =
      some (2*k+3-t,t,c-t) := by
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le' hc
  have hstep :
      (some (0,k,d+4) : Option (Nat × Nat × Nat)).bind BB6CLine.nextC =
        some (2*k+3,0,d+4) := by
    simp [BB6CLine.nextC, hodd]
    omega
  change run t ((some (0,k,d+4)).bind BB6CLine.nextC) =
    some (2*k+3-t,t,(d+4)-t)
  rw [hstep]
  simpa using run_high t (2*k+3) 0 (d+4) ht htc

private theorem run_even_prefix (k c t : Nat)
    (heven : k%2=0) (hc : 4≤c)
    (ht : t≤2*k+2) (htc : t+3≤c-3) :
    run (t+1) (some (0,k,c)) =
      some (2*k+2-t,2+t,c-3-t) := by
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le' hc
  have hstep :
      (some (0,k,d+4) : Option (Nat × Nat × Nat)).bind BB6CLine.nextC =
        some (2*k+2,2,d+1) := by
    simp [BB6CLine.nextC, heven]
    omega
  change run t ((some (0,k,d+4)).bind BB6CLine.nextC) =
    some (2*k+2-t,2+t,(d+1)-t)
  rw [hstep]
  simpa using run_high t (2*k+2) 2 (d+1) ht htc

/-- Before the certified bounce time, the original CLine path has not
returned to the c=0 section. This is the minimality property missing from
the generic section-halting argument. -/
theorem bounce_no_early_c0 :
    ∀ c, 4≤c → ∀ k n, n < (bounce k c).1 →
      ∀ a b, run n (some (0,k,c)) ≠ some (a,b,0) := by
  intro c
  refine Nat.strongRecOn c ?_
  intro c ih
  intro hc k n hn a b
      by_cases hodd : k%2=1
      · by_cases hsmall : c≤2*k+6
        · have hnlt : n<c := by
            simpa [bounce, Nat.not_lt.mpr hc, hodd, hsmall] using hn
          by_cases hn0 : n=0
          · subst n
            intro hEq
            simp [run] at hEq
            simp only [Prod.mk.injEq] at hEq
            omega
          · by_cases hlast : n=c-1
            · have hbound : c-3≤2*k+3 := by omega
              have hpre0 := odd_bounce_to_three k c hodd hc hbound
              have hnum : c-2 = 1+(c-3) := by omega
              have hpre : run (c-2) (some (0,k,c)) =
                  some (2*k+3-(c-3),c-3,3) := by
                rw [hnum]
                exact hpre0
              have hrun : run n (some (0,k,c)) =
                  some (2*k+3-(c-3),c-3+2,1) := by
                rw [hlast, show c-1=(c-2)+1 by omega, run_add, hpre]
                simp [run, BB6CLine.nextC]
              intro hEq
              rw [hrun] at hEq
              simp only [Option.some.injEq, Prod.mk.injEq] at hEq
              omega
            · have hnle : n≤c-2 := by omega
              have ht : n-1≤2*k+3 := by omega
              have htc : n-1+3≤c := by omega
              have hpre := run_odd_prefix k c (n-1) hodd hc ht htc
              have hrun : run n (some (0,k,c)) =
                  some (2*k+3-(n-1),n-1,c-(n-1)) := by
                simpa [show n=(n-1)+1 by omega] using hpre
              intro hEq
              rw [hrun] at hEq
              simp only [Option.some.injEq, Prod.mk.injEq] at hEq
              omega
        · have hlarge : 2*k+6<c := by omega
          have hnlt : n < 2*k+4 + (bounce (2*k+3) (c-(2*k+3))).1 := by
            simpa [bounce, Nat.not_lt.mpr hc, hodd, hlarge] using hn
          by_cases hprefix : n<2*k+4
          · by_cases hn0 : n=0
            · subst n
              intro hEq
              simp [run] at hEq
              simp only [Prod.mk.injEq] at hEq
              omega
            · have ht : n-1≤2*k+3 := by omega
              have htc : n-1+3≤c := by omega
              have hpre := run_odd_prefix k c (n-1) hodd hc ht htc
              have hrun : run n (some (0,k,c)) =
                  some (2*k+3-(n-1),n-1,c-(n-1)) := by
                simpa [show n=(n-1)+1 by omega] using hpre
              intro hEq
              rw [hrun] at hEq
              simp only [Option.some.injEq, Prod.mk.injEq] at hEq
              omega
          · have hprefix_le : 2*k+4≤n := by omega
            let n' := n-(2*k+4)
            have hnEq : n=(2*k+4)+n' := by
              dsimp [n']
              omega
            have hnrec : n' < (bounce (2*k+3) (c-(2*k+3))).1 := by
              dsimp [n']
              omega
            have hc' : 4≤c-(2*k+3) := by omega
            have hpre := odd_zero_continue k c hodd hlarge
            have hrun : run n (some (0,k,c)) =
                run n' (some (0,2*k+3,c-(2*k+3))) := by
              rw [hnEq, run_add, hpre]
            intro hEq
            rw [hrun] at hEq
            exact ih (c-(2*k+3)) (by omega) hc' (2*k+3) n' hnrec a b hEq
      · have heven : k%2=0 := by omega
        by_cases hc4 : c=4
        · have hnlt : n<2 := by
            subst c
            simpa [bounce, heven] using hn
          have hncase : n=0 ∨ n=1 := by omega
          rcases hncase with hn0 | hn1
          · subst n
            intro hEq
            simp [run] at hEq
            simp only [Prod.mk.injEq] at hEq
            omega
          · subst n
            intro hEq
            subst c
            simp [run, BB6CLine.nextC, heven] at hEq
        · by_cases hc5 : c=5
          · have hnlt : n<2 := by
              subst c
              simpa [bounce, heven] using hn
            have hncase : n=0 ∨ n=1 := by omega
            rcases hncase with hn0 | hn1
            · subst n
              intro hEq
              simp [run] at hEq
              simp only [Prod.mk.injEq] at hEq
              omega
            · subst n
              intro hEq
              subst c
              simp [run, BB6CLine.nextC, heven] at hEq
          · have hc6 : 6≤c := by omega
            by_cases hsmall : c≤2*k+8
            · have hnlt : n<c-3 := by
                simpa [bounce, Nat.not_lt.mpr hc, heven, hc6, hsmall] using hn
              by_cases hn0 : n=0
              · subst n
                intro hEq
                simp [run] at hEq
                simp only [Prod.mk.injEq] at hEq
                omega
              · by_cases hlast : n=c-4
                · have hbound : c-6≤2*k+2 := by omega
                  have hpre0 := even_bounce_to_three k c heven hc6 hbound
                  have hnum : c-5 = 1+(c-6) := by omega
                  have hpre : run (c-5) (some (0,k,c)) =
                      some (2*k+2-(c-6),2+(c-6),3) := by
                    rw [hnum]
                    exact hpre0
                  have hrun : run n (some (0,k,c)) =
                      some (2*k+2-(c-6),2+(c-6)+2,1) := by
                    rw [hlast, show c-4=(c-5)+1 by omega, run_add, hpre]
                    simp [run, BB6CLine.nextC]
                  intro hEq
                  rw [hrun] at hEq
                  simp only [Option.some.injEq, Prod.mk.injEq] at hEq
                  omega
                · have hnle : n≤c-5 := by omega
                  have ht : n-1≤2*k+2 := by omega
                  have htc : n-1+3≤c-3 := by omega
                  have hpre := run_even_prefix k c (n-1) heven hc ht htc
                  have hrun : run n (some (0,k,c)) =
                      some (2*k+2-(n-1),2+(n-1),c-3-(n-1)) := by
                    simpa [show n=(n-1)+1 by omega] using hpre
                  intro hEq
                  rw [hrun] at hEq
                  simp only [Option.some.injEq, Prod.mk.injEq] at hEq
                  omega
            · have hlarge : 2*k+8<c := by omega
              have hnlt : n < 2*k+3 + (bounce (2*k+4) (c-(2*k+5))).1 := by
                simpa [bounce, Nat.not_lt.mpr hc, heven, hc6, hlarge] using hn
              by_cases hprefix : n<2*k+3
              · by_cases hn0 : n=0
                · subst n
                  intro hEq
                  simp [run] at hEq
                  simp only [Prod.mk.injEq] at hEq
                  omega
                · have ht : n-1≤2*k+2 := by omega
                  have htc : n-1+3≤c-3 := by omega
                  have hpre := run_even_prefix k c (n-1) heven hc ht htc
                  have hrun : run n (some (0,k,c)) =
                      some (2*k+2-(n-1),2+(n-1),c-3-(n-1)) := by
                    simpa [show n=(n-1)+1 by omega] using hpre
                  intro hEq
                  rw [hrun] at hEq
                  simp only [Option.some.injEq, Prod.mk.injEq] at hEq
                  omega
              · have hprefix_le : 2*k+3≤n := by omega
                let n' := n-(2*k+3)
                have hnEq : n=(2*k+3)+n' := by
                  dsimp [n']
                  omega
                have hnrec : n' < (bounce (2*k+4) (c-(2*k+5))).1 := by
                  dsimp [n']
                  omega
                have hc' : 4≤c-(2*k+5) := by omega
                have hpre := even_zero_continue k c heven hlarge
                have hrun : run n (some (0,k,c)) =
                    run n' (some (0,2*k+4,c-(2*k+5))) := by
                  rw [hnEq, run_add, hpre]
                intro hEq
                rw [hrun] at hEq
                exact ih (c-(2*k+5)) (by omega) hc' (2*k+4) n' hnrec a b hEq

#print axioms bounce_no_early_c0

end BB6.Agent15
