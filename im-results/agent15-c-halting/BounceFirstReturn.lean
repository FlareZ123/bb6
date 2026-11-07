import FastSectionHalting
import Lean.Elab.Tactic.Omega

namespace BB6.Agent15

open BB6.Agent46

abbrev CState := Nat × Nat × Nat

private theorem run_step_commute (n : Nat) : ∀ s : Option CState,
    BB6.Agent46.run n (s.bind BB6CLine.nextC) = (BB6.Agent46.run n s).bind BB6CLine.nextC := by
  induction n with
  | zero => intro s; rfl
  | succ n ih =>
      intro s
      change BB6.Agent46.run n ((s.bind BB6CLine.nextC).bind BB6CLine.nextC) = (BB6.Agent46.run n (s.bind BB6CLine.nextC)).bind BB6CLine.nextC
      exact ih (s.bind BB6CLine.nextC)

private theorem run_add (n m : Nat) (s : Option CState) :
    BB6.Agent46.run (n+m) s = BB6.Agent46.run m (BB6.Agent46.run n s) := by
  induction m with
  | zero => rfl
  | succ m ih =>
      rw [Nat.add_succ]
      calc
        BB6.Agent46.run (n+m+1) s = BB6.Agent46.run (n+m) (s.bind BB6CLine.nextC) := rfl
        _ = (BB6.Agent46.run (n+m) s).bind BB6CLine.nextC := run_step_commute (n+m) s
        _ = (BB6.Agent46.run m (BB6.Agent46.run n s)).bind BB6CLine.nextC := congrArg (fun z => z.bind BB6CLine.nextC) ih
        _ = BB6.Agent46.run m ((BB6.Agent46.run n s).bind BB6CLine.nextC) := (run_step_commute m (BB6.Agent46.run n s)).symm
        _ = BB6.Agent46.run (m+1) (BB6.Agent46.run n s) := rfl

private theorem high_odd_bounce (k c : Nat) (hk : k%2=1) (hc : 4≤c) :
    BB6CLine.nextC (0,k,c) = some (2*k+3,0,c) := by
  obtain ⟨d, rfl⟩ : ∃ d, c=d+4 := ⟨c-4,by omega⟩
  change (if k%2=0 then some (4*(k/2)+2,2,d+1)
      else some (4*(k/2)+5,0,d+4)) = some (2*k+3,0,d+4)
  have hne : k%2≠0 := by omega
  have hdiv : k%2 + 2*(k/2) = k := Nat.mod_add_div k 2
  simp only [hne, ite_false, Option.some.injEq, Prod.mk.injEq]
  constructor
  · omega
  · trivial

private theorem high_even_bounce (k c : Nat) (hk : k%2=0) (hc : 4≤c) :
    BB6CLine.nextC (0,k,c) = some (2*k+2,2,c-3) := by
  obtain ⟨d, rfl⟩ : ∃ d, c=d+4 := ⟨c-4,by omega⟩
  change (if k%2=0 then some (4*(k/2)+2,2,d+1)
      else some (4*(k/2)+5,0,d+4)) = some (2*k+2,2,(d+4)-3)
  have hdiv : k%2 + 2*(k/2) = k := Nat.mod_add_div k 2
  simp only [hk, ite_true, Option.some.injEq, Prod.mk.injEq]
  constructor
  · omega
  · constructor
    · trivial
    · omega

def BouncePrefix (n k c : Nat) : Prop :=
  ∀ i, 1 ≤ i → i < n →
    ∃ s, BB6.Agent46.run i (some (0,k,c)) = some s ∧ 0 < s.2.2

private theorem odd_exit_prefix (k c i : Nat) (hk : k%2=1)
    (hc : 4≤c) (hsmall : c≤2*k+6) (hi1 : 1≤i) (hi : i<c) :
    ∃ s, BB6.Agent46.run i (some (0,k,c)) = some s ∧ 0<s.2.2 := by
  have hkEq : k=2*(k/2)+1 := by omega
  by_cases hlast : i=c-1
  · have hbound : c-3≤2*k+3 := by omega
    have hb := odd_bounce_to_three k c hk hc hbound
    have hnum : i=(1+(c-3))+1 := by omega
    refine ⟨(2*k+3-(c-3),c-3+2,1), ?_, ?_⟩
    · calc
      BB6.Agent46.run i (some (0,k,c)) = BB6.Agent46.run ((1+(c-3))+1) (some (0,k,c)) := congrArg (fun n => BB6.Agent46.run n (some (0,k,c))) hnum
      _ = BB6.Agent46.run 1 (BB6.Agent46.run (1+(c-3)) (some (0,k,c))) := run_add _ _ _
      _ = BB6.Agent46.run 1 (some (2*k+3-(c-3),c-3,3)) := by rw [hb]
      _ = some (2*k+3-(c-3),c-3+2,1) := by simp [BB6.Agent46.run,BB6CLine.nextC]
    · change 0 < 1
      omega
  · have hi2 : i≤c-2 := by omega
    have hfirst : BB6.Agent46.run 1 (some (0,k,c)) = some (2*k+3,0,c) := by
      simp [BB6.Agent46.run,high_odd_bounce k c hk hc]
    have hiA : i-1≤2*k+3 := by omega
    have hiC : (i-1)+3≤c := by omega
    have hh := run_high (i-1) (2*k+3) 0 c hiA hiC
    have hnum : i=1+(i-1) := by omega
    refine ⟨(2*k+3-(i-1),i-1,c-(i-1)), ?_, ?_⟩
    · calc
      BB6.Agent46.run i (some (0,k,c)) = BB6.Agent46.run (1+(i-1)) (some (0,k,c)) := congrArg (fun n => BB6.Agent46.run n (some (0,k,c))) hnum
      _ = BB6.Agent46.run (i-1) (BB6.Agent46.run 1 (some (0,k,c))) := run_add _ _ _
      _ = BB6.Agent46.run (i-1) (some (2*k+3,0,c)) := by rw [hfirst]
      _ = some (2*k+3-(i-1),i-1,c-(i-1)) := by simpa [Nat.zero_add] using hh
    · change 0 < c-(i-1)
      omega

private theorem even_exit_prefix (k c i : Nat) (hk : k%2=0)
    (hc : 6≤c) (hsmall : c≤2*k+8) (hi1 : 1≤i) (hi : i<c-3) :
    ∃ s, BB6.Agent46.run i (some (0,k,c)) = some s ∧ 0<s.2.2 := by
  have hkEq : k=2*(k/2) := by omega
  by_cases hlast : i=c-4
  · have hbound : c-6≤2*k+2 := by omega
    have hb := even_bounce_to_three k c hk hc hbound
    have hnum : i=(1+(c-6))+1 := by omega
    refine ⟨(2*k+2-(c-6),2+(c-6)+2,1), ?_, ?_⟩
    · calc
      BB6.Agent46.run i (some (0,k,c)) = BB6.Agent46.run ((1+(c-6))+1) (some (0,k,c)) := congrArg (fun n => BB6.Agent46.run n (some (0,k,c))) hnum
      _ = BB6.Agent46.run 1 (BB6.Agent46.run (1+(c-6)) (some (0,k,c))) := run_add _ _ _
      _ = BB6.Agent46.run 1 (some (2*k+2-(c-6),2+(c-6),3)) := by rw [hb]
      _ = some (2*k+2-(c-6),2+(c-6)+2,1) := by simp [BB6.Agent46.run,BB6CLine.nextC]
    · change 0 < 1
      omega
  · have hi2 : i≤c-5 := by omega
    have hfirst : BB6.Agent46.run 1 (some (0,k,c)) = some (2*k+2,2,c-3) := by
      simp [BB6.Agent46.run,high_even_bounce k c hk (by omega)]
    have hiA : i-1≤2*k+2 := by omega
    have hiC : (i-1)+3≤c-3 := by omega
    have hh := run_high (i-1) (2*k+2) 2 (c-3) hiA hiC
    have hnum : i=1+(i-1) := by omega
    refine ⟨(2*k+2-(i-1),2+(i-1),c-3-(i-1)), ?_, ?_⟩
    · calc
      BB6.Agent46.run i (some (0,k,c)) = BB6.Agent46.run (1+(i-1)) (some (0,k,c)) := congrArg (fun n => BB6.Agent46.run n (some (0,k,c))) hnum
      _ = BB6.Agent46.run (i-1) (BB6.Agent46.run 1 (some (0,k,c))) := run_add _ _ _
      _ = BB6.Agent46.run (i-1) (some (2*k+2,2,c-3)) := by rw [hfirst]
      _ = some (2*k+2-(i-1),2+(i-1),c-3-(i-1)) := hh
    · change 0 < c-3-(i-1)
      omega

private theorem odd_continue_prefix (k c i : Nat) (hk : k%2=1)
    (hc : 4≤c) (hlarge : 2*k+6<c) (hi1 : 1≤i) (hi : i≤2*k+4) :
    ∃ s, BB6.Agent46.run i (some (0,k,c)) = some s ∧ 0<s.2.2 := by
  have hkEq : k=2*(k/2)+1 := by omega
  by_cases hiEq : i=1
  · subst i
    refine ⟨(2*k+3,0,c), ?_, ?_⟩
    · simp [BB6.Agent46.run,high_odd_bounce k c hk hc]
    · change 0 < c
      omega
  · have hi2 : 2≤i := by omega
    have hiA : i-1≤2*k+3 := by omega
    have hiC : (i-1)+3≤c := by omega
    have hh := run_high (i-1) (2*k+3) 0 c hiA hiC
    have hfirst : BB6.Agent46.run 1 (some (0,k,c)) = some (2*k+3,0,c) := by
      simp [BB6.Agent46.run,high_odd_bounce k c hk hc]
    have hnum : i=1+(i-1) := by omega
    refine ⟨(2*k+3-(i-1),i-1,c-(i-1)), ?_, ?_⟩
    · calc
      BB6.Agent46.run i (some (0,k,c)) = BB6.Agent46.run (1+(i-1)) (some (0,k,c)) := congrArg (fun n => BB6.Agent46.run n (some (0,k,c))) hnum
      _ = BB6.Agent46.run (i-1) (BB6.Agent46.run 1 (some (0,k,c))) := run_add _ _ _
      _ = BB6.Agent46.run (i-1) (some (2*k+3,0,c)) := by rw [hfirst]
      _ = some (2*k+3-(i-1),i-1,c-(i-1)) := by simpa [Nat.zero_add] using hh
    · change 0 < c-(i-1)
      omega

private theorem even_continue_prefix (k c i : Nat) (hk : k%2=0)
    (hc : 4≤c) (hlarge : 2*k+8<c) (hi1 : 1≤i) (hi : i≤2*k+3) :
    ∃ s, BB6.Agent46.run i (some (0,k,c)) = some s ∧ 0<s.2.2 := by
  have hkEq : k=2*(k/2) := by omega
  by_cases hiEq : i=1
  · subst i
    refine ⟨(2*k+2,2,c-3), ?_, ?_⟩
    · simp [BB6.Agent46.run,high_even_bounce k c hk hc]
    · change 0 < c-3
      omega
  · have hi2 : 2≤i := by omega
    have hiA : i-1≤2*k+2 := by omega
    have hiC : (i-1)+3≤c-3 := by omega
    have hh := run_high (i-1) (2*k+2) 2 (c-3) hiA hiC
    have hfirst : BB6.Agent46.run 1 (some (0,k,c)) = some (2*k+2,2,c-3) := by
      simp [BB6.Agent46.run,high_even_bounce k c hk hc]
    have hnum : i=1+(i-1) := by omega
    refine ⟨(2*k+2-(i-1),2+(i-1),c-3-(i-1)), ?_, ?_⟩
    · calc
      BB6.Agent46.run i (some (0,k,c)) = BB6.Agent46.run (1+(i-1)) (some (0,k,c)) := congrArg (fun n => BB6.Agent46.run n (some (0,k,c))) hnum
      _ = BB6.Agent46.run (i-1) (BB6.Agent46.run 1 (some (0,k,c))) := run_add _ _ _
      _ = BB6.Agent46.run (i-1) (some (2*k+2,2,c-3)) := by rw [hfirst]
      _ = some (2*k+2-(i-1),2+(i-1),c-3-(i-1)) := hh
    · change 0 < c-3-(i-1)
      omega

theorem bounce_prefix (c : Nat) : ∀ k : Nat, 4≤c → BouncePrefix (BB6.Agent46.bounce k c).1 k c := by
  induction c using Nat.strongRecOn with
  | ind c ih =>
    intro k hc i hi1 hiLt
    rw [BB6.Agent46.bounce.eq_1] at hiLt
    have hnot : ¬c<4 := by omega
    simp only [hnot,ite_false] at hiLt
    by_cases ho : k%2=1
    · simp only [ho,ite_true] at hiLt
      by_cases hs : c≤2*k+6
      · simp only [hs,ite_true] at hiLt ⊢
        exact odd_exit_prefix k c i ho hc hs hi1 hiLt
      · simp only [hs,ite_false] at hiLt ⊢
        have hlarge : 2*k+6<c := by omega
        let m := 2*k+4
        let c' := c-(2*k+3)
        have hsmall : c'<c := Nat.sub_lt (by omega) (by omega)
        have hc' : 4≤c' := by omega
        change i < m + (BB6.Agent46.bounce (2*k+3) c').1 at hiLt
        by_cases hshort : i≤m
        · exact odd_continue_prefix k c i ho hc hlarge hi1 (by omega)
        · have hj1 : 1≤i-m := by omega
          have hjlt : i-m < (BB6.Agent46.bounce (2*k+3) c').1 := by omega
          have hpre := odd_zero_continue k c ho hlarge
          have hrec := ih c' hsmall (2*k+3) hc' (i-m) hj1 hjlt
          have hsplit : i=m+(i-m) := by omega
          obtain ⟨s,hsrun,hsc⟩ := hrec
          refine ⟨s, ?_, hsc⟩
          rw [hsplit,run_add,hpre]
          exact hsrun
    · simp only [ho,ite_false] at hiLt
      have he : k%2=0 := by omega
      by_cases hc4 : c=4
      · simp only [hc4,ite_true] at hiLt ⊢
        have hiEq : i=1 := by omega
        subst i
        refine ⟨(2*k+2,2,1), ?_, ?_⟩
        · simp [BB6.Agent46.run,high_even_bounce k 4 he (by omega)]
        · change 0 < 1
          omega
      · simp only [hc4,ite_false] at hiLt
        by_cases hc5 : c=5
        · simp only [hc5,ite_true] at hiLt ⊢
          have hiEq : i=1 := by omega
          subst i
          refine ⟨(2*k+2,2,2), ?_, ?_⟩
          · simp [BB6.Agent46.run,high_even_bounce k 5 he (by omega)]
          · change 0 < 2
            omega
        · simp only [hc5,ite_false] at hiLt
          by_cases hs : c≤2*k+8
          · simp only [hs,ite_true] at hiLt ⊢
            exact even_exit_prefix k c i he (by omega) hs hi1 hiLt
          · simp only [hs,ite_false] at hiLt ⊢
            have hlarge : 2*k+8<c := by omega
            let m := 2*k+3
            let c' := c-(2*k+5)
            have hsmall : c'<c := Nat.sub_lt (by omega) (by omega)
            have hc' : 4≤c' := by omega
            change i < m + (BB6.Agent46.bounce (2*k+4) c').1 at hiLt
            by_cases hshort : i≤m
            · exact even_continue_prefix k c i he hc hlarge hi1 (by omega)
            · have hj1 : 1≤i-m := by omega
              have hjlt : i-m < (BB6.Agent46.bounce (2*k+4) c').1 := by omega
              have hpre := even_zero_continue k c he hlarge
              have hrec := ih c' hsmall (2*k+4) hc' (i-m) hj1 hjlt
              have hsplit : i=m+(i-m) := by omega
              obtain ⟨s,hsrun,hsc⟩ := hrec
              refine ⟨s, ?_, hsc⟩
              rw [hsplit,run_add,hpre]
              exact hsrun


theorem bounce_no_early_c0 (c : Nat) (hc : 4≤c) (k n : Nat)
    (hn : n<(BB6.Agent46.bounce k c).1) :
    ∀ a b, BB6.Agent46.run n (some (0,k,c)) ≠ some (a,b,0) := by
  intro a b hEq
  by_cases hn0 : n=0
  · subst n
    have hcEq : c=0 := by
      simp [BB6.Agent46.run] at hEq
      rcases hEq with ⟨_,_,hcEq⟩
      exact hcEq
    omega
  · have hp := bounce_prefix c k hc n (by omega) hn
    obtain ⟨s,hs,hsc⟩ := hp
    rw [hs] at hEq
    have hcEq : s.2.2=0 := by
      injection hEq with hs'
      simpa using congrArg (fun z : CState => z.2.2) hs'
    omega

#print axioms bounce_prefix
#print axioms bounce_no_early_c0

end BB6.Agent15