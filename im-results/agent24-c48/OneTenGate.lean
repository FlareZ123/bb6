import OneTwoGate
import S5Reach
import Lean.Elab.Tactic.Omega

set_option maxRecDepth 8192
namespace BB6.Agent46

private theorem one_ten_pow_even (n : Nat) (hn : 1≤n) :
    ∃ u : Nat, 2^n=2*u := by
  obtain ⟨m,hm⟩ : ∃ m, n=m+1 := ⟨n-1,by omega⟩
  refine ⟨2^m,?_⟩
  rw [hm,Nat.pow_succ]
  omega

/-- An exact third predecessor after the six-residue and classical affine
    return reductions, uniform across a full Machine C one-left cylinder. -/
theorem one_ten_third_inverse (u a k : Nat) (hu : 1≤u)
    (h : secNext (a,k)=some (96*u+11,16*u+1)) :
    a=56*u+4 ∧ k=36*u+1 := by
  by_cases ha0 : a=0
  · by_cases hk0 : k=0
    · simp [secNext,exactSection,ha0,hk0] at h
    · by_cases hk1 : k=1
      · simp [secNext,exactSection,ha0,hk0,hk1] at h
        omega
      · have hb : (bounce 1 (2*k+1)).2=
            some (96*u+11,16*u+1) := by
          simpa only [secNext,exactSection,if_pos ha0,if_neg hk0,if_neg hk1] using h
        obtain ⟨n,hsum,_⟩ :=
          bounce_odd_output_invariants (2*k+1) 1
            (96*u+11) (16*u+1) (by decide) hb
        have hm : 112*u+12=8*(2^n) := by omega
        omega
  · by_cases ha1 : a=1
    · by_cases hk0 : k=0
      · simp [secNext,exactSection,ha0,ha1,hk0] at h
        omega
      · by_cases hk1 : k=1
        · simp [secNext,exactSection,ha0,ha1,hk0,hk1] at h
          omega
        · by_cases hk2 : k=2
          · simp [secNext,exactSection,ha0,ha1,hk0,hk1,hk2] at h
            omega
          · by_cases hk3 : k=3
            · simp [secNext,exactSection,ha0,ha1,hk0,hk1,hk2,hk3] at h
              omega
            · have hb : (bounce 4 (2*k-3)).2=
                  some (96*u+11,16*u+1) := by
                simpa only [secNext,exactSection,if_neg ha0,if_pos ha1,
                  if_neg hk0,if_neg hk1,if_neg hk2,if_neg hk3] using h
              obtain ⟨n,hsum,_⟩ :=
                bounce_even_output_invariants (2*k-3) 4
                  (96*u+11) (16*u+1) (by decide) (by omega) hb
              have hm : 112*u+13=16*(2^n) := by omega
              omega
    · have ha2 : 2≤a := by omega
      by_cases hk0 : k=0
      · simp [secNext,exactSection,ha0,ha1,hk0] at h
        omega
      · by_cases hregion : 2*k≤a
        · simp [secNext,exactSection,ha0,ha1,hk0,hregion] at h
          omega
        · have hb : (bounce (a-1) (2*k-a+3)).2=
              some (96*u+11,16*u+1) := by
            simpa only [secNext,exactSection,if_neg ha0,if_neg ha1,
              if_neg hk0,if_neg hregion] using h
          by_cases haeven : a%2=0
          · have hodd : (a-1)%2=1 := by omega
            obtain ⟨n,hsum,hcost⟩ :=
              bounce_odd_output_invariants (2*k-a+3) (a-1)
                (96*u+11) (16*u+1) hodd hb
            have hsum' : 112*u+12=2^n*(2*(a-1)+6) := by omega
            have hcost' : 128*u+13=2*k+a+7+3*n := by omega
            by_cases hn0 : n=0
            · subst n
              simp at hsum' hcost'
              constructor <;> omega
            · obtain ⟨p,hp⟩ := one_ten_pow_even n (by omega)
              obtain ⟨v,hv⟩ : ∃ v : Nat, 2*(a-1)+6=4*v :=
                ⟨a/2+1,by omega⟩
              have hdiv : 112*u+12=8*(p*v) := by
                calc
                  112*u+12=2^n*(2*(a-1)+6) := hsum'
                  _=(2*p)*(4*v) := by rw [hp,hv]
                  _=(2*4)*(p*v) := by ac_rfl
                  _=8*(p*v) := by rfl
              omega
          · have heven : (a-1)%2=0 := by omega
            obtain ⟨n,hsum,_⟩ :=
              bounce_even_output_invariants (2*k-a+3) (a-1)
                (96*u+11) (16*u+1) heven (by omega) hb
            have hm : 112*u+13=2*(2^n*(a+3)) := by
              calc
                112*u+13=2^n*(2*(a-1)+8) := hsum
                _=2^n*(2*(a+3)) := by congr 1 <;> omega
                _=2*(2^n*(a+3)) := by ac_rfl
            omega

theorem blank_no_one_ten_mod64 (u : Nat) (hu : 1≤u) :
    ¬ BB6.Agent3.CReach 1 (64*u+10) := by
  intro hr
  have hfirst : BB6.Agent3.CReach (64*u+9) (32*u+4) := by
    have hh := (six_even_right_blank_reach_iff
      1 (64*u+10) (by omega) (by omega) (by omega) (by omega)).mp hr
    have hx : 1+(64*u+10)-2=64*u+9 := by omega
    have hy : ((64*u+10)-2)/2=32*u+4 := by omega
    rw [hx,hy] at hh
    exact hh
  have hsecond : BB6.Agent3.CReach (96*u+11) (16*u+1) := by
    have hh := (BB6.Agent15.blank_reach_iff_affine
      (64*u+9) (32*u+4) (by omega) (by omega) (by omega)).mp hfirst
    have hx : (64*u+9)+(32*u+4)-2=96*u+11 := by omega
    have hy : ((32*u+4)-2)/2=16*u+1 := by omega
    rw [hx,hy] at hh
    exact hh
  have hthird : BB6.Agent3.CReach (56*u+4) (36*u+1) :=
    reach_forced_parent (96*u+11) (16*u+1) (56*u+4) (36*u+1)
      (by omega) (fun a k h => one_ten_third_inverse u a k hu h) hsecond
  rcases hthird with ⟨time,ht⟩
  cases time with
  | zero =>
      simp [BB6.Agent8Section.run] at ht
  | succ n =>
      have hh := BB6.Agent3.blank_section_odd_image n
        (56*u+4) (36*u+1) ht (by omega) (by omega)
      omega

theorem blank_no_low_halt_depth38 (m k : Nat)
    (hm : m%64=38) (heq : k+3*m+4=2^(2*m+3)) :
    ¬ BB6.Agent3.CReach 1 k := by
  have hm38 : 38≤m := by omega
  have hpow_lower := pow_two_linear m
  have hk42 : 42≤k := by omega
  have hdiv : 64 ∣ 2^(2*m+3) := by
    change 2^6 ∣ 2^(2*m+3)
    exact Nat.pow_dvd_pow 2 (by omega)
  obtain ⟨w,hw⟩ := hdiv
  have hmod : k%64=10 := by omega
  have hk : k=64*(k/64)+10 := by omega
  have ht : 1≤k/64 := by omega
  intro hr
  rw [hk] at hr
  exact blank_no_one_ten_mod64 (k/64) ht hr

#print axioms one_ten_third_inverse
#print axioms blank_no_one_ten_mod64
#print axioms blank_no_low_halt_depth38
end BB6.Agent46
