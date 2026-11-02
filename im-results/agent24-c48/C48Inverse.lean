import FastSectionDef
import BounceInverse
import Lean.Elab.Tactic.Omega

set_option maxRecDepth 8192
namespace BB6.Agent46

private theorem pow_two_four (n : Nat) (hn : 2≤n) : ∃ v : Nat, 2^n=4*v := by
  obtain ⟨m,hm⟩ : ∃ m, n=m+2 := ⟨n-2, by omega⟩
  refine ⟨2^m, ?_⟩
  rw [hm, Nat.pow_add]
  simp only [show (2:Nat)^2=4 by decide]
  omega

private theorem pow_two_sixteen (n : Nat) (hn : 4≤n) : ∃ v : Nat, 2^n=16*v := by
  obtain ⟨m,hm⟩ : ∃ m, n=m+4 := ⟨n-4, by omega⟩
  refine ⟨2^m, ?_⟩
  rw [hm, Nat.pow_add]
  simp only [show (2:Nat)^4=16 by decide]
  omega

/-- All high-branch even bounces producing this affine target have only
    two possible recursion depths, with corresponding exact parents. -/
theorem target_bounce_even_inverse48 (q a k : Nat)
    (ha : 3≤a) (hodd : a%2=1) (hhigh : a<2*k)
    (hb : (bounce (a-1) (2*k-a+3)).2 = some (768*q+576,640*q+479)) :
    (a=704*q+525 ∧ k=672*q+501) ∨
    (a=176*q+129 ∧ k=936*q+696) := by
  have heven : (a-1)%2=0 := by omega
  obtain ⟨n,hsum,hcost⟩ :=
    bounce_even_output_invariants (2*k-a+3) (a-1) (768*q+576) (640*q+479)
      heven (by omega) hb
  have hsum' : 1408*q+1056 = 2^n * (2*(a-1)+8) := by omega
  have hcost' : 2048*q+1536 = 2*k+a+9+3*n := by omega
  have heven4 : ∃ z : Nat, 2*(a-1)+8=4*z := by
    refine ⟨(a+3)/2, ?_⟩
    omega
  have hbound : n≤3 := by
    by_cases hh : n≤3
    · exact hh
    exfalso
    have hn : 4≤n := by omega
    obtain ⟨u,hu⟩ := pow_two_sixteen n hn
    obtain ⟨z,hz⟩ := heven4
    have hmod : 1408*q+1056 = 64*(u*z) := by
      calc
        1408*q+1056 = 2^n*(2*(a-1)+8) := hsum'
        _ = (16*u)*(4*z) := by rw [hu,hz]
        _ = (16*4)*(u*z) := by ac_rfl
        _ = 64*(u*z) := by rfl
    omega
  have hpar : n%2=0 := by omega
  have hcases : n=0 ∨ n=2 := by omega
  rcases hcases with h0 | h2
  · subst n
    left
    constructor <;> simp_all <;> omega
  · subst n
    right
    constructor <;> simp_all <;> omega

/-- Even bounce starting at middle four cannot produce this affine output. -/
theorem no_kfour_bounce_target48 (q k : Nat)
    (hb : (bounce 4 (2*k-3)).2=some (768*q+576,640*q+479)) : False := by
  obtain ⟨n,hsum,_⟩ :=
    bounce_even_output_invariants (2*k-3) 4 (768*q+576) (640*q+479)
      (by decide) (by omega) hb
  have hsum' : 1408*q+1056 = 16*2^n := by omega
  by_cases hn : n=0
  · subst n
    simp at hsum'
    omega
  by_cases hn1 : n=1
  · subst n
    simp at hsum'
    omega
  have hn2 : 2≤n := by omega
  obtain ⟨u,hu⟩ := pow_two_four n hn2
  have hh : 1408*q+1056=64*u := by
    calc
      1408*q+1056 = 16*2^n := hsum'
      _ = 16*(4*u) := by rw [hu]
      _ = 64*u := by omega
  omega

/-- A universally complete necessary-predecessor classification for one
    affine family of the original Machine C source section map. -/
theorem target_section_inverse48 (q a k : Nat)
    (h : secNext (a,k)=some (768*q+576,640*q+479)) :
    (a=704*q+525 ∧ k=672*q+501) ∨
    (a=176*q+129 ∧ k=936*q+696) := by
  by_cases ha0 : a=0
  · by_cases hk0 : k=0
    · simp [secNext,exactSection,ha0,hk0] at h
    · by_cases hk1 : k=1
      · simp [secNext,exactSection,ha0,hk0,hk1] at h
      · have hb : (bounce 1 (2*k+1)).2=some (768*q+576,640*q+479) := by
          simpa only [secNext,exactSection,if_pos ha0,if_neg hk0,if_neg hk1] using h
        obtain ⟨n,hsum,_⟩ :=
          bounce_odd_output_invariants (2*k+1) 1 (768*q+576) (640*q+479)
            (by decide) hb
        omega
  · by_cases ha1 : a=1
    · by_cases hk0 : k=0
      · simp [secNext,exactSection,ha0,ha1,hk0] at h
      · by_cases hk1 : k=1
        · simp [secNext,exactSection,ha0,ha1,hk0,hk1] at h
        · by_cases hk2 : k=2
          · simp [secNext,exactSection,ha0,ha1,hk0,hk1,hk2] at h
          · by_cases hk3 : k=3
            · simp [secNext,exactSection,ha0,ha1,hk0,hk1,hk2,hk3] at h
            · have hb : (bounce 4 (2*k-3)).2=some (768*q+576,640*q+479) := by
                simpa only [secNext,exactSection,if_neg ha0,if_pos ha1,if_neg hk0,if_neg hk1,if_neg hk2,if_neg hk3] using h
              exact False.elim (no_kfour_bounce_target48 q k hb)
    · have ha2 : 2≤a := by omega
      by_cases hk0 : k=0
      · simp [secNext,exactSection,ha0,ha1,hk0] at h
      · by_cases hregion : 2*k≤a
        · simp [secNext,exactSection,ha0,ha1,hk0,hregion] at h
          omega
        · have hb : (bounce (a-1) (2*k-a+3)).2=some (768*q+576,640*q+479) := by
            simpa only [secNext,exactSection,if_neg ha0,if_neg ha1,if_neg hk0,if_neg hregion] using h
          by_cases he : a%2=0
          · have hodd : (a-1)%2=1 := by omega
            obtain ⟨n,hsum,_⟩ :=
              bounce_odd_output_invariants (2*k-a+3) (a-1)
                (768*q+576) (640*q+479) hodd hb
            have hfactor : 2*(a-1)+6=2*(a+2) := by omega
            have heven_sum : 1408*q+1055=2*(2^n*(a+2)) := by
              calc
                1408*q+1055 = 2^n*(2*(a-1)+6) := by omega
                _ = 2^n*(2*(a+2)) := by rw [hfactor]
                _ = 2*(2^n*(a+2)) := by ac_rfl
            omega
          · have hodd : a%2=1 := by omega
            exact target_bounce_even_inverse48 q a k (by omega) hodd (by omega) hb

#print axioms target_bounce_even_inverse48
#print axioms no_kfour_bounce_target48
#print axioms target_section_inverse48
end BB6.Agent46
