import AffineTarget
import BounceInverse
import Lean.Elab.Tactic.Omega

set_option maxRecDepth 8192
namespace BB6.Agent46

private theorem pow_two_even (n : Nat) (hn : 1≤n) : ∃ v : Nat, 2^n = 2*v := by
  obtain ⟨m,hm⟩ : ∃ m, n=m+1 := ⟨n-1, by omega⟩
  refine ⟨2^m, ?_⟩
  rw [hm, Nat.pow_succ]
  omega

private theorem pow_two_eight (n : Nat) (hn : 3≤n) : ∃ v : Nat, 2^n = 8*v := by
  obtain ⟨m,hm⟩ : ∃ m, n=m+3 := ⟨n-3, by omega⟩
  refine ⟨2^m, ?_⟩
  rw [hm, Nat.pow_add]
  simp only [show (2:Nat)^3 = 8 by decide]
  omega

/-- All high-branch even bounces producing this affine target have only
    two possible recursion depths, with corresponding exact parents. -/
theorem target_bounce_even_inverse56 (q a k : Nat)
    (ha : 3≤a) (hodd : a%2=1) (hhigh : a<2*k)
    (hb : (bounce (a-1) (2*k-a+3)).2 = some (1536*q+672,1280*q+559)) :
    (a=1408*q+613 ∧ k=1344*q+585) ∨
    (a=352*q+151 ∧ k=1872*q+813) := by
  have heven : (a-1)%2=0 := by omega
  obtain ⟨n,hsum,hcost⟩ :=
    bounce_even_output_invariants (2*k-a+3) (a-1) (1536*q+672) (1280*q+559)
      heven (by omega) hb
  have hsum' : 2816*q+1232 = 2^n * (2*(a-1)+8) := by omega
  have hcost' : 4096*q+1792 = 2*k+a+9+3*n := by omega
  have heven4 : ∃ z : Nat, 2*(a-1)+8=4*z := by
    refine ⟨(a+3)/2, ?_⟩
    omega
  have hbound : n≤2 := by
    by_cases hh : n≤2
    · exact hh
    exfalso
    have hn : 3≤n := by omega
    obtain ⟨u,hu⟩ := pow_two_eight n hn
    obtain ⟨z,hz⟩ := heven4
    have hmod : 2816*q+1232 = 32*(u*z) := by
      calc
        2816*q+1232 = 2^n * (2*(a-1)+8) := hsum'
        _ = (8*u)*(4*z) := by rw [hu,hz]
        _ = (8*4)*(u*z) := by ac_rfl
        _ = 32*(u*z) := by rfl
    omega
  have hpar : n%2=0 := by omega
  have hcases : n=0 ∨ n=1 ∨ n=2 := by omega
  rcases hcases with h0 | h1 | h2
  · subst n
    left
    constructor <;> simp_all <;> omega
  · omega
  · subst n
    right
    constructor <;> simp_all <;> omega

/-- Even bounce starting at middle four cannot produce this affine output. -/
theorem no_kfour_bounce_target56 (q k : Nat)
    (hb : (bounce 4 (2*k-3)).2=some (1536*q+672,1280*q+559)) : False := by
  obtain ⟨n,hsum,_⟩ :=
    bounce_even_output_invariants (2*k-3) 4 (1536*q+672) (1280*q+559)
      (by decide) (by omega) hb
  have hsum' : 2816*q+1232 = 16*2^n := by omega
  by_cases hn : n=0
  · subst n
    simp at hsum'
  · have hpos : 1≤n := by omega
    obtain ⟨u,hu⟩ := pow_two_even n hpos
    have hh : 2816*q+1232=32*u := by
      calc
        2816*q+1232=16*2^n := hsum'
        _ = 16*(2*u) := by rw [hu]
        _ = 32*u := by omega
    omega

/-- A universally complete necessary-predecessor classification for one
    affine family of the original Machine C source section map. -/
theorem target_section_inverse56 (q a k : Nat)
    (h : secNext (a,k)=some (1536*q+672,1280*q+559)) :
    (a=1408*q+613 ∧ k=1344*q+585) ∨
    (a=352*q+151 ∧ k=1872*q+813) := by
  by_cases ha0 : a=0
  · by_cases hk0 : k=0
    · simp [secNext,exactSection,ha0,hk0] at h
    · by_cases hk1 : k=1
      · simp [secNext,exactSection,ha0,hk0,hk1] at h
      · have hb : (bounce 1 (2*k+1)).2=some (1536*q+672,1280*q+559) := by
          simpa only [secNext,exactSection,if_pos ha0,if_neg hk0,if_neg hk1] using h
        obtain ⟨n,hsum,_⟩ :=
          bounce_odd_output_invariants (2*k+1) 1 (1536*q+672) (1280*q+559)
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
            · have hb : (bounce 4 (2*k-3)).2=some (1536*q+672,1280*q+559) := by
                simpa only [secNext,exactSection,if_neg ha0,if_pos ha1,if_neg hk0,if_neg hk1,if_neg hk2,if_neg hk3] using h
              exact False.elim (no_kfour_bounce_target56 q k hb)
    · have ha2 : 2≤a := by omega
      by_cases hk0 : k=0
      · simp [secNext,exactSection,ha0,ha1,hk0] at h
      · by_cases hregion : 2*k≤a
        · simp [secNext,exactSection,ha0,ha1,hk0,hregion] at h
          omega
        · have hb : (bounce (a-1) (2*k-a+3)).2=some (1536*q+672,1280*q+559) := by
            simpa only [secNext,exactSection,if_neg ha0,if_neg ha1,if_neg hk0,if_neg hregion] using h
          by_cases he : a%2=0
          · have hodd : (a-1)%2=1 := by omega
            obtain ⟨n,hsum,_⟩ :=
              bounce_odd_output_invariants (2*k-a+3) (a-1)
                (1536*q+672) (1280*q+559) hodd hb
            have hfactor : 2*(a-1)+6=2*(a+2) := by omega
            have heven_sum : 2816*q+1231=2*(2^n*(a+2)) := by
              calc
                2816*q+1231 = 2^n*(2*(a-1)+6) := by omega
                _ = 2^n*(2*(a+2)) := by rw [hfactor]
                _ = 2*(2^n*(a+2)) := by ac_rfl
            omega
          · have hodd : a%2=1 := by omega
            exact target_bounce_even_inverse56 q a k (by omega) hodd (by omega) hb

#print axioms target_bounce_even_inverse56
#print axioms no_kfour_bounce_target56
#print axioms target_section_inverse56
end BB6.Agent46
