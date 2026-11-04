import UniformOrbitIff
import BounceInverse
import Lean.Elab.Tactic.Omega

set_option maxRecDepth 8192

namespace BB6.Agent46

private theorem pow_two_even (n : Nat) (hn : 1 ≤ n) :
    ∃ z : Nat, 2^n = 2*z := by
  obtain ⟨m,hm⟩ : ∃ m, n=m+1 := ⟨n-1,by omega⟩
  refine ⟨2^m,?_⟩
  rw [hm,Nat.pow_succ]
  omega

/-- Exact unique source predecessor of the affine gateway ancestor
    Q(q)=(35584q+6939,14976q+2921). -/
theorem s25_first_inverse (q a k : Nat)
    (h : secNext (a,k) = some (35584*q+6939,14976*q+2921)) :
    a=25280*q+4928 ∧ k=20128*q+3923 := by
  by_cases ha0 : a=0
  · by_cases hk0 : k=0
    · simp [secNext,exactSection,ha0,hk0] at h
    · by_cases hk1 : k=1
      · simp [secNext,exactSection,ha0,hk0,hk1] at h
      · have hb : (bounce 1 (2*k+1)).2 =
            some (35584*q+6939,14976*q+2921) := by
          simpa only [secNext,exactSection,if_pos ha0,if_neg hk0,if_neg hk1] using h
        obtain ⟨n,hsum,_⟩ :=
          bounce_odd_output_invariants (2*k+1) 1
            (35584*q+6939) (14976*q+2921) (by decide) hb
        have hmod : 50560*q+9860=8*(2^n) := by omega
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
            · have hb : (bounce 4 (2*k-3)).2 =
                  some (35584*q+6939,14976*q+2921) := by
                simpa only [secNext,exactSection,if_neg ha0,if_pos ha1,
                  if_neg hk0,if_neg hk1,if_neg hk2,if_neg hk3] using h
              obtain ⟨n,hsum,_⟩ :=
                bounce_even_output_invariants (2*k-3) 4
                  (35584*q+6939) (14976*q+2921)
                  (by decide) (by omega) hb
              have hpar : 50560*q+9861=16*(2^n) := by omega
              omega
    · have ha2 : 2≤a := by omega
      by_cases hk0 : k=0
      · simp [secNext,exactSection,ha0,ha1,hk0] at h
      · by_cases hregion : 2*k≤a
        · simp [secNext,exactSection,ha0,ha1,hk0,hregion] at h
          omega
        · have hb : (bounce (a-1) (2*k-a+3)).2 =
              some (35584*q+6939,14976*q+2921) := by
            simpa only [secNext,exactSection,if_neg ha0,if_neg ha1,
              if_neg hk0,if_neg hregion] using h
          by_cases he : a%2=0
          · have hodd : (a-1)%2=1 := by omega
            obtain ⟨n,hsum,hcost⟩ :=
              bounce_odd_output_invariants (2*k-a+3) (a-1)
                (35584*q+6939) (14976*q+2921) hodd hb
            have hsum' : 50560*q+9860 = 2^n*(2*(a-1)+6) := by omega
            have hcost' : 65536*q+12781 = 2*k+a+7+3*n := by omega
            by_cases hn : n=0
            · subst n
              simp at hsum' hcost'
              omega
            · obtain ⟨u,hu⟩ := pow_two_even n (by omega)
              obtain ⟨v,hv⟩ : ∃ v : Nat, 2*(a-1)+6=4*v :=
                ⟨a/2+1, by omega⟩
              have hdiv : 50560*q+9860=8*(u*v) := by
                calc
                  50560*q+9860=2^n*(2*(a-1)+6) := hsum'
                  _ = (2*u)*(4*v) := by rw [hu,hv]
                  _ = (2*4)*(u*v) := by ac_rfl
                  _ = 8*(u*v) := by rfl
              omega
          · have hodd : (a-1)%2=0 := by omega
            obtain ⟨n,hsum,_⟩ :=
              bounce_even_output_invariants (2*k-a+3) (a-1)
                (35584*q+6939) (14976*q+2921) hodd (by omega) hb
            have hfactor : 2*(a-1)+8=2*(a+3) := by omega
            have heven : 50560*q+9861=2*(2^n*(a+3)) := by
              calc
                50560*q+9861=2^n*(2*(a-1)+8) := by omega
                _ = 2^n*(2*(a+3)) := by rw [hfactor]
                _ = 2*(2^n*(a+3)) := by ac_rfl
            omega

/-- Unique one-step original-source predecessor of the intermediate
    P(q)=(25280q+4928,20128q+3923). -/
theorem s25_second_inverse (q a k : Nat)
    (h : secNext (a,k) = some (25280*q+4928,20128*q+3923)) :
    a=22704*q+4423 ∧ k=21416*q+4172 := by
  by_cases ha0 : a=0
  · by_cases hk0 : k=0
    · simp [secNext,exactSection,ha0,hk0] at h
    · by_cases hk1 : k=1
      · simp [secNext,exactSection,ha0,hk0,hk1] at h
      · have hb : (bounce 1 (2*k+1)).2 =
            some (25280*q+4928,20128*q+3923) := by
          simpa only [secNext,exactSection,if_pos ha0,if_neg hk0,if_neg hk1] using h
        obtain ⟨n,hsum,_⟩ :=
          bounce_odd_output_invariants (2*k+1) 1
            (25280*q+4928) (20128*q+3923) (by decide) hb
        have hmod : 45408*q+8851=8*(2^n) := by omega
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
            · have hb : (bounce 4 (2*k-3)).2 =
                  some (25280*q+4928,20128*q+3923) := by
                simpa only [secNext,exactSection,if_neg ha0,if_pos ha1,
                  if_neg hk0,if_neg hk1,if_neg hk2,if_neg hk3] using h
              obtain ⟨n,hsum,_⟩ :=
                bounce_even_output_invariants (2*k-3) 4
                  (25280*q+4928) (20128*q+3923)
                  (by decide) (by omega) hb
              have hpar : 45408*q+8852=16*(2^n) := by omega
              omega
    · have ha2 : 2≤a := by omega
      by_cases hk0 : k=0
      · simp [secNext,exactSection,ha0,ha1,hk0] at h
      · by_cases hregion : 2*k≤a
        · simp [secNext,exactSection,ha0,ha1,hk0,hregion] at h
          omega
        · have hb : (bounce (a-1) (2*k-a+3)).2 =
              some (25280*q+4928,20128*q+3923) := by
            simpa only [secNext,exactSection,if_neg ha0,if_neg ha1,
              if_neg hk0,if_neg hregion] using h
          by_cases he : a%2=0
          · have hodd : (a-1)%2=1 := by omega
            obtain ⟨n,hsum,_⟩ :=
              bounce_odd_output_invariants (2*k-a+3) (a-1)
                (25280*q+4928) (20128*q+3923) hodd hb
            have hsum' : 45408*q+8851=2^n*(2*(a-1)+6) := by omega
            have hpar : 2*(a-1)+6=2*(a+2) := by omega
            have heven : 45408*q+8851=2*(2^n*(a+2)) := by
              calc
                45408*q+8851=2^n*(2*(a-1)+6) := hsum'
                _ = 2^n*(2*(a+2)) := by rw [hpar]
                _ = 2*(2^n*(a+2)) := by ac_rfl
            omega
          · have hodd : (a-1)%2=0 := by omega
            obtain ⟨n,hsum,hcost⟩ :=
              bounce_even_output_invariants (2*k-a+3) (a-1)
                (25280*q+4928) (20128*q+3923) hodd (by omega) hb
            have hsum' : 45408*q+8852=2^n*(2*(a-1)+8) := by omega
            have hcost' : 65536*q+12776=2*k+a+9+3*n := by omega
            by_cases hn : n=0
            · subst n
              simp at hsum' hcost'
              omega
            · obtain ⟨u,hu⟩ := pow_two_even n (by omega)
              obtain ⟨v,hv⟩ : ∃ v : Nat, 2*(a-1)+8=4*v :=
                ⟨(a+3)/2, by omega⟩
              have hdiv : 45408*q+8852=8*(u*v) := by
                calc
                  45408*q+8852=2^n*(2*(a-1)+8) := hsum'
                  _ = (2*u)*(4*v) := by rw [hu,hv]
                  _ = (2*4)*(u*v) := by ac_rfl
                  _ = 8*(u*v) := by rfl
              omega

/-- Source-complete third inverse: the even-right output has exactly
    one predecessor. Its other apparent high-bounce branches are ruled
    out by the parity of the exact bounce cost. -/
theorem s25_third_inverse (q a k : Nat)
    (h : secNext (a,k) = some (22704*q+4423,21416*q+4172)) :
    a=44120*q+8593 ∧ k=10708*q+2085 := by
  by_cases ha0 : a=0
  · by_cases hk0 : k=0
    · simp [secNext,exactSection,ha0,hk0] at h
    · by_cases hk1 : k=1
      · simp [secNext,exactSection,ha0,hk0,hk1] at h
      · have hb : (bounce 1 (2*k+1)).2 =
            some (22704*q+4423,21416*q+4172) := by
          simpa only [secNext,exactSection,if_pos ha0,if_neg hk0,if_neg hk1] using h
        obtain ⟨n,hsum,_⟩ :=
          bounce_odd_output_invariants (2*k+1) 1
            (22704*q+4423) (21416*q+4172) (by decide) hb
        have hmod : 44120*q+8595=8*(2^n) := by omega
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
            · have hb : (bounce 4 (2*k-3)).2 =
                  some (22704*q+4423,21416*q+4172) := by
                simpa only [secNext,exactSection,if_neg ha0,if_pos ha1,
                  if_neg hk0,if_neg hk1,if_neg hk2,if_neg hk3] using h
              obtain ⟨n,hsum,_⟩ :=
                bounce_even_output_invariants (2*k-3) 4
                  (22704*q+4423) (21416*q+4172)
                  (by decide) (by omega) hb
              have hpar : 44120*q+8596=16*(2^n) := by omega
              omega
    · have ha2 : 2≤a := by omega
      by_cases hk0 : k=0
      · simp [secNext,exactSection,ha0,ha1,hk0] at h
      · by_cases hregion : 2*k≤a
        · simp [secNext,exactSection,ha0,ha1,hk0,hregion] at h
          omega
        · have hb : (bounce (a-1) (2*k-a+3)).2 =
              some (22704*q+4423,21416*q+4172) := by
            simpa only [secNext,exactSection,if_neg ha0,if_neg ha1,
              if_neg hk0,if_neg hregion] using h
          by_cases he : a%2=0
          · have hodd : (a-1)%2=1 := by omega
            obtain ⟨n,hsum,_⟩ :=
              bounce_odd_output_invariants (2*k-a+3) (a-1)
                (22704*q+4423) (21416*q+4172) hodd hb
            have hpar : 2*(a-1)+6=2*(a+2) := by omega
            have heven : 44120*q+8595=2*(2^n*(a+2)) := by
              calc
                44120*q+8595=2^n*(2*(a-1)+6) := by omega
                _ = 2^n*(2*(a+2)) := by rw [hpar]
                _ = 2*(2^n*(a+2)) := by ac_rfl
            omega
          · have hodd : (a-1)%2=0 := by omega
            obtain ⟨n,hsum,hcost⟩ :=
              bounce_even_output_invariants (2*k-a+3) (a-1)
                (22704*q+4423) (21416*q+4172) hodd (by omega) hb
            have hsum' : 44120*q+8596=2^n*(2*(a-1)+8) := by omega
            have hcost' : 65536*q+12769=2*k+a+9+3*n := by omega
            by_cases hn : n=0
            · subst n
              simp at hsum' hcost'
              omega
            · obtain ⟨u,hu⟩ := pow_two_even n (by omega)
              obtain ⟨v,hv⟩ : ∃ v : Nat, 2*(a-1)+8=4*v :=
                ⟨(a+3)/2, by omega⟩
              have hdiv : 44120*q+8596=8*(u*v) := by
                calc
                  44120*q+8596=2^n*(2*(a-1)+8) := hsum'
                  _ = (2*u)*(4*v) := by rw [hu,hv]
                  _ = (2*4)*(u*v) := by ac_rfl
                  _ = 8*(u*v) := by rfl
              omega

#print axioms s25_first_inverse
#print axioms s25_second_inverse
#print axioms s25_third_inverse

end BB6.Agent46
