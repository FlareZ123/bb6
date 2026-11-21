import U5B2Root32
import Lean.Elab.Tactic.Omega

set_option maxHeartbeats 1000000
set_option maxRecDepth 65536

namespace BB6.Agent3EvenOddV3Parent
open BB6.Agent46

theorem evenodd_sumplusone_v3_parent (x y a k : Nat)
    (hx5 : 5<x) (hx : x%2=0) (hy : y%2=1) (hy5 : 5≤y)
    (hplus16 : (x+y+1)%16=8)
    (hedge : secNext (a,k)=some (x,y)) :
    a=(x+y+1)/2-3 ∧ k=(x+2*y-a-7)/2 := by
  have hp := (section_preimage_all_iff a k x y).mp hedge
  by_cases ha0 : a=0
  · by_cases hk0 : k=0
    · simp [sectionPreimageAll,ha0,hk0] at hp
    · by_cases hk1 : k=1
      · simp [sectionPreimageAll,ha0,hk0,hk1] at hp
        omega
      · have hcase : 4≤y ∧ ∃ n : Nat,
            x+y=2^n*8 ∧ (2*k+1)+8+3*n=x+2*y := by
          simpa [sectionPreimageAll,ha0,hk0,hk1] using hp
        rcases hcase with ⟨_,n,hpow,_⟩
        have hmod : (x+y)%2=0 := by rw [hpow]; simp [Nat.mul_mod]
        omega
  · by_cases ha1 : a=1
    · by_cases hk0 : k=0
      · simp [sectionPreimageAll,ha0,ha1,hk0] at hp <;> omega
      · by_cases hk1 : k=1
        · simp [sectionPreimageAll,ha0,ha1,hk0,hk1] at hp <;> omega
        · by_cases hk2 : k=2
          · simp [sectionPreimageAll,ha0,ha1,hk0,hk1,hk2] at hp <;> omega
          · by_cases hk3 : k=3
            · simp [sectionPreimageAll,ha0,ha1,hk0,hk1,hk2,hk3] at hp <;> omega
            · have hcase :
                  (y=3 ∧ ∃ n : Nat, x+6=2^n*16 ∧
                    (2*k-3)+16+3*n=x+10) ∨
                  (5≤y ∧ ∃ n : Nat,
                    x+y+1=2^n*16 ∧
                    (2*k-3)+16+3*n=x+2*y+2) := by
                simpa [sectionPreimageAll,ha0,ha1,hk0,hk1,hk2,hk3] using hp
              rcases hcase with ⟨hy3,_⟩ | ⟨_,n,hpow,_⟩
              · omega
              · have hzero : (x+y+1)%16=0 := by
                  rw [hpow]
                  simp [Nat.mul_mod]
                omega
    · have ha2 : 2≤a := by omega
      by_cases hk0 : k=0
      · simp [sectionPreimageAll,ha0,ha1,hk0] at hp <;> omega
      · by_cases hlow : 2*k≤a
        · have hcase : x=a-2*k ∧ y=2*k+2 := by
            simpa [sectionPreimageAll,ha0,ha1,hk0,hlow] using hp
          rcases hcase with ⟨_,hyy⟩
          omega
        · by_cases haeven : a%2=0
          · have hcase : 4≤y ∧ ∃ n : Nat,
                x+y=2^n*(2*(a-1)+6) ∧
                (2*k-a+3)+(2*(a-1)+6)+3*n=x+2*y := by
              simpa [sectionPreimageAll,ha0,ha1,hk0,hlow,haeven] using hp
            rcases hcase with ⟨_,n,hpow,_⟩
            have hmod : (x+y)%2=0 := by rw [hpow]; simp [Nat.mul_mod]
            omega
          · have hcase :
                (y=3 ∧ ∃ n : Nat, x+6=2^n*(2*(a-1)+8) ∧
                  (2*k-a+3)+(2*(a-1)+8)+3*n=x+10) ∨
                (5≤y ∧ ∃ n : Nat,
                  x+y+1=2^n*(2*(a-1)+8) ∧
                  (2*k-a+3)+(2*(a-1)+8)+3*n=x+2*y+2) := by
              simpa [sectionPreimageAll,ha0,ha1,hk0,hlow,haeven] using hp
            rcases hcase with ⟨hy3,_⟩ | ⟨_,n,hpow,hcost⟩
            · omega
            · have hfac : 4∣2*(a-1)+8 := by
                refine ⟨(a-1)/2+2,?_⟩
                omega
              have hnEven : n%2=0 := by omega
              have hn0 : n=0 := by
                by_cases hn : n=0
                · exact hn
                · have hn2 : 2≤n := by omega
                  have hpow4 : 4∣2^n := by
                    change 2^2∣2^n
                    exact Nat.pow_dvd_pow 2 (by omega)
                  obtain ⟨u,hu⟩ := hpow4
                  obtain ⟨v,hv⟩ := hfac
                  have hdiv16 : 16∣2^n*(2*(a-1)+8) := by
                    refine ⟨u*v,?_⟩
                    calc
                      2^n*(2*(a-1)+8)=(4*u)*(4*v) := by rw [hu,hv]
                      _=4*4*(u*v) := by ac_rfl
                      _=16*(u*v) := by omega
                  have hdiv : 16∣x+y+1 := by rw [hpow]; exact hdiv16
                  have hzero : (x+y+1)%16=0 := Nat.mod_eq_zero_of_dvd hdiv
                  omega
              rw [hn0] at hpow hcost
              simp at hpow hcost
              have hxy : x+y+1=2*a+6 := by omega
              constructor
              · omega
              · omega

#print axioms evenodd_sumplusone_v3_parent

end BB6.Agent3EvenOddV3Parent
