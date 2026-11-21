import U5B2Root32
import Lean.Elab.Tactic.Omega

set_option maxHeartbeats 1000000
set_option maxRecDepth 65536

namespace BB6.Agent3RRoot32ParentFanQ
open BB6.Agent46

def RxQ (q : Nat) : Nat := 9353264199+11447726640*q
def RyQ (q : Nat) : Nat := 6837816184+8368998120*q
def RpxQ (q : Nat) : Nat := 16191080381+19816724760*q
def RpyQ (q : Nat) : Nat := 3418908091+4184499060*q
def AbxQ (q : Nat) : Nat := 4047770093+4954181190*q
def AbyQ (q : Nat) : Nat := 9490563232+11615770845*q

theorem R_parent_fan_q7 (q a k : Nat) (hq : q%64=7)
    (hedge : secNext (a,k)=some (RxQ q,RyQ q)) :
    (a=RpxQ q ∧ k=RpyQ q) ∨ (a=AbxQ q ∧ k=AbyQ q) := by
  have hx5 : 5<RxQ q := by dsimp [RxQ]; omega
  have hxodd : RxQ q%2=1 := by dsimp [RxQ]; omega
  have hyeven : RyQ q%2=0 := by dsimp [RyQ]; omega
  have hy6 : 6≤RyQ q := by dsimp [RyQ]; omega
  have hsum8 : (RxQ q+RyQ q)%8=7 := by dsimp [RxQ,RyQ]; omega
  have hplus16 : (RxQ q+RyQ q+1)%16=8 := by dsimp [RxQ,RyQ]; omega
  have hCodd : (RxQ q+2*RyQ q)%2=1 := by dsimp [RxQ,RyQ]; omega
  clear hq
  have hp := (section_preimage_all_iff a k (RxQ q) (RyQ q)).mp hedge
  by_cases ha0 : a=0
  · by_cases hk0 : k=0
    · simp [sectionPreimageAll,ha0,hk0] at hp
    · by_cases hk1 : k=1
      · simp [sectionPreimageAll,ha0,hk0,hk1] at hp; omega
      · have hcase : 4≤RyQ q ∧ ∃ n : Nat,
            RxQ q+RyQ q=2^n*8 ∧ (2*k+1)+8+3*n=RxQ q+2*RyQ q := by
          simpa [sectionPreimageAll,ha0,hk0,hk1] using hp
        rcases hcase with ⟨_,n,hpow,_⟩
        have hzero : (RxQ q+RyQ q)%8=0 := by rw [hpow]; simp
        omega
  · by_cases ha1 : a=1
    · by_cases hk0 : k=0
      · simp [sectionPreimageAll,ha0,ha1,hk0] at hp; omega
      · by_cases hk1 : k=1
        · simp [sectionPreimageAll,ha0,ha1,hk0,hk1] at hp; omega
        · by_cases hk2 : k=2
          · simp [sectionPreimageAll,ha0,ha1,hk0,hk1,hk2] at hp; omega
          · by_cases hk3 : k=3
            · simp [sectionPreimageAll,ha0,ha1,hk0,hk1,hk2,hk3] at hp; omega
            · have hcase :
                  (RyQ q=3 ∧ ∃ n : Nat, RxQ q+6=2^n*16 ∧
                    (2*k-3)+16+3*n=RxQ q+10) ∨
                  (5≤RyQ q ∧ ∃ n : Nat,
                    RxQ q+RyQ q+1=2^n*16 ∧
                    (2*k-3)+16+3*n=RxQ q+2*RyQ q+2) := by
                simpa [sectionPreimageAll,ha0,ha1,hk0,hk1,hk2,hk3] using hp
              rcases hcase with ⟨hy3,_⟩ | ⟨_,n,hpow,_⟩
              · omega
              · have hzero : (RxQ q+RyQ q+1)%16=0 := by rw [hpow]; simp
                omega
    · have ha2 : 2≤a := by omega
      by_cases hk0 : k=0
      · simp [sectionPreimageAll,ha0,ha1,hk0] at hp; omega
      · by_cases hlow : 2*k≤a
        · have hcase : RxQ q=a-2*k ∧ RyQ q=2*k+2 := by
            simpa [sectionPreimageAll,ha0,ha1,hk0,hlow] using hp
          rcases hcase with ⟨hx,hy⟩
          have ha : a=RxQ q+RyQ q-2 := by omega
          have hk : k=(RyQ q-2)/2 := by omega
          left
          constructor
          · rw [ha]
            dsimp [RpxQ,RxQ,RyQ]
            omega
          · rw [hk]
            dsimp [RpyQ,RyQ]
            omega
        · by_cases haeven : a%2=0
          · have hcase : 4≤RyQ q ∧ ∃ n : Nat,
                RxQ q+RyQ q=2^n*(2*(a-1)+6) ∧
                (2*k-a+3)+(2*(a-1)+6)+3*n=RxQ q+2*RyQ q := by
              simpa [sectionPreimageAll,ha0,ha1,hk0,hlow,haeven] using hp
            rcases hcase with ⟨_,n,hpow,_⟩
            have hzero : (RxQ q+RyQ q)%2=0 := by rw [hpow]; simp [Nat.mul_mod]
            omega
          · have hcase :
                (RyQ q=3 ∧ ∃ n : Nat, RxQ q+6=2^n*(2*(a-1)+8) ∧
                  (2*k-a+3)+(2*(a-1)+8)+3*n=RxQ q+10) ∨
                (5≤RyQ q ∧ ∃ n : Nat,
                  RxQ q+RyQ q+1=2^n*(2*(a-1)+8) ∧
                  (2*k-a+3)+(2*(a-1)+8)+3*n=RxQ q+2*RyQ q+2) := by
              simpa [sectionPreimageAll,ha0,ha1,hk0,hlow,haeven] using hp
            rcases hcase with ⟨hy3,_⟩ | ⟨_,n,hpow,hcost⟩
            · omega
            · have hfac : 4∣2*(a-1)+8 := by
                refine ⟨(a-1)/2+2,?_⟩
                omega
              have hnodd : n%2=1 := by omega
              have hn1 : n=1 := by
                by_cases hn : n=1
                · exact hn
                · have hn3 : 3≤n := by omega
                  have hpow8 : 8∣2^n := by
                    change 2^3∣2^n
                    exact Nat.pow_dvd_pow 2 (by omega)
                  obtain ⟨u,hu⟩ := hpow8
                  obtain ⟨v,hv⟩ := hfac
                  have hdiv32 : 32∣2^n*(2*(a-1)+8) := by
                    refine ⟨u*v,?_⟩
                    calc
                      2^n*(2*(a-1)+8)=(8*u)*(4*v) := by rw [hu,hv]
                      _=8*4*(u*v) := by ac_rfl
                      _=32*(u*v) := by rw [show 8*4=32 by decide]
                  have hdiv16 : 16∣RxQ q+RyQ q+1 := by
                    rw [hpow]
                    exact Nat.dvd_trans (by decide : 16∣32) hdiv32
                  have hzero : (RxQ q+RyQ q+1)%16=0 := Nat.mod_eq_zero_of_dvd hdiv16
                  omega
              have haeq : a=AbxQ q := by
                rw [hn1] at hpow
                simp at hpow
                have hcalc : RxQ q+RyQ q+1=4*AbxQ q+12 := by
                  dsimp [RxQ,RyQ,AbxQ]
                  omega
                have hpow' : RxQ q+RyQ q+1=4*a+12 := by omega
                omega
              have hkeq : k=AbyQ q := by
                rw [hn1] at hcost
                simp at hcost
                rw [haeq] at hcost
                have hcalc : 2*AbyQ q+AbxQ q+10=RxQ q+2*RyQ q := by
                  dsimp [RxQ,RyQ,AbxQ,AbyQ]
                  omega
                omega
              exact Or.inr ⟨haeq,hkeq⟩

#print axioms R_parent_fan_q7

end BB6.Agent3RRoot32ParentFanQ
