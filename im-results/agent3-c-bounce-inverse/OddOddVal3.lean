import OddOddOrbit
import Lean.Elab.Tactic.Omega

namespace BB6.Agent3
open BB6.Agent46

/-- The next odd/odd 2-adic layer also has exactly one genuine section
    predecessor, after excluding the exceptional total mass eight. -/
theorem oddodd_val3_parent_equations (a k x y : Nat)
    (hx : x%2=1) (hy : y%2=1) (hy5 : 5≤y)
    (hs : (x+y)%16=8) (hsize : 24≤x+y)
    (h : secNext (a,k)=some (x,y)) :
    x+y=2*a+4 ∧ x+3*y=4*k+10 := by
  have hp := (section_preimage_all_iff a k x y).mp h
  by_cases ha0 : a=0
  · by_cases hk0 : k=0
    · simp [sectionPreimageAll,ha0,hk0] at hp
    · by_cases hk1 : k=1
      · simp [sectionPreimageAll,ha0,hk0,hk1] at hp
        omega
      · simp only [sectionPreimageAll,if_pos ha0,if_neg hk0,if_neg hk1] at hp
        obtain ⟨_,n,hpow,_⟩ := hp
        cases n with
        | zero => simp at hpow; omega
        | succ n =>
            have h16 : 16∣x+y := by
              refine ⟨2^n,?_⟩
              calc
                x+y = 2^(n+1)*8 := hpow
                _ = 16*2^n := by rw [Nat.pow_succ]; omega
            omega
  · by_cases ha1 : a=1
    · by_cases hk0 : k=0
      · simp [sectionPreimageAll,ha0,ha1,hk0] at hp
        omega
      · by_cases hk1 : k=1
        · simp [sectionPreimageAll,ha0,ha1,hk0,hk1] at hp
          omega
        · by_cases hk2 : k=2
          · simp [sectionPreimageAll,ha0,ha1,hk0,hk1,hk2] at hp
            omega
          · by_cases hk3 : k=3
            · simp [sectionPreimageAll,ha0,ha1,hk0,hk1,hk2,hk3] at hp
              omega
            · simp only [sectionPreimageAll,if_neg ha0,if_pos ha1,
                if_neg hk0,if_neg hk1,if_neg hk2,if_neg hk3] at hp
              rcases hp with ⟨hy3,_⟩ | ⟨_,n,hpow,_⟩
              · omega
              · have hd : 16∣x+y+1 := ⟨2^n,by omega⟩
                omega
    · have ha2 : 2≤a := by omega
      by_cases hk0 : k=0
      · simp [sectionPreimageAll,ha0,ha1,hk0] at hp
        omega
      · by_cases hlow : 2*k≤a
        · simp [sectionPreimageAll,ha0,ha1,hk0,hlow] at hp
          omega
        · by_cases heven : a%2=0
          · simp only [sectionPreimageAll,if_neg ha0,if_neg ha1,
              if_neg hk0,if_neg hlow,if_pos heven] at hp
            obtain ⟨_,n,hpow,hcost⟩ := hp
            cases n with
            | zero => simp at hpow hcost; omega
            | succ n =>
                cases n with
                | zero => simp at hpow hcost; omega
                | succ n =>
                    have hbase : 4∣2*(a-1)+6 := by
                      refine ⟨a/2+1,?_⟩
                      omega
                    obtain ⟨u,hu⟩ : 4∣2^(n+1+1) :=
                      (show 2^2∣2^(n+1+1) from Nat.pow_dvd_pow 2 (by omega))
                    obtain ⟨v,hv⟩ := hbase
                    have h16 : 16∣x+y := by
                      refine ⟨u*v,?_⟩
                      calc
                        x+y=2^(n+1+1)*(2*(a-1)+6) := hpow
                        _=(4*u)*(4*v) := by rw [hu,hv]
                        _=16*(u*v) := by ac_rfl
                    omega
          · simp only [sectionPreimageAll,if_neg ha0,if_neg ha1,
              if_neg hk0,if_neg hlow,if_neg heven] at hp
            rcases hp with ⟨hy3,_⟩ | ⟨_,n,hpow,_⟩
            · omega
            · have hd : 2∣2^n*(2*(a-1)+8) := by
                refine ⟨2^n*((a-1)+4),?_⟩
                calc
                  2^n*(2*(a-1)+8)=2^n*(2*((a-1)+4)) := by congr 1 <;> omega
                  _=2*(2^n*((a-1)+4)) := by ac_rfl
              omega

/-- Complete iff for all large odd/odd outputs with v2(total mass)=3. -/
theorem oddodd_val3_parent_iff (a k x y : Nat)
    (hx : x%2=1) (hy : y%2=1) (hy5 : 5≤y)
    (hs : (x+y)%16=8) (hsize : 24≤x+y) :
    secNext (a,k)=some (x,y) ↔
      x+y=2*a+4 ∧ x+3*y=4*k+10 := by
  constructor
  · exact oddodd_val3_parent_equations a k x y hx hy hy5 hs hsize
  · rintro ⟨hsum,hcost⟩
    have ha0 : a≠0 := by omega
    have ha1 : a≠1 := by omega
    have hk0 : k≠0 := by omega
    have hlow : ¬2*k≤a := by omega
    have heven : a%2=0 := by omega
    apply (section_preimage_all_iff a k x y).mpr
    simp only [sectionPreimageAll,if_neg ha0,if_neg ha1,
      if_neg hk0,if_neg hlow,if_pos heven]
    refine ⟨by omega,0,?_,?_⟩ <;> simp <;> omega

#print axioms oddodd_val3_parent_iff
end BB6.Agent3
