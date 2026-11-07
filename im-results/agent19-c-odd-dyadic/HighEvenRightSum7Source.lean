import SectionAllInverse
import Agent3CImage
import Agent3COrbitIff
import HighEvenRightSum7Arithmetic
import Lean.Elab.Tactic.Omega

namespace BB6.Agent19HighEvenRight

/-- Every exact one-step predecessor of this sum-seven target cylinder
    lies in the forbidden odd-right image class. This uses the complete
    SectionAllInverse preimage grammar, including the exceptional
    a=1 and odd-a bounce branches. -/
theorem sum7_every_parent_odd_image (x y a b : Nat)
    (hy12 : 12≤y) (hxy8 : (x+y)%8=7)
    (hS16 : (x+y+1)%16=8) (hS32 : (x+y+1)%32=24)
    (hx4 : x%4=3) (hy8 : y%8=4)
    (hpre : BB6.Agent46.sectionPreimageAll a b x y) :
    5≤b ∧ b%2=1 ∧ (a+b)%4=2 := by
  by_cases ha0 : a=0
  · by_cases hb0 : b=0
    · simp [BB6.Agent46.sectionPreimageAll,ha0,hb0] at hpre
    · by_cases hb1 : b=1
      · simp [BB6.Agent46.sectionPreimageAll,ha0,hb0,hb1] at hpre
        omega
      · have hcase : 4≤y ∧ ∃ n:Nat,
            x+y=2^n*8 ∧ (2*b+1)+8+3*n=x+2*y := by
          simpa [BB6.Agent46.sectionPreimageAll,ha0,hb0,hb1] using hpre
        rcases hcase with ⟨_,n,hsum,_⟩
        have hdiv : 8∣x+y := by
          refine ⟨2^n,?_⟩
          simpa [Nat.mul_comm] using hsum
        have hmod : (x+y)%8=0 := Nat.mod_eq_zero_of_dvd hdiv
        omega
  · by_cases ha1 : a=1
    · by_cases hb0 : b=0
      · simp [BB6.Agent46.sectionPreimageAll,ha0,ha1,hb0] at hpre
        omega
      · by_cases hb1 : b=1
        · simp [BB6.Agent46.sectionPreimageAll,ha0,ha1,hb0,hb1] at hpre
          omega
        · by_cases hb2 : b=2
          · simp [BB6.Agent46.sectionPreimageAll,ha0,ha1,hb0,hb1,hb2] at hpre
            omega
          · by_cases hb3 : b=3
            · simp [BB6.Agent46.sectionPreimageAll,ha0,ha1,hb0,hb1,hb2,hb3] at hpre
              omega
            · have hcase :
                (y=3 ∧ ∃ n:Nat, x+6=2^n*16 ∧
                  (2*b-3)+16+3*n=x+10) ∨
                (5≤y ∧ ∃ n:Nat, x+y+1=2^n*16 ∧
                  (2*b-3)+16+3*n=x+2*y+2) := by
                  simpa [BB6.Agent46.sectionPreimageAll,ha0,ha1,hb0,hb1,hb2,hb3] using hpre
              rcases hcase with ⟨hy3,_⟩ | ⟨_,n,hsum,_⟩
              · omega
              · have hdiv : 16∣x+y+1 := by
                  refine ⟨2^n,?_⟩
                  simpa [Nat.mul_comm] using hsum
                have hmod : (x+y+1)%16=0 := Nat.mod_eq_zero_of_dvd hdiv
                omega
    · have ha2 : 2≤a := by omega
      by_cases hb0 : b=0
      · simp [BB6.Agent46.sectionPreimageAll,ha0,ha1,hb0] at hpre
        omega
      · by_cases hdirect : 2*b≤a
        · have hcase : x=a-2*b ∧ y=2*b+2 := by
            simpa [BB6.Agent46.sectionPreimageAll,ha0,ha1,hb0,hdirect] using hpre
          rcases hcase with ⟨hx,hy⟩
          have hb4 : b%4=1 := by omega
          have hsum : (a+b)%4=2 := by omega
          have hbodd : b%2=1 := by omega
          exact ⟨by omega,hbodd,hsum⟩
        · by_cases haeven : a%2=0
          · have hcase : 4≤y ∧ ∃ n:Nat,
                x+y=2^n*(2*(a-1)+6) ∧
                (2*b-a+3)+(2*(a-1)+6)+3*n=x+2*y := by
              simpa [BB6.Agent46.sectionPreimageAll,ha0,ha1,hb0,hdirect,haeven] using hpre
            rcases hcase with ⟨_,n,hsum,_⟩
            have hfactor : 4∣2*(a-1)+6 := by
              refine ⟨a/2+1,?_⟩
              omega
            have hone : 1∣2^n := ⟨2^n,by simp⟩
            have hdiv : 4∣2^n*(2*(a-1)+6) := by
              have h := Nat.mul_dvd_mul hone hfactor
              simpa using h
            have hmod : (x+y)%4=0 := by
              rw [hsum]
              exact Nat.mod_eq_zero_of_dvd hdiv
            have hxy4 : (x+y)%4=3 := by omega
            omega
          · have hcase :
              (y=3 ∧ ∃ n:Nat, x+6=2^n*(2*(a-1)+8) ∧
                (2*b-a+3)+(2*(a-1)+8)+3*n=x+10) ∨
              (5≤y ∧ ∃ n:Nat, x+y+1=2^n*(2*(a-1)+8) ∧
                (2*b-a+3)+(2*(a-1)+8)+3*n=x+2*y+2) := by
              simpa [BB6.Agent46.sectionPreimageAll,ha0,ha1,hb0,hdirect,haeven] using hpre
            rcases hcase with ⟨hy3,_⟩ | ⟨_,n,hsum,hcost⟩
            · omega
            · have hfactor : 4∣2*(a-1)+8 := by
                refine ⟨(a-1)/2+2,?_⟩
                omega
              have hnle : n≤1 := by
                by_cases hn2 : 2≤n
                · have hpow4 : 4∣2^n := by
                    change (2:Nat)^2 ∣ 2^n
                    exact Nat.pow_dvd_pow (a:=2) (m:=2) (n:=n) hn2
                  have hdiv16 : 16∣2^n*(2*(a-1)+8) := by
                    have h := Nat.mul_dvd_mul hpow4 hfactor
                    simpa only [show 4*4=16 by decide] using h
                  have hmod : (x+y+1)%16=0 := by
                    rw [hsum]
                    exact Nat.mod_eq_zero_of_dvd hdiv16
                  omega
                · omega
              have hnodd : n%2=1 := by omega
              have hn1 : n=1 := by omega
              have hEq : x+y+1=4*a+12 := by
                rw [hsum,hn1]
                omega
              have ha8 : a%8=3 := by omega
              have hcost' : 2*b+a+12=x+2*y+2 := by
                rw [hn1] at hcost
                omega
              have h2b : 2*b=3*a+y+1 := by omega
              have hbmod : (2*b)%8=6 := by rw [h2b]; omega
              have hb4 : b%4=3 := by omega
              have hb5 : 5≤b := by omega
              have hsum : (a+b)%4=2 := by omega
              exact ⟨hb5,by omega,hsum⟩

/-- The full exceptional sum-seven high cylinder is unreachable.
    The only arithmetic hypotheses are m >= 5, m = 1 (mod 4), and
    (j+8) = (3*m+1) (mod 32). -/
theorem sum7_high_blank_unreachable_of_congruence (j m : Nat)
    (hm5 : 5≤m) (hm4 : m%4=1)
    (hrel : (j+8)%32=(3*m+1)%32) :
    ¬ BB6.Agent3.CReach (2*j+3) (highK j m) := by
  let x : Nat := 2*j+3
  let y : Nat := highK j m
  obtain ⟨hy12,hy8,hxy8,hS32,hx4⟩ :=
    sum7_target_residues_of_congruence j m hm5 hm4 hrel
  have hS16 : (x+y+1)%16=8 := by omega
  intro hreach
  rcases hreach with ⟨time,ht⟩
  cases time with
  | zero =>
      simp [BB6.Agent8Section.run] at ht
      omega
  | succ n =>
      have hstep :
          ∃ a b, BB6.Agent8Section.run BB6.Agent46.secNext n (some (5,1)) =
              some (a,b) ∧
            BB6.Agent46.secNext (a,b)=some (x,y) := by
        cases hprev : BB6.Agent8Section.run BB6.Agent46.secNext n (some (5,1)) with
        | none =>
            simp [BB6.Agent8Section.run, hprev] at ht
        | some p =>
            rcases p with ⟨a,b⟩
            refine ⟨a,b,rfl,?_⟩
            simpa [BB6.Agent8Section.run, hprev] using ht
      rcases hstep with ⟨a,b,hprev,hnext⟩
      have hpre : BB6.Agent46.sectionPreimageAll a b x y :=
        (BB6.Agent46.section_preimage_all_iff a b x y).mp hnext
      obtain ⟨hb5,hbodd,hsum⟩ :=
        sum7_every_parent_odd_image x y a b hy12 hxy8 hS16 hS32 hx4 hy8 hpre
      cases n with
      | zero =>
          simp [BB6.Agent8Section.run] at hprev
          omega
      | succ t =>
          have himage :=
            BB6.Agent3.blank_section_odd_image t a b hprev hb5 hbodd
          omega

/-- The previously isolated (j,m)=(8,5) mod-32 progression is a
    special case of the full sum-seven congruence cylinder. -/
theorem sum7_high_blank_unreachable (q r : Nat) :
    ¬ BB6.Agent3.CReach (2*(32*q+8)+3)
      (highK (32*q+8) (32*r+5)) := by
  apply sum7_high_blank_unreachable_of_congruence (32*q+8) (32*r+5)
  · omega
  · omega
  · omega

#print axioms sum7_every_parent_odd_image
#print axioms sum7_high_blank_unreachable
end BB6.Agent19HighEvenRight
