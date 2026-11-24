import SectionAllInverse
import Lean.Elab.Tactic.Omega

namespace BB6.Agent3R0
open BB6.Agent46

/-- The odd-s member of the t=719 q=0 residual left by the A4 fan. -/
def r0X (s : Nat) : Nat := 3389315364793 + 4825264211040*s
def r0Y (s : Nat) : Nat := 839478963638 + 1195142023120*s
def r0M (s : Nat) : Nat := 264299645527 + 376275289635*s
def r0H (s : Nat) : Nat := r0X s + r0Y s + 1

/-- Exact affine arithmetic for the residual: its height is 16*M,
    M is 2 modulo 5, and x+2y is 4 modulo 5. -/
theorem r0_facts (s : Nat) (hs : s%2=1) :
    5 < r0X s ∧ 6 ≤ r0Y s ∧
    r0X s%2=1 ∧ r0Y s%2=0 ∧
    r0H s=16*r0M s ∧ r0M s%5=2 ∧
    (r0X s+2*r0Y s)%5=4 ∧
    48 ≤ r0H s ∧ r0H s%32=0 := by
  have hsdiv : s%2 + 2*(s/2)=s := Nat.mod_add_div s 2
  have hs' : s=2*(s/2)+1 := by omega
  rw [hs']
  dsimp [r0X,r0Y,r0M,r0H]
  omega

private theorem pow_four_mod_five (m : Nat) :
    (4^m)%5=1 ∨ (4^m)%5=4 := by
  induction m with
  | zero =>
      decide
  | succ m ih =>
      have hstep : (4^(m+1))%5 = ((4^m)%5*4)%5 := by
        rw [Nat.pow_succ, Nat.mul_mod]
        simp
      rw [hstep]
      rcases ih with h | h
      · right
        rw [h]
      · left
        rw [h]

private theorem pow_two_double (m : Nat) : 2^(2*m)=4^m := by
  induction m with
  | zero =>
      rfl
  | succ m ih =>
      calc
        2^(2*(m+1)) = 2^(2*m+2) := by congr 1 <;> omega
        _ = 2^(2*m)*2^2 := by rw [Nat.pow_add]
        _ = 4^m*4 := by rw [ih]; rfl
        _ = 4^(m+1) := by rw [Nat.pow_succ]; rfl

private theorem pow_two_even_mod_five_ne_two (n : Nat)
    (hn : n%2=0) : (2^n)%5≠2 := by
  have hn' : n=2*(n/2) := by omega
  rw [hn',pow_two_double]
  rcases pow_four_mod_five (n/2) with h | h <;> omega

/-- Complete original-source inverse fan for the odd-s R0 family.
    Besides the direct parent, every possible parent is an odd-a high
    bounce parent of odd depth. The exceptional a=1 branch is removed
    uniformly by the exact mod-5 phase. -/
theorem r0_parent_fan (s a k : Nat) (hs : s%2=1)
    (hedge : secNext (a,k)=some (r0X s,r0Y s)) :
    (a=r0X s+r0Y s-2 ∧ k=(r0Y s-2)/2) ∨
    (∃ n : Nat, n%2=1 ∧ 3≤a ∧ a%2=1 ∧ 0<k ∧ a<2*k ∧
      r0H s=2^(n+1)*(a+3) ∧
      2*k+a+9+3*n=r0X s+2*r0Y s+2) := by
  obtain ⟨hx,hy,hxodd,hyeven,hH16,hM5,hX5,hbig,hH32⟩ := r0_facts s hs
  have hpre := (section_preimage_all_iff a k (r0X s) (r0Y s)).mp hedge
  by_cases ha0 : a=0
  · by_cases hk0 : k=0
    · simp [sectionPreimageAll,ha0,hk0] at hpre
    · by_cases hk1 : k=1
      · simp [sectionPreimageAll,ha0,hk0,hk1] at hpre
        omega
      · have hcase :
          4≤r0Y s ∧ ∃ n : Nat,
            r0X s+r0Y s=2^n*8 ∧
            (2*k+1)+8+3*n=r0X s+2*r0Y s := by
          simpa [sectionPreimageAll,ha0,hk0,hk1] using hpre
        rcases hcase with ⟨_,n,hsum,_⟩
        have hodd : (r0X s+r0Y s)%2=1 := by omega
        have heven : (2^n*8)%2=0 := by omega
        omega
  · by_cases ha1 : a=1
    · by_cases hk0 : k=0
      · simp [sectionPreimageAll,ha0,ha1,hk0] at hpre
        omega
      · by_cases hk1 : k=1
        · simp [sectionPreimageAll,ha0,ha1,hk0,hk1] at hpre
          omega
        · by_cases hk2 : k=2
          · simp [sectionPreimageAll,ha0,ha1,hk0,hk1,hk2] at hpre
            omega
          · by_cases hk3 : k=3
            · simp [sectionPreimageAll,ha0,ha1,hk0,hk1,hk2,hk3] at hpre
              omega
            · have hcase :
                (r0Y s=3 ∧ ∃ n : Nat,
                  r0X s+6=2^n*16 ∧
                  (2*k-3)+16+3*n=r0X s+10) ∨
                (5≤r0Y s ∧ ∃ n : Nat,
                  r0H s=2^n*16 ∧
                  (2*k-3)+16+3*n=r0X s+2*r0Y s+2) := by
                simpa [sectionPreimageAll,r0H,ha0,ha1,hk0,hk1,hk2,hk3] using hpre
              rcases hcase with ⟨hy3,_⟩ | ⟨_,n,hsum,hcost⟩
              · omega
              · have hnEven : n%2=0 := by omega
                have hMpow : r0M s=2^n := by
                  have hEq : 16*r0M s=2^n*16 := by
                    calc
                      16*r0M s=r0H s := by omega
                      _=2^n*16 := hsum
                  omega
                have hbad := hM5
                rw [hMpow] at hbad
                exact False.elim ((pow_two_even_mod_five_ne_two n hnEven) hbad)
    · have ha2 : 2≤a := by omega
      by_cases hk0 : k=0
      · simp [sectionPreimageAll,ha0,ha1,hk0] at hpre
        omega
      · by_cases hlow : 2*k≤a
        · have hcase : r0X s=a-2*k ∧ r0Y s=2*k+2 := by
            simpa [sectionPreimageAll,ha0,ha1,hk0,hlow] using hpre
          rcases hcase with ⟨hx',hy'⟩
          left
          constructor <;> omega
        · by_cases haeven : a%2=0
          · have hcase :
              4≤r0Y s ∧ ∃ n : Nat,
                r0X s+r0Y s=2^n*(2*(a-1)+6) ∧
                (2*k-a+3)+(2*(a-1)+6)+3*n=r0X s+2*r0Y s := by
              simpa [sectionPreimageAll,ha0,ha1,hk0,hlow,haeven] using hpre
            rcases hcase with ⟨_,n,hsum,_⟩
            have hdiv : 2∣2^n*(2*(a-1)+6) := by
              refine ⟨2^n*(a+2),?_⟩
              calc
                2^n*(2*(a-1)+6)=2^n*(2*(a+2)) := by congr 1 <;> omega
                _=2*(2^n*(a+2)) := by ac_rfl
            have hmod : (r0X s+r0Y s)%2=0 := by
              rw [hsum]
              exact Nat.mod_eq_zero_of_dvd hdiv
            have hodd : (r0X s+r0Y s)%2=1 := by omega
            omega
          · have haodd : a%2=1 := by omega
            have hcase :
              (r0Y s=3 ∧ ∃ n : Nat,
                r0X s+6=2^n*(2*(a-1)+8) ∧
                (2*k-a+3)+(2*(a-1)+8)+3*n=r0X s+10) ∨
              (5≤r0Y s ∧ ∃ n : Nat,
                r0H s=2^n*(2*(a-1)+8) ∧
                (2*k-a+3)+(2*(a-1)+8)+3*n=r0X s+2*r0Y s+2) := by
              simpa [sectionPreimageAll,r0H,ha0,ha1,hk0,hlow,haeven] using hpre
            rcases hcase with ⟨hy3,_⟩ | ⟨_,n,hsum,hcost⟩
            · omega
            · have hnOdd : n%2=1 := by omega
              have hHfan : r0H s=2^(n+1)*(a+3) := by
                calc
                  r0H s=2^n*(2*(a-1)+8) := hsum
                  _=2^n*(2*(a+3)) := by congr 1 <;> omega
                  _=2^(n+1)*(a+3) := by
                    rw [Nat.pow_succ]
                    ac_rfl
              have hcost' : 2*k+a+9+3*n=r0X s+2*r0Y s+2 := by omega
              exact Or.inr ⟨n,hnOdd,by omega,haodd,by omega,by omega,hHfan,hcost'⟩

/-- Exact iff for every original-source predecessor of the odd-s R0 family.
    The reverse direction reconstructs each direct or odd-bounce source edge. -/
theorem r0_section_preimage_iff (s : Nat) (hs : s%2=1) (a k : Nat) :
    secNext (a,k)=some (r0X s,r0Y s) ↔
    (a=r0X s+r0Y s-2 ∧ k=(r0Y s-2)/2) ∨
    (∃ n : Nat, n%2=1 ∧ 3≤a ∧ a%2=1 ∧ 0<k ∧ a<2*k ∧
      r0H s=2^(n+1)*(a+3) ∧
      2*k+a+9+3*n=r0X s+2*r0Y s+2) := by
  constructor
  · exact r0_parent_fan s a k hs
  · rintro (hdir | ⟨n,hn,ha3,haodd,hkpos,hregion,hH,hcost⟩)
    · rcases hdir with ⟨rfl,rfl⟩
      have ha0 : r0X s+r0Y s-2≠0 := by
        have hf := r0_facts s hs
        omega
      have ha1 : r0X s+r0Y s-2≠1 := by
        have hf := r0_facts s hs
        omega
      have hk0 : (r0Y s-2)/2≠0 := by
        have hf := r0_facts s hs
        omega
      have hlow : 2*((r0Y s-2)/2)≤r0X s+r0Y s-2 := by
        have hf := r0_facts s hs
        omega
      have hpre : sectionPreimageAll (r0X s+r0Y s-2) ((r0Y s-2)/2)
          (r0X s) (r0Y s) := by
        simp [sectionPreimageAll,ha0,ha1,hk0,hlow]
        obtain ⟨_,hy,_,hyeven,_,_,_,_,_⟩ := r0_facts s hs
        omega
      exact (section_preimage_all_iff _ _ _ _).mpr hpre
    · have hy5 : 5≤r0Y s := by
        have hf := r0_facts s hs
        omega
      have ha0 : a≠0 := by omega
      have ha1 : a≠1 := by omega
      have hk0 : k≠0 := by omega
      have hlow : ¬2*k≤a := by omega
      have haeven : a%2≠0 := by omega
      have hsum : r0X s+r0Y s+1=2^n*(2*(a-1)+8) := by
        calc
          r0X s+r0Y s+1=2^(n+1)*(a+3) := hH
          _=2^n*(2*(a+3)) := by
            rw [Nat.pow_succ]
            ac_rfl
          _=2^n*(2*(a-1)+8) := by congr 1 <;> omega
      have hcost' :
          (2*k-a+3)+(2*(a-1)+8)+3*n=r0X s+2*r0Y s+2 := by omega
      have hpre : sectionPreimageAll a k (r0X s) (r0Y s) := by
        simp [sectionPreimageAll,ha0,ha1,hk0,hlow,haeven]
        exact Or.inr ⟨hy5,n,hsum,hcost'⟩
      exact (section_preimage_all_iff a k (r0X s) (r0Y s)).mpr hpre

/-- Lossless blank-root reachability split: the R0 target is reachable
    exactly when its direct parent is reachable or one of the explicit
    odd-depth high-bounce parents is reachable. -/
theorem r0_blank_reach_iff (s : Nat) (hs : s%2=1) :
    (∃ time, BB6.Agent8Section.run secNext time (some (5,1))=
      some (r0X s,r0Y s)) ↔
    (∃ time, BB6.Agent8Section.run secNext time (some (5,1))=
      some (r0X s+r0Y s-2,(r0Y s-2)/2)) ∨
    (∃ n a k time, n%2=1 ∧ 3≤a ∧ a%2=1 ∧ 0<k ∧ a<2*k ∧
      r0H s=2^(n+1)*(a+3) ∧
      2*k+a+9+3*n=r0X s+2*r0Y s+2 ∧
      BB6.Agent8Section.run secNext time (some (5,1))=some (a,k)) := by
  constructor
  · rintro ⟨time,hrun⟩
    cases time with
    | zero =>
        simp [BB6.Agent8Section.run] at hrun
        obtain ⟨hx,hy,_,_,_,_,_,_,_⟩ := r0_facts s hs
        omega
    | succ time =>
        cases hp : BB6.Agent8Section.run secNext time (some (5,1)) with
        | none =>
            simp [BB6.Agent8Section.run,hp] at hrun
        | some p =>
            rcases p with ⟨a,k⟩
            have hedge : secNext (a,k)=some (r0X s,r0Y s) := by
              simpa [BB6.Agent8Section.run,hp] using hrun
            rcases (r0_section_preimage_iff s hs a k).mp hedge with hdir | hhigh
            · rcases hdir with ⟨ha,hk⟩
              left
              refine ⟨time,?_⟩
              simpa [ha,hk] using hp
            · rcases hhigh with ⟨n,hn,ha,haodd,hkpos,hregion,hH,hcost⟩
              right
              exact ⟨n,a,k,time,hn,ha,haodd,hkpos,hregion,hH,hcost,hp⟩
  · rintro (⟨time,hrun⟩ |
      ⟨n,a,k,time,hn,ha,haodd,hkpos,hregion,hH,hcost,hrun⟩)
    · have hedge :
        secNext (r0X s+r0Y s-2,(r0Y s-2)/2)=some (r0X s,r0Y s) := by
        apply (r0_section_preimage_iff s hs _ _).2
        exact Or.inl ⟨rfl,rfl⟩
      refine ⟨time+1,?_⟩
      simpa [BB6.Agent8Section.run,hrun,hedge]
    · have hedge : secNext (a,k)=some (r0X s,r0Y s) := by
        apply (r0_section_preimage_iff s hs a k).2
        exact Or.inr ⟨n,hn,ha,haodd,hkpos,hregion,hH,hcost⟩
      refine ⟨time+1,?_⟩
      simpa [BB6.Agent8Section.run,hrun,hedge]

/-- Every high-bounce parent in this exact fan satisfies two simultaneous
    mod-5 phase equations; these hold uniformly over all allowed depths. -/
theorem r0_high_parent_mod_five (s a k n : Nat) (hs : s%2=1)
    (hH : r0H s=2^(n+1)*(a+3))
    (hcost : 2*k+a+9+3*n=r0X s+2*r0Y s+2) :
    (2^(n+1)*(a+3))%5=2 ∧
    (2*k+(a+3)+3*n)%5=0 := by
  obtain ⟨_,_,_,_,hH16,hM5,hX5,_,_⟩ := r0_facts s hs
  have hH5 : r0H s%5=2 := by
    rw [hH16]
    omega
  constructor
  · rw [← hH]
    exact hH5
  · omega

#print axioms r0_parent_fan
#print axioms r0_section_preimage_iff
#print axioms r0_blank_reach_iff
#print axioms r0_high_parent_mod_five

end BB6.Agent3R0
