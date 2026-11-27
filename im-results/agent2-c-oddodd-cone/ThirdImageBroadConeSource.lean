import OddOddWedge
import OddOddConeSource
import Lean.Elab.Tactic.Omega

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace BB6.Agent2CThirdBroad

open BB6.Agent46

private theorem odd_depth_lt_three (b n S : Nat)
    (hb : b%2=1) (hb2 : 2≤b) (hs : (S+1)%64=48)
    (h : S+1=2^n*(2*(b-1)+8)) : n<3 := by
  by_cases hn : n<3
  · exact hn
  have hn3 : 3≤n := by omega
  let r := n-3
  have hr : n=r+3 := by dsimp [r]; omega
  have hb4 : (2*(b-1)+8)%4=0 := by omega
  rcases (Nat.dvd_of_mod_eq_zero hb4) with ⟨q,hq⟩
  have hpower : 2^(r+3)=8*2^r := by simp [Nat.pow_add]; omega
  have hmul : 2^(r+3)*(2*(b-1)+8)=32*(2^r*q) := by
    rw [hq,hpower]
    simp only [Nat.mul_assoc,Nat.mul_left_comm,Nat.mul_comm]
  rw [hr,hmul] at h
  omega

private theorem odd_high_source_forbidden (b l A K n : Nat)
    (hb : b%2=1) (hb2 : 2≤b) (hreg : b<2*l)
    (hA : A%8=0) (hQ : (A+K+1)%64=48)
    (hS : A+K+1=2^n*(2*(b-1)+8))
    (hC : (2*l-b+3)+(2*(b-1)+8)+3*n=A+2*K+2) :
    5≤l ∧ l%2=1 ∧ (b+l)%4=2 := by
  have hn := odd_depth_lt_three b n (A+K) hb hb2 hQ hS
  have hn1 : n≠1 := by
    intro h1
    subst n
    simp at hS hC
    omega
  have h02 : n=0 ∨ n=2 := by omega
  rcases h02 with h0|h2
  · subst n
    simp at hS hC
    omega
  · subst n
    simp at hS hC
    omega

private theorem no_even_source (b n S : Nat)
    (hs : S%2=1) (h : S=2^n*(2*(b-1)+6)) : False := by
  have he : 2*(b-1)+6=2*((b-1)+3) := by omega
  rw [he] at h
  have ht : 2^n*(2*((b-1)+3))=2*(2^n*((b-1)+3)) := by ac_rfl
  rw [ht] at h
  omega

private theorem no_zero_source (S n : Nat)
    (hs : S%2=1) (h : S=2^n*8) : False := by
  have ht : 2^n*8=2*(2^n*4) := by omega
  rw [ht] at h
  omega

private theorem no_one_source (S n : Nat)
    (hs : (S+1)%64=48) (h : S+1=2^n*16) : False := by
  cases n with
  | zero =>
      simp at h
      omega
  | succ n =>
      cases n with
      | zero =>
          simp at h
          omega
      | succ n =>
          have he : 2^(n+2)*16=64*2^n := by
            have hp : 2^(n+2)=2^n*4 := by
              rw [Nat.pow_add]
            rw [hp]
            calc
              (2^n*4)*16=(4*16)*2^n := by ac_rfl
              _=64*2^n := by rfl
          rw [he] at h
          omega

/-- An original Machine C section state with left counter 16 modulo 128
    and right counter 31 modulo 64 has no allowable predecessor unless
    that predecessor has the previously proven impossible odd-image
    residue 2 modulo 4.  The proof exhausts exceptional and every
    unbounded bounce-depth branch of the unchanged source criterion. -/
theorem all_parent_forbidden (b l A K : Nat)
    (hA : A%8=0) (hQ : (A+K+1)%64=48)
    (h : BB6.Agent46.sectionPreimageCriterion b l A K) :
    5≤l ∧ l%2=1 ∧ (b+l)%4=2 := by
  have hsodd : (A+K)%2=1 := by omega
  have hsval : (A+K+1)%64=48 := hQ
  unfold BB6.Agent46.sectionPreimageCriterion at h
  by_cases hb0 : b=0
  · simp only [if_pos hb0] at h
    by_cases hl0 : l=0
    · simp [hl0] at h
    by_cases hl1 : l=1
    · simp only [if_neg hl0,if_pos hl1] at h
      omega
    simp only [if_neg hl0,if_neg hl1] at h
    rcases h with ⟨n,hS,_⟩
    exact False.elim (no_zero_source (A+K) n hsodd hS)
  by_cases hb1 : b=1
  · simp only [if_neg hb0,if_pos hb1] at h
    by_cases hl0 : l=0
    · simp [hl0] at h
    by_cases hl1 : l=1
    · simp [hl0,hl1] at h
    by_cases hl2 : l=2
    · simp only [if_neg hl0,if_neg hl1,if_pos hl2] at h
      omega
    by_cases hl3 : l=3
    · simp only [if_neg hl0,if_neg hl1,if_neg hl2,if_pos hl3] at h
      omega
    simp only [if_neg hl0,if_neg hl1,if_neg hl2,if_neg hl3] at h
    rcases h with ⟨n,hS,_⟩
    exact False.elim (no_one_source (A+K) n hsval hS)
  have hb2 : 2≤b := by omega
  simp only [if_neg hb0,if_neg hb1] at h
  by_cases hl0 : l=0
  · simp [hl0] at h
  simp only [if_neg hl0] at h
  by_cases hreg : 2*l≤b
  · simp only [if_pos hreg] at h
    rcases h with ⟨_,hK0⟩
    omega
  simp only [if_neg hreg] at h
  by_cases hbe : b%2=0
  · simp only [if_pos hbe] at h
    rcases h with ⟨n,hS,_⟩
    exact False.elim (no_even_source b n (A+K) hsodd hS)
  simp only [if_neg hbe] at h
  rcases h with ⟨n,hS,hC⟩
  exact odd_high_source_forbidden b l A K n (by omega) hb2 (by omega)
    hA hQ hS hC

/-- New genuine-blank source obstruction, independent of the earlier
    six-sector forced normalizer: the entire high right odd cone
    (A mod128,K mod64)=(16,31) is unreachable at all section times. -/
theorem parent_cone_blank_unreachable (A K time : Nat)
    (hA : A%8=0) (hQ : (A+K+1)%64=48) :
    BB6.Agent8Section.run BB6.Agent46.secNext time (some (5,1)) ≠ some (A,K) := by
  intro h
  cases time with
  | zero =>
      simp [BB6.Agent8Section.run] at h
      omega
  | succ n =>
      cases hp : BB6.Agent8Section.run BB6.Agent46.secNext n (some (5,1)) with
      | none => simp [BB6.Agent8Section.run,hp] at h
      | some p =>
          rcases p with ⟨b,l⟩
          have he : BB6.Agent46.secNext (b,l)=some (A,K) := by
            simpa [BB6.Agent8Section.run,hp] using h
          have hcrit :=
            (BB6.Agent46.complete_section_inverse b l A K (by omega)).mp he
          obtain ⟨hl5,hlodd,hsum⟩ :=
            all_parent_forbidden b l A K hA hQ hcrit
          cases n with
          | zero =>
              simp [BB6.Agent8Section.run] at hp
              omega
          | succ nn =>
              have hi := BB6.Agent3.blank_section_odd_image nn b l hp hl5 hlodd
              omega

/-- The exact odd/odd unique-predecessor equations transport this
    much broader section congruence cylinder into a missing parent cone. -/
theorem first_parent_cone (a k x y : Nat)
    (hs : (x+y)%16=4)
    (hq : (3*(x+y)+2*y)%256=206) (hy5 : 5≤y)
    (hedge : BB6.Agent46.secNext (a,k)=some (x,y)) :
    a%8=0 ∧ (a+k+1)%64=48 := by
  have hxodd : x%2=1 := by omega
  have hyodd : y%2=1 := by omega
  have hs8 : (x+y)%8=4 := by omega
  obtain ⟨h1,h2⟩ := BB6.Agent3.oddodd_parent_equations
    a k x y hxodd hyodd hy5 hs8 hedge
  omega

/-- The new broad third-image cylinder is unconditionally unreachable
    from Machine C's genuine blank section, at every return time. -/
theorem third_image_blank_unreachable (x y time : Nat)
    (hs : (x+y)%16=4)
    (hq : (3*(x+y)+2*y)%256=206) (hy5 : 5≤y) :
    BB6.Agent8Section.run BB6.Agent46.secNext time (some (5,1)) ≠ some (x,y) := by
  intro h
  cases time with
  | zero =>
      simp [BB6.Agent8Section.run] at h
      omega
  | succ n =>
      cases hp : BB6.Agent8Section.run BB6.Agent46.secNext n (some (5,1)) with
      | none => simp [BB6.Agent8Section.run,hp] at h
      | some p =>
          rcases p with ⟨a,k⟩
          have he : BB6.Agent46.secNext (a,k)=some (x,y) := by
            simpa [BB6.Agent8Section.run,hp] using h
          obtain ⟨ha,hqparent⟩ := first_parent_cone a k x y hs hq hy5 he
          exact (parent_cone_blank_unreachable a k n ha hqparent) hp

private theorem power_lower (m : Nat) : 4*m+4 ≤ 2^(2*m+2) := by
  induction m with
  | zero => decide
  | succ m ih =>
    rw [show 2*(m+1)+2=2*m+2+2 by omega, Nat.pow_add]
    change 4*(m+1)+4 ≤ 2^(2*m+2)*4
    omega

/-- Broad exact high stopping pullback. Modulo 256 every target with
    m=2 mod4 and j=15m+222 mod256 lies in this strict third-image gap. -/
theorem high_stop_coordinates (j m k : Nat)
    (hm6 : 6≤m) (hm4 : m%4=2)
    (hj : j%256=(15*m+222)%256)
    (hstop : k+j+3*m+5=2^(2*m+2)*(j+3)) :
    (2*j+3+k)%16=4 ∧
      (3*(2*j+3+k)+2*k)%256=206 ∧ 5≤k := by
  have hp8 : 2^8 ∣ 2^(2*m+2) := Nat.pow_dvd_pow 2 (by omega)
  have hp256 : 256 ∣ 2^(2*m+2) := by
    simpa only [show (2:Nat)^8=256 by decide] using hp8
  have hdiv : 256 ∣ k+j+3*m+5 := by
    rw [hstop]
    exact Nat.dvd_trans hp256 (Nat.dvd_mul_right _ _)
  have hzero : (k+j+3*m+5)%256=0 := Nat.mod_eq_zero_of_dvd hdiv
  have hlower := power_lower m
  have hj0 := Nat.mul_le_mul_right j (by omega : 1≤2^(2*m+2))
  have hjbase : j≤2^(2*m+2)*j := by simpa using hj0
  have hm : 3*m+10≤2^(2*m+2)*3 := by
    have h3 := Nat.mul_le_mul_right 3 hlower
    omega
  rw [Nat.mul_add] at hstop
  constructor
  · omega
  constructor
  · omega
  · omega

/-- New source-proven infinite high-halting nonreachability family:
    m>=6, m=2 mod4, j=15m+222 mod256. Lattice density 1/1024.
    Disjoint from both previous Agent34 third-image classes. -/
theorem high_stop_blank_unreachable (j m k time : Nat)
    (hm6 : 6≤m) (hm4 : m%4=2)
    (hj : j%256=(15*m+222)%256)
    (hstop : k+j+3*m+5=2^(2*m+2)*(j+3)) :
    BB6.Agent8Section.run BB6.Agent46.secNext time (some (5,1)) ≠
      some (2*j+3,k) := by
  obtain ⟨hs,hq,hy5⟩ := high_stop_coordinates j m k hm6 hm4 hj hstop
  exact third_image_blank_unreachable (2*j+3) k time hs hq hy5

#print axioms all_parent_forbidden
#print axioms parent_cone_blank_unreachable
#print axioms first_parent_cone
#print axioms third_image_blank_unreachable
#print axioms high_stop_coordinates
#print axioms high_stop_blank_unreachable

end BB6.Agent2CThirdBroad
