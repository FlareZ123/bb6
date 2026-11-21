import MixedOdd16TwoOrbit
import EvenOddFourExact
import OddOddLowVal
import EvenRightUnique
import Agent3CImage
import Lean.Elab.Tactic.Omega

set_option maxHeartbeats 1000000
set_option maxRecDepth 65536

namespace BB6.Agent3Root32HighStopR10592LCore
open BB6.Agent46

def RunReach (x y : Nat) : Prop :=
  ∃ n, BB6.Agent8Section.run secNext n (some (5,1)) = some (x,y)

theorem run_parent_of_left_gt5 (x y : Nat) (hx : 5<x)
    (hr : RunReach x y) :
    ∃ a k, RunReach a k ∧ secNext (a,k)=some (x,y) := by
  rcases hr with ⟨time,ht⟩
  cases time with
  | zero => simp [BB6.Agent8Section.run] at ht; omega
  | succ n =>
    cases hp : BB6.Agent8Section.run secNext n (some (5,1)) with
    | none => simp [BB6.Agent8Section.run,hp] at ht
    | some p =>
      rcases p with ⟨a,k⟩
      refine ⟨a,k,⟨n,hp⟩,?_⟩
      simpa [BB6.Agent8Section.run,hp] using ht

theorem run_no_odd_sum_one (x y : Nat)
    (_hx : 5<x) (hy : 5≤y) (ho : y%2=1)
    (hsum : (x+y)%4=1) : ¬ RunReach x y := by
  intro hr
  rcases hr with ⟨time,ht⟩
  cases time with
  | zero => simp [BB6.Agent8Section.run] at ht; omega
  | succ n =>
    have hi := BB6.Agent3.blank_section_odd_image n x y ht hy ho
    omega

def Lx (t : Nat) : Nat := 5065196640*t+1358307257
def Ly (t : Nat) : Nat := 990617040*t+265648583
def P0x (t : Nat) : Nat := 3027906840*t+811977918
def P0y (t : Nat) : Nat := 2009261940*t+538813249
def P2x (t : Nat) : Nat := 756976710*t+202994478
def P2y (t : Nat) : Nat := 3144727005*t+843304966
def A0x (t : Nat) : Nat := 2518584390*t+675395581
def A0y (t : Nat) : Nat := 2263923165*t+607104414
def Qx (v : Nat) : Nat := 9565015110*v+7815011328
def Qy (v : Nat) : Nat := 9310353885*v+7606942617
def Qpx (m : Nat) : Nat := 151002951960*m+147549536908
def Qpy (m : Nat) : Nat := 37241415540*m+36389709905

theorem no_parent_evenodd_sumplusone_two (x y : Nat)
    (hx5 : 5<x) (hx : x%2=0) (hy : y%2=1) (hy5 : 5≤y)
    (hsum : (x+y)%2=1) (hplus : (x+y+1)%4=2) :
    ¬ ∃ a k, secNext (a,k)=some (x,y) := by
  rintro ⟨a,k,hedge⟩
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
        have heven : (x+y)%2=0 := by rw [hpow]; simp [Nat.mul_mod]
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
            · have hcase :
                  (y=3 ∧ ∃ n : Nat, x+6=2^n*16 ∧
                    (2*k-3)+16+3*n=x+10) ∨
                  (5≤y ∧ ∃ n : Nat,
                    x+y+1=2^n*16 ∧
                    (2*k-3)+16+3*n=x+2*y+2) := by
                simpa [sectionPreimageAll,ha0,ha1,hk0,hk1,hk2,hk3] using hp
              rcases hcase with ⟨hy3,_⟩ | ⟨_,n,hpow,_⟩
              · omega
              · have hzero : (x+y+1)%4=0 := by
                  rw [hpow]
                  simp [Nat.mul_mod]
                omega
    · have ha2 : 2≤a := by omega
      by_cases hk0 : k=0
      · simp [sectionPreimageAll,ha0,ha1,hk0] at hp
        omega
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
            have heven : (x+y)%2=0 := by rw [hpow]; simp [Nat.mul_mod]
            omega
          · have hcase :
                (y=3 ∧ ∃ n : Nat, x+6=2^n*(2*(a-1)+8) ∧
                  (2*k-a+3)+(2*(a-1)+8)+3*n=x+10) ∨
                (5≤y ∧ ∃ n : Nat,
                  x+y+1=2^n*(2*(a-1)+8) ∧
                  (2*k-a+3)+(2*(a-1)+8)+3*n=x+2*y+2) := by
              simpa [sectionPreimageAll,ha0,ha1,hk0,hlow,haeven] using hp
            rcases hcase with ⟨hy3,_⟩ | ⟨_,n,hpow,_⟩
            · omega
            · have hfac : 4∣2*(a-1)+8 := by
                refine ⟨(a-1)/2+2,?_⟩
                omega
              have hzero : (x+y+1)%4=0 := by
                rcases hfac with ⟨q,hq⟩
                rw [hpow,hq]
                simp [Nat.mul_mod]
              omega

theorem P2_unreachable (m : Nat) :
    ¬ RunReach (P2x (32*m+31)) (P2y (32*m+31)) := by
  intro hr
  have hx5 : 5<P2x (32*m+31) := by dsimp [P2x]; omega
  have hx : P2x (32*m+31)%2=0 := by dsimp [P2x]; omega
  have hy : P2y (32*m+31)%2=1 := by dsimp [P2y]; omega
  have hy5 : 5≤P2y (32*m+31) := by dsimp [P2y]; omega
  have hsum : (P2x (32*m+31)+P2y (32*m+31))%2=1 := by
    dsimp [P2x,P2y]
    omega
  have hplus : (P2x (32*m+31)+P2y (32*m+31)+1)%4=2 := by
    dsimp [P2x,P2y]
    omega
  obtain ⟨a,k,hprev,hstep⟩ :=
    run_parent_of_left_gt5 (P2x (32*m+31)) (P2y (32*m+31)) hx5 hr
  exact no_parent_evenodd_sumplusone_two
    (P2x (32*m+31)) (P2y (32*m+31)) hx5 hx hy hy5 hsum hplus ⟨a,k,hstep⟩

theorem L_unreachable_t31_mod32 (m : Nat) :
    ¬ RunReach (Lx (32*m+31)) (Ly (32*m+31)) := by
  let t := 32*m+31
  have hx : Lx t%2=1 := by dsimp [Lx]; omega
  have hy : Ly t%2=1 := by dsimp [Ly]; omega
  have hy64 : 64≤Ly t := by dsimp [Ly]; omega
  have hmod : (Lx t+Ly t)%32=16 := by dsimp [Lx,Ly]; omega
  intro hL
  have hsplit0 := BB6.Agent3.oddodd_sum16_blank_reach_iff
    (Lx t) (Ly t) hx hy hy64 hmod
  have hsplit : RunReach (Lx t) (Ly t) ↔
      RunReach (P0x t) (P0y t) ∨ RunReach (P2x t) (P2y t) := by
    have hP0x : (Lx t+Ly t-4)/2=P0x t := by dsimp [Lx,Ly,P0x,P0y]; omega
    have hP0y : (Lx t+3*Ly t-10)/4=P0y t := by dsimp [Lx,Ly,P0x,P0y]; omega
    have hP2x : (Lx t+Ly t-16)/8=P2x t := by dsimp [Lx,Ly,P2x,P2y]; omega
    have hP2y : (7*Lx t+15*Ly t-88)/16=P2y t := by dsimp [Lx,Ly,P2x,P2y]; omega
    simpa [RunReach,BB6.Agent3.CReach,hP0x,hP0y,hP2x,hP2y] using hsplit0
  have hP2not : ¬ RunReach (P2x t) (P2y t) := by
    simpa [t] using P2_unreachable m
  have hP0 : RunReach (P0x t) (P0y t) := (hsplit.mp hL).resolve_right hP2not
  have hP0x : P0x t%2=0 := by dsimp [P0x]; omega
  have hP0y : P0y t%2=1 := by dsimp [P0y]; omega
  have hP0y5 : 5≤P0y t := by dsimp [P0y]; omega
  have hP0mod : (P0x t+P0y t+1)%8=4 := by dsimp [P0x,P0y]; omega
  have hA0 : RunReach (A0x t) (A0y t) := by
    have hiff := BB6.Agent3.evenodd_four_blank_reach_iff
      (P0x t) (P0y t) hP0x hP0y hP0y5 hP0mod
    have hA0x : (P0x t+P0y t-5)/2=A0x t := by dsimp [P0x,P0y,A0x]; omega
    have hA0y : (P0x t+3*P0y t-9)/4=A0y t := by dsimp [P0x,P0y,A0y]; omega
    simpa [RunReach,hA0x,hA0y] using hiff.mp hP0
  have hA0x : A0x t%2=1 := by dsimp [A0x]; omega
  have hA0y : A0y t%2=1 := by dsimp [A0y]; omega
  have hA0y5 : 5≤A0y t := by dsimp [A0y]; omega
  have hA0sum4 : (A0x t+A0y t)%4=0 := by dsimp [A0x,A0y]; omega
  have hA0sum16 : (A0x t+A0y t)%16=8 := by dsimp [A0x,A0y]; omega
  have hA0size : 24≤A0x t+A0y t := by dsimp [A0x,A0y]; omega
  let v := 8*m+7
  have hQ : RunReach (Qx v) (Qy v) := by
    have hiff := BB6.Agent3.oddodd_lowval_blank_reach_iff
      (A0x t) (A0y t) hA0x hA0y hA0y5 hA0sum4 (by omega) hA0size
    have hQx : (A0x t+A0y t-4)/2=Qx v := by
      dsimp [A0x,A0y,Qx,v,t]
      omega
    have hQy : (A0x t+3*A0y t-10)/4=Qy v := by
      dsimp [A0x,A0y,Qy,v,t]
      omega
    simpa [RunReach,hQx,hQy] using hiff.mp hA0
  have hQy6 : 6≤Qy v := by dsimp [Qy,v]; omega
  have hQyeven : Qy v%2=0 := by dsimp [Qy,v]; omega
  have hQsum : (Qx v+Qy v)%8=6 := by dsimp [Qx,Qy,v]; omega
  have hQprime : RunReach (Qx v+Qy v-2) ((Qy v-2)/2) := by
    have hiff := BB6.Agent15.blank_reach_iff_even_right
      (Qx v) (Qy v) hQy6 hQyeven (by omega) (by omega)
    exact hiff.mp hQ
  have hQpx : Qx v+Qy v-2=Qpx m := by dsimp [Qx,Qy,Qpx,v]; omega
  have hQpy : (Qy v-2)/2=Qpy m := by dsimp [Qy,Qpy,v]; omega
  have hQpx5 : 5<Qpx m := by dsimp [Qpx]; omega
  have hQpy5 : 5≤Qpy m := by dsimp [Qpy]; omega
  have hQpyodd : Qpy m%2=1 := by dsimp [Qpy]; omega
  have hQpsum : (Qpx m+Qpy m)%4=1 := by dsimp [Qpx,Qpy]; omega
  exact (run_no_odd_sum_one (Qpx m) (Qpy m) hQpx5 hQpy5 hQpyodd hQpsum) (by simpa [hQpx,hQpy] using hQprime)

#print axioms no_parent_evenodd_sumplusone_two
#print axioms P2_unreachable
#print axioms L_unreachable_t31_mod32

end BB6.Agent3Root32HighStopR10592LCore
