import EvenOddLowStopEvenReachIff
import EvenOddLowStopSecondFanSpecialized
import EvenOddAllValuationParent
import LowM67All1583Criterion
import Lean.Elab.Tactic.Omega

set_option maxHeartbeats 0

namespace BB6.Agent29Z78Q6

open BB6.Agent46
open BB6.Agent13LowSecondFanSpecialized
open BB6.Agent13AllFan

/-- The two 8192-residue classes forced by the z=846 (mod 2048)
    low-stop cylinder both lie in the same first-generation even-z
    source section: P=(173u+24,(339u+47)/2). -/
theorem target_arithmetic (u : Nat)
    (hu : u%8192=3115 ∨ u%8192=7211) :
    (173*u+24)%2=1 ∧
    ((339*u+47)/2)%2=0 ∧
    8≤(339*u+47)/2 ∧
    (173*u+24+(339*u+47)/2+1)%16=8 := by
  omega

/-- High parent of P, followed by its odd/odd low-value inverse.
    The resulting D is even/odd and has mass exactly 32 mod 64. -/
theorem high_parent_arithmetic (u a k : Nat)
    (hu : u%256=43)
    (ha : a%2=1) (ha3 : 3≤a) (hr : a<2*k)
    (hm : 173*u+24+(339*u+47)/2+1=4*(a+3))
    (hc : 2*k+a+10=173*u+24+2*((339*u+47)/2)) :
    k%2=1 ∧ 5≤k ∧
    (a+k)%4=0 ∧ (a+k)%16≠0 ∧ 24≤a+k ∧
    5≤(a+3*k-10)/4 ∧ ((a+3*k-10)/4)%2=1 ∧
    ((a+k-4)/2)%2=0 ∧
    (((a+k-4)/2+(a+3*k-10)/4)%4=3 := by
  have haEq : 8*a=685*u+73 := by omega
  have hkEq : 16*k=3411*u+415 := by omega
  omega

/-- The direct parent of P has a fixed four-edge inverse chain to the
    forbidden odd-right, sum-one blank image. -/
theorem direct_parent_arithmetic (u : Nat)
    (hu : u%8192=3115 ∨ u%8192=7211) :
    let X:=173*u+24
    let Y:=(339*u+47)/2
    let a:=X+Y-2
    let k:=(Y-2)/2
    let e:=(a+k-4)/2
    let f:=(a+3*k-10)/4
    let g:=e+f-2
    let h:=(f-2)/2
    a%2=1 ∧ k%2=1 ∧ 5≤k ∧
    (a+k)%4=0 ∧ (a+k)%16≠0 ∧ 24≤a+k ∧
    6≤f ∧ f%2=0 ∧ (e+f)%8=4 ∧
    5≤h ∧ h%2=1 ∧ (g+h)%4=1 := by
  dsimp
  omega

private theorem not_power_two_of_mod64_32
    (M : Nat) (hbig : 64≤M) (hmod : M%64=32) :
    ∀ t : Nat, M≠2^t := by
  intro t ht
  by_cases hsmall : t<6
  · have hp : 2^t≤2^5 :=
      Nat.pow_le_pow_right (by omega) (by omega)
    have hp32 : (2:Nat)^5=32 := by decide
    omega
  · have hlarge : 6≤t := by omega
    have hd : (2:Nat)^6 ∣ 2^t :=
      Nat.pow_dvd_pow 2 (by omega)
    have hd64 : 64∣2^t := by
      simpa only [show (2:Nat)^6=64 by decide] using hd
    have hzero : M%64=0 := by
      rw [ht]
      exact Nat.mod_eq_zero_of_dvd hd64
    omega

/-- A source parent of D has even bounce depth, and the mass residue
    32 mod 64 leaves only depths zero and two. -/
private theorem depth_zero_or_two
    (x y a k n : Nat)
    (hx : x%2=0) (hy : y%2=1)
    (hmass : x+y+1=2^n*(2*(a-1)+8))
    (hcost : (2*k-a+3)+(2*(a-1)+8)+3*n=x+2*y+2)
    (hn : n%2=0)
    (hmod : (x+y+1)%64=32) :
    n=0 ∨ n=2 := by
  have haOdd : a%2=1 := by omega
  have hmass' : x+y+1=2^(n+1)*(a+3) := by
    calc
      x+y+1=2^n*(2*(a-1)+8) := hmass
      _=2^n*(2*(a+3)) := by congr 1 <;> omega
      _=2^(n+1)*(a+3) := by rw [Nat.pow_succ]
  have haPlusEven : 2∣a+3 := by omega
  obtain ⟨c,hc⟩ := haPlusEven
  have hdiv : 2^(n+2)∣x+y+1 := by
    refine ⟨c,?_⟩
    rw [hmass',hc,Nat.pow_succ]
    ring
  have hnlt : n<4 := by
    by_contra hnot
    have hn4 : 4≤n := by omega
    have hp : (2:Nat)^6∣2^(n+2) :=
      Nat.pow_dvd_pow 2 (by omega)
    have h64 : 64∣x+y+1 := dvd_trans hp hdiv
    have hzero : (x+y+1)%64=0 :=
      Nat.mod_eq_zero_of_dvd h64
    omega
  omega

/-- Every source parent of the even/odd D produced by the high branch
    is excluded. The full all-depth parent theorem is used; the mass
    residue forces n=0 or n=2, with no depth cutoff. -/
private theorem high_D_parents_unreachable
    (u x y : Nat)
    (hu : u%8192=3115 ∨ u%8192=7211)
    (hx : x%2=0) (hy : y%2=1) (hy5 : 5≤y)
    (hbig : 64≤x+y+1) (hmod : (x+y+1)%64=32)
    (hD : BB6.Agent3.CReach x y) :
    False := by
  have hnpow : ∀ t : Nat, x+y+1≠2^t :=
    not_power_two_of_mod64_32 (x+y+1) hbig hmod
  obtain ⟨a,k,hpre,hedge⟩ :=
    BB6.Agent11M0SumZeroVerified.cReach_parent_of_left_gt5
      x y (by omega) hD
  obtain ⟨n,hn,ha3,har,hmass,hcost⟩ :=
    even_odd_nonpower_parent a k x y hx hy hy5 hbig hnpow hedge
  have hncase : n=0 ∨ n=2 :=
    depth_zero_or_two x y a k n hx hy hmass hcost hn hmod
  have haEq : 32*x=4781*u+497 := by omega
  have hyEq : 64*y=11603*u+1231 := by omega
  rcases hncase with hn0 | hn2
  · subst n
    have hmass0 : x+y+1=2*(a+3) := by
      simpa using hmass
    have hcost0 : 2*k+a+9=x+2*y+2 := by omega
    have hbad : 5≤k ∧ k%2=1 ∧ (a+k)%4=2 := by omega
    exact BB6.Agent13TwoParent.odd_forbidden_image
      a k hbad.1 hbad.2.1 (Or.inr hbad.2.2) hpre
  · subst n
    have hmass2 : x+y+1=8*(a+3) := by
      simpa using hmass
    have hcost2 : 2*k+a+15=x+2*y+2 := by omega
    have hgate : 6≤k ∧ k%2=0 ∧
        ((u%8192=3115 ∧ (a+k)%8=5) ∨
         (u%8192=7211 ∧ (a+k)%8=1)) := by omega
    have h0 : (a+k)%8≠0 := by omega
    have h7 : (a+k)%8≠7 := by omega
    have hF := (six_even_right_blank_reach_iff
      a k hgate.1 hgate.2.1 h0 h7).mp hpre
    let fx:=a+k-2
    let fy:=(k-2)/2
    have hF' : BB6.Agent3.CReach fx fy := by
      simpa [fx,fy] using hF
    rcases hu with hu3115 | hu7211
    · have hFfacts :
          fx%2=1 ∧ fy%2=1 ∧ 5≤fy ∧
          (fx+fy)%4=0 ∧ (fx+fy)%16≠0 ∧ 24≤fx+fy := by
        dsimp [fx,fy]
        omega
      have hG := (BB6.Agent3.oddodd_lowval_blank_reach_iff
        fx fy hFfacts.1 hFfacts.2.1 hFfacts.2.2.1
        hFfacts.2.2.2.1 hFfacts.2.2.2.2 (by omega)).mp hF'
      let gx:=(fx+fy-4)/2
      let gy:=(fx+3*fy-10)/4
      have hG' : BB6.Agent3.CReach gx gy := by
        simpa [gx,gy] using hG
      have hbad : 5≤gy ∧ gy%2=1 ∧ (gx+gy)%4=1 := by
        dsimp [gx,gy]
        omega
      exact BB6.Agent13TwoParent.odd_forbidden_image
        gx gy hbad.1 hbad.2.1 (Or.inl hbad.2.2) hG'
    · have hFfacts : fx%2=1 ∧ fy%2=1 ∧
          5≤fy ∧ (fx+fy)%4=2 := by
        dsimp [fx,fy]
        omega
      exact BB6.Agent13TwoParent.odd_forbidden_image
        fx fy hFfacts.2.1 hFfacts.2.2.1
        (Or.inr hFfacts.2.2.2) hF'

/-- The complete P=(173u+24,(339u+47)/2) cylinder is source-unreachable
    for u=3115 or 7211 modulo 8192. The direct and depth-one high
    source parents are both eliminated; the high branch retains all
    possible even bounce depths before forcing n=0 or n=2. -/
theorem payload_unreachable (u : Nat)
    (hu : u%8192=3115 ∨ u%8192=7211) :
    ¬ BB6.Agent3.CReach (173*u+24) ((339*u+47)/2) := by
  obtain ⟨hx,hy,hy8,hm⟩ := target_arithmetic u hu
  intro hroot
  obtain ⟨a,k,hpre,hedge⟩ :=
    BB6.Agent11M0SumZeroVerified.cReach_parent_of_left_gt5
      (173*u+24) ((339*u+47)/2) (by omega) hroot
  rcases (depth_one_or_direct a k (173*u+24) ((339*u+47)/2)
      hx hy hy8 hm).mp hedge with hdir | hhigh
  · obtain ⟨ha,hk⟩ := hdir
    subst a
    subst k
    obtain ⟨haOdd,hkOdd,hk5,h4,h16,hsize,hf6,hfe,hefsum,hh5,hho,hghsum⟩ :=
      direct_parent_arithmetic u hu
    have hE := (BB6.Agent3.oddodd_lowval_blank_reach_iff
      (173*u+24+((339*u+47)/2)-2)
      (((339*u+47)/2-2)/2)
      haOdd hkOdd hk5 h4 h16 hsize).mp hpre
    let e:=(173*u+24+((339*u+47)/2)-2+
        (((339*u+47)/2-2)/2)-4)/2
    let f:=(173*u+24+((339*u+47)/2)-2+
        3*(((339*u+47)/2-2)/2)-10)/4
    have hE' : BB6.Agent3.CReach e f := by
      simpa [e,f] using hE
    have hF := (six_even_right_blank_reach_iff e f hf6 hfe
      (by change (e+f)%8≠0; dsimp [e,f]; omega)
      (by change (e+f)%8≠7; dsimp [e,f]; omega)).mp hE'
    let g:=e+f-2
    let h:=(f-2)/2
    have hF' : BB6.Agent3.CReach g h := by
      simpa [g,h] using hF
    exact BB6.Agent13TwoParent.odd_forbidden_image
      g h hh5 hho (Or.inl hghsum) hF'
  · obtain ⟨ha,ha3,hr,hmass,hcost⟩ := hhigh
    obtain ⟨hkOdd,hk5,h4,h16,hsize,hy5,hyo,hEsum⟩ :=
      high_parent_arithmetic u a k (by omega) ha ha3 hr hmass hcost
    let x:=(a+k-4)/2
    let y:=(a+3*k-10)/4
    have hD : BB6.Agent3.CReach x y := by
      simpa [x,y] using
        (BB6.Agent3.oddodd_lowval_blank_reach_iff
          a k ha hkOdd hk5 h4 h16 hsize).mp hpre
    have hDfacts :
        x%2=0 ∧ y%2=1 ∧ 5≤y ∧
        64≤x+y+1 ∧ (x+y+1)%64=32 := by
      have hu4096 : u%4096=3115 := by omega
      have haEq : 8*a=685*u+73 := by omega
      have hkEq : 16*k=3411*u+415 := by omega
      dsimp [x,y]
      omega
    exact high_D_parents_unreachable u x y hu
      hDfacts.1 hDfacts.2.1 hDfacts.2.2.1
      hDfacts.2.2.2.1 hDfacts.2.2.2.2 hD

/-- Exact arithmetic bridge from the stopping equation to the two
    8192-residue classes used by payload_unreachable. -/
theorem low_stop_arithmetic (z m k : Nat)
    (hm : m=512*z+67) (hz : z%2048=846)
    (hstop : k+3*m+4=2^(2*m+3)) :
    ∃ u, k=256*u+51 ∧
      u+6*z+1=2^(1024*z+129) ∧
      (u%8192=3115 ∨ u%8192=7211) := by
  have hpow : 2^(2*m+3)=256*2^(1024*z+129) := by
    rw [show 2*m+3=(1024*z+129)+8 by omega,Nat.pow_add]
    simp only [show (2:Nat)^8=256 by decide]
    omega
  rw [hpow] at hstop
  have hkmod : k%256=51 := by omega
  let u:=k/256
  have hk : k=256*u+51 := by
    have hh := Nat.mod_add_div k 256
    dsimp [u]
    omega
  have hu : u+6*z+1=2^(1024*z+129) := by omega
  let t:=z/2048
  have hzEq : z=2048*t+846 := by
    have hh := Nat.mod_add_div z 2048
    dsimp [t]
    omega
  have hpowdiv : 8192∣2^(1024*z+129) := by
    have hp : (2:Nat)^13∣2^(1024*z+129) :=
      Nat.pow_dvd_pow 2 (by omega)
    simpa only [show (2:Nat)^13=8192 by decide] using hp
  have hdiv : 8192∣u+6*z+1 := by
    rw [hu]
    exact hpowdiv
  obtain ⟨w,hw⟩ := hdiv
  by_cases htEven : t%2=0
  · have htEq : t=2*(t/2) := by omega
    have hres : u%8192=3115 := by
      have hmod := Nat.mod_add_div u 8192
      rw [hzEq,htEq] at hw
      omega
    exact ⟨u,hk,hu,Or.inl hres⟩
  · have htEq : t=2*(t/2)+1 := by omega
    have hres : u%8192=7211 := by
      have hmod := Nat.mod_add_div u 8192
      rw [hzEq,htEq] at hw
      omega
    exact ⟨u,hk,hu,Or.inr hres⟩

/-- The authentic low-stop family z=846 (mod 2048) is unreachable
    from the blank section. -/
theorem low_stop_m67_z846_mod2048_unreachable
    (z m k : Nat)
    (hm : m=512*z+67) (hz : z%2048=846)
    (hstop : k+3*m+4=2^(2*m+3)) :
    ¬ BB6.Agent3.CReach 1 k := by
  obtain ⟨u,hk,hu,hu8192⟩ := low_stop_arithmetic z m k hm hz hstop
  intro h
  rw [hk] at h
  have hR := BB6.Agent13One307.four_step_to_rectangle u h
  have hP := even_low_ray_reach_iff_unique_parent z u hu (by omega) hR
  exact payload_unreachable u hu8192 hP

/-- The 1583 low-stop criterion gains the disjoint exact cylinder
    m=433219 (mod 1048576), corresponding to z=846 (mod 2048). -/
def lowAllowedSource1585 (m : Nat) : Prop :=
  BB6.Agent13Low1583.lowAllowedSource1583 m ∧ m%1048576≠433219

theorem blank_halts_iff_six_low1585 :
    BB6.CReachBridge.RunHalts ↔
      (∃ m, lowAllowedSource1585 m ∧
        BB6.Agent11SixForced.sixForcedRootDecision 1
          (2^(2*m+3)-(3*m+4))=true) ∨
      (∃ j m, BB6.Agent11SixAll.highAllowed j m ∧
        BB6.Agent11SixForced.sixForcedRootDecision (2*j+3)
          (2^(2*m+2)*(j+3)-(j+3*m+5))=true) := by
  rw [BB6.Agent13Low1583.blank_halts_iff_six_low1583]
  constructor
  · rintro (⟨m,hprior,hroot⟩ | ⟨j,m,hprior,hroot⟩)
    · let k:=2^(2*m+3)-(3*m+4)
      have hr : BB6.Agent3.CReach 1 k :=
        (BB6.Agent11SixForced.sixForcedRootDecision_iff 1 k).mp hroot
      have hstop : k+3*m+4=2^(2*m+3) := by
        dsimp [k]
        have hb := Nat.sub_add_cancel (by
          have hh : 3*m+4≤2^(2*m+3) := by
            induction m with
            | zero => decide
            | succ m ih =>
              have he : 2*(m+1)+3=(2*m+3)+2 := by omega
              rw [he,Nat.pow_add]
              simp only [show (2:Nat)^2=4 by decide]
              omega
          exact hh)
        omega
      have hnon : m%1048576≠433219 := by
        intro hbad
        let z:=m/512
        have hm' : m=512*z+67 := by
          have hmod : m%512=67 := by omega
          have hh := Nat.mod_add_div m 512
          dsimp [z]
          omega
        have hz' : z%2048=846 := by
          rw [hm'] at hbad
          omega
        exact (low_stop_m67_z846_mod2048_unreachable
          z m k hm' hz' hstop) hr
      exact Or.inl ⟨m,⟨hprior,hnon⟩,hroot⟩
    · exact Or.inr ⟨j,m,hprior,hroot⟩
  · rintro (⟨m,⟨hprior,_⟩,hroot⟩ | ⟨j,m,hprior,hroot⟩)
    · exact Or.inl ⟨m,hprior,hroot⟩
    · exact Or.inr ⟨j,m,hprior,hroot⟩

#print axioms target_arithmetic
#print axioms direct_parent_arithmetic
#print axioms payload_unreachable
#print axioms low_stop_m67_z846_mod2048_unreachable
#print axioms blank_halts_iff_six_low1585

end BB6.Agent29Z78Q6
