import AffineConeLowStop
import U5Y3M8
import U5Q0M16Residual
import M0EvenEvenSumZero
import Lean.Elab.Tactic.Omega

set_option maxHeartbeats 400000
namespace BB6.Agent15U5Affine
open BB6.Agent3 BB6.Agent46 BB6.Agent13AffineCone
open BB6.Agent11M0SumZeroVerified

theorem residual_index (w t : Nat)
    (h : 211*t+1360+22155*w=20*2^(201+3360*w)) :
    ∃ n, t=60+105*n ∧ (n+w)%65536=16180 := by
  have hp6 : (2:Nat)^6%21=1 := by decide
  have hp21 : (2:Nat)^(201+3360*w)%21=8 := by
    rw [show 201+3360*w=6*(33+560*w)+3 by omega,
      Nat.pow_add,Nat.mul_mod,Nat.pow_mul,Nat.pow_mod,hp6]
    simp
  have h21 : (211*t+1360+22155*w)%21=13 := by
    rw [h,Nat.mul_mod,hp21]
  have h5 : (211*t+1360+22155*w)%5=0 := by
    rw [h,Nat.mul_mod]
    simp
  have ht105 : t%105=60 := by omega
  let n := t/105
  have ht : t=60+105*n := by dsimp [n]; omega
  have hd : 65536 ∣ (2:Nat)^(201+3360*w) := by
    change 2^16 ∣ 2^(201+3360*w)
    exact Nat.pow_dvd_pow 2 (by omega)
  have hpow : (2:Nat)^(201+3360*w)%65536=0 := Nat.mod_eq_zero_of_dvd hd
  have hmod : (211*t+1360+22155*w)%65536=0 := by
    rw [h,Nat.mul_mod,hpow]
  have hlin : (14020+22155*(n+w))%65536=0 := by
    rw [ht] at hmod
    have hh : 211*(60+105*n)+1360+22155*w=14020+22155*(n+w) := by omega
    rw [hh] at hmod
    exact hmod
  have hmul : (22155*(n+w))%65536=51516 := by
    have haux (z : Nat) (hz : (14020+z)%65536=0) : z%65536=51516 := by
      rw [Nat.add_mod] at hz
      have hlt := Nat.mod_lt z (by decide : 0<65536)
      omega
    exact haux _ hlin
  have hprod : (57635*(22155*(n+w)))%65536=16180 := by
    rw [Nat.mul_mod,hmul]
  have hfac : 57635*(22155*(n+w))=1276903425*(n+w) := by
    rw [←Nat.mul_assoc]
  rw [hfac,Nat.mul_mod] at hprod
  have hr : (n+w)%65536=16180 := by simpa using hprod
  exact ⟨n,ht,hr⟩

def index (w : Nat) : Nat := (16180+65536-w%65536)%65536

theorem index_eq (n w : Nat) (h : (n+w)%65536=16180) :
    n%65536=index w := by
  unfold index
  omega

def xRay (b : Nat) : Ray :=
  let t := 60+105*b
  ⟨⟨44*105*65536,44*t-1⟩,⟨42*105*65536,42*t-1⟩⟩

def wFilter (w : Nat) : Bool := excluded 24 (xRay (index w))

theorem wFilter_periodic (w : Nat) : wFilter w = wFilter (w%65536) := by
  simp [wFilter,index]

theorem x_excluded (w t : Nat)
    (h : 211*t+1360+22155*w=20*2^(201+3360*w))
    (hc : wFilter w=true) : ¬ CReach (44*t-1) (42*t-1) := by
  obtain ⟨n,ht,hn⟩ := residual_index w t h
  have hi := index_eq n w hn
  have hd := Nat.mod_add_div n 65536
  rw [hi] at hd
  have hx : (xRay (index w)).x.eval (n/65536)=44*t-1 := by
    simp only [xRay,Linear.eval]
    omega
  have hy : (xRay (index w)).y.eval (n/65536)=42*t-1 := by
    simp only [xRay,Linear.eval]
    omega
  have he := source_excluded 24 (xRay (index w)) hc (n/65536)
  rwa [hx,hy] at he

private theorem q0_parent_reach_implies_X (t : Nat) (ht : 1≤t)
    (h : CReach (64*t+5) (32*t+3)) : CReach (44*t-1) (42*t-1) := by
  have h1 := (oddodd_val3_blank_reach_iff
    (64*t+5) (32*t+3)
    (by omega) (by omega) (by omega) (by omega) (by omega)).mp h
  have h1' : CReach (48*t+2) (40*t+1) := by
    have hx : ((64*t+5)+(32*t+3)-4)/2=48*t+2 := by omega
    have hy : ((64*t+5)+3*(32*t+3)-10)/4=40*t+1 := by omega
    simpa only [hx,hy] using h1
  have h2 := (evenodd_four_blank_reach_iff
    (48*t+2) (40*t+1)
    (by omega) (by omega) (by omega) (by omega)).mp h1'
  have hx : ((48*t+2)+(40*t+1)-5)/2=44*t-1 := by omega
  have hy : ((48*t+2)+3*(40*t+1)-9)/4=42*t-1 := by omega
  simpa only [hx,hy] using h2

theorem terminal_excluded (w s m : Nat)
    (hs : 211*s+129=5*2^(201+3360*w))
    (hm : 32*s=32+840*w+m) (hc : wFilter w=true) :
    ¬ CReach (302+512*s-4*(201+3360*w)) 3 := by
  let t := m/8
  have hp : m+1=8*t+1 := by dsimp [t]; omega
  have hid := BB6.Agent3U5M16Residual.u5_m8_t_identity w s m t hs hm hp
  obtain ⟨n,ht,_⟩ := residual_index w t hid
  have htge : 60≤t := by omega
  have hX := x_excluded w t hid hc
  have hs' : 211*s+129=5*2^(201+420*(8*w)) := by
    simpa only [show 201+420*(8*w)=201+3360*w by omega] using hs
  have hm' : 32*s=32+105*(8*w)+m := by omega
  intro hr
  obtain ⟨a,k,hP,hstep⟩ := cReach_parent_of_left_gt5 _ 3 (by omega) hr
  have hedge : secNext (a,k)=some (302+512*s-4*(201+420*(8*w)),3) := by
    simpa only [show 201+420*(8*w)=201+3360*w by omega] using hstep
  rcases BB6.Agent3U5DepthFan.u5_residual_y3_parent_fan (8*w) s m a k hs' hm' hedge with h0 | ⟨q,U,hq,hbound,hdecomp,ha,hk⟩
  · have ha0 : a=64*t+5 := by omega
    have hk0 : k=32*t+3 := by omega
    rw [ha0,hk0] at hP
    exact hX (q0_parent_reach_implies_X t (by omega) hP)
  · by_cases hq1 : q=1
    · subst q
      simp at hdecomp hk
      have ha1 : a=2*(m+1)-3 := by omega
      have hk1 : k=7*(m+1)-4 := by omega
      rw [ha1,hk1] at hP
      exact BB6.Agent11High.blank_no_odd_sum_two _ _ (by omega) (by omega) (by omega) hP
    · have hd : 4 ∣ 2^(2*q-2) := by
        change 2^2 ∣ 2^(2*q-2)
        exact Nat.pow_dvd_pow 2 (by omega)
      have hd' : 4 ∣ m+1 := hdecomp ▸ Nat.dvd_mul_right_of_dvd hd U
      omega

theorem high_stop_excluded (w s m : Nat)
    (hs : 211*s+129=5*2^(201+3360*w))
    (hm : 32*s=32+840*w+m) (hc : wFilter w=true) :
    ¬ CReach (2*(39+64*s)+3) (3*(39+64*s)+7) := by
  have hp : 8 ∣ (2:Nat)^(201+3360*w) := by
    change 2^3 ∣ 2^(201+3360*w)
    exact Nat.pow_dvd_pow 2 (by omega)
  have hp8 := Nat.mod_eq_zero_of_dvd hp
  have hs8 : s%8=5 := by
    have h8 : (211*s+129)%8=0 := by rw [hs,Nat.mul_mod,hp8]
    omega
  have hB : ¬ CReach (54+90*s) (127+211*s) := by
    intro h
    have hs' : 211*s+129=5*2^(201+420*(8*w)) := by
      simpa only [show 201+420*(8*w)=201+3360*w by omega] using hs
    have ht := (BB6.Agent3U5M8.u5_residual_six_even_right_chain (8*w) s hs').mp h
    apply terminal_excluded w s m hs hm hc
    simpa only [show 201+420*(8*w)=201+3360*w by omega] using ht
  intro h
  have h' : CReach (17+64*(2*s+1)) (28+96*(2*s+1)) := by
    have hx : 17+64*(2*s+1)=2*(39+64*s)+3 := by omega
    have hy : 28+96*(2*s+1)=3*(39+64*s)+7 := by omega
    simpa only [hx,hy] using h
  have hA : CReach (130+208*s) (94+152*s) := by
    have hx : 26+104*(2*s+1)=130+208*s := by omega
    have hy : 18+76*(2*s+1)=94+152*s := by omega
    simpa only [hx,hy] using mzero_first_two_reach (2*s+1) h'
  obtain ⟨a,k,hP,hedge⟩ := cReach_parent_of_left_gt5 _ _ (by omega) hA
  rcases m0_odd_ray_parent s a k (by omega) hedge with hL | hR
  · rw [hL.1,hL.2] at hP
    exact blank_no_L_s_mod8_five s hs8 hP
  · rw [hR.1,hR.2] at hP
    exact hB hP

#eval (List.range 65536).foldl (fun n w => if wFilter w then n+1 else n) (0 : Nat)
#eval (List.range 8).map (fun r => (List.range 8192).foldl
  (fun n j => if wFilter (8*j+r) then n+1 else n) (0 : Nat))
#print axioms residual_index
#print axioms wFilter_periodic
#print axioms high_stop_excluded
end BB6.Agent15U5Affine
