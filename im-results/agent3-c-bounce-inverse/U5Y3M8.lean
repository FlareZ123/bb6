import U5Y3ParentFan
import U5M8Q0Partial
import EvenRightSixOrbit
import OddOddVal3Orbit
import EvenOddFourExact
import HighSumTwo
import Lean.Elab.Tactic.Omega

namespace BB6.Agent3U5M8
open BB6.Agent3 BB6.Agent46 BB6.Agent3U5DepthFan BB6.Agent11High
set_option maxHeartbeats 1000000

/-- The exact normalization orbit, with conserved weighted mass. -/
def u5Orbit (s : Nat) : Nat → Nat × Nat
  | 0 => (54+90*s,127+211*s)
  | n+1 => let p := u5Orbit s n; (p.1+p.2-2,(p.2-2)/2)

private theorem orbit_snd (r s n : Nat)
    (hs : 211*s+129=5*2^r) (hn : n≤r) :
    (u5Orbit s n).2=5*2^(r-n)-2 := by
  induction n with
  | zero => simp [u5Orbit]; omega
  | succ n ih =>
    have he : r-n=(r-(n+1))+1 := by omega
    have hp : 2^(r-n)=2^(r-(n+1))*2 := by rw [he,Nat.pow_succ]
    change ((u5Orbit s n).2-2)/2=5*2^(r-(n+1))-2
    rw [ih (by omega),hp]
    omega

private theorem orbit_mass (r s n : Nat)
    (hs : 211*s+129=5*2^r) (hn : n≤r) :
    (u5Orbit s n).1+2*(u5Orbit s n).2+4*n=308+512*s := by
  induction n with
  | zero => simp [u5Orbit]; omega
  | succ n ih =>
    have hprev := ih (by omega)
    have hy := orbit_snd r s n hs (by omega)
    have hd : 2∣2^(r-n) := by
      change 2^1∣2^(r-n)
      exact Nat.pow_dvd_pow 2 (by omega)
    have hm := Nat.mod_eq_zero_of_dvd hd
    have hp : 0<2^(r-n) := Nat.pow_pos (by decide)
    change 2^(r-n)%2=0 at hm
    have hy2 : 2≤(u5Orbit s n).2 := by omega
    have hyEven : (u5Orbit s n).2%2=0 := by omega
    simp only [u5Orbit]
    omega

private theorem orbit_gate (r s n : Nat)
    (hs : 211*s+129=5*2^r) (hr : r%2=1) (hn : n<r) :
    6≤(u5Orbit s n).2 ∧ (u5Orbit s n).2%2=0 ∧
    ((u5Orbit s n).1+(u5Orbit s n).2)%8≠0 ∧
    ((u5Orbit s n).1+(u5Orbit s n).2)%8≠7 := by
  have hy := orbit_snd r s n hs (by omega)
  have hmass := orbit_mass r s n hs (by omega)
  have hd : 2∣2^(r-n) := by
    change 2^1∣2^(r-n)
    exact Nat.pow_dvd_pow 2 (by omega)
  have hm := Nat.mod_eq_zero_of_dvd hd
  change 2^(r-n)%2=0 at hm
  have hp : 0<2^(r-n) := Nat.pow_pos (by decide)
  have hy6 : 6≤(u5Orbit s n).2 := by omega
  have hyEven : (u5Orbit s n).2%2=0 := by omega
  refine ⟨hy6,hyEven,?_,?_⟩
  · by_cases h : 3≤r-n
    · have hd8 : 8∣2^(r-n) := by
        change 2^3∣2^(r-n)
        exact Nat.pow_dvd_pow 2 h
      have hm8 := Nat.mod_eq_zero_of_dvd hd8
      change 2^(r-n)%8=0 at hm8
      omega
    · by_cases h2 : r-n=2
      · rw [h2] at hy
        have hy18 : (u5Orbit s n).2=18 := by omega
        omega
      · have h1 : r-n=1 := by omega
        rw [h1] at hy
        have hy8 : (u5Orbit s n).2=8 := by omega
        omega
  · omega

/-- Exact original-source equivalence along the entire U5 chain. -/
theorem u5_residual_six_even_right_chain (M s : Nat)
    (hs : 211*s+129=5*2^(201+420*M)) :
    CReach (54+90*s) (127+211*s) ↔ CReach (302+512*s-4*(201+420*M)) 3 := by
  let r := 201+420*M
  have hs' : 211*s+129=5*2^r := hs
  have hr : r%2=1 := by dsimp [r]; omega
  have hchain : ∀ n, n≤r → (CReach (u5Orbit s 0).1 (u5Orbit s 0).2 ↔
      CReach (u5Orbit s n).1 (u5Orbit s n).2) := by
    intro n
    induction n with
    | zero => intro hn; exact Iff.rfl
    | succ n ih =>
      intro hn
      obtain ⟨hy,he,h0,h7⟩ := orbit_gate r s n hs' hr (by omega)
      have hstep := six_even_right_blank_reach_iff (u5Orbit s n).1 (u5Orbit s n).2 hy he h0 h7
      exact (ih (by omega)).trans (by simpa only [u5Orbit] using hstep)
  have hlast := hchain r (by omega)
  have hyLast : (u5Orbit s r).2=3 := by
    rw [orbit_snd r s r hs' (by omega),Nat.sub_self]
  have hmass := orbit_mass r s r hs' (by omega)
  have hxLast : (u5Orbit s r).1=302+512*s-4*r := by omega
  simpa only [u5Orbit,hxLast,hyLast,r] using hlast

/-- For p=m+1 in the residue class p=1 (mod 8), the q=1 member of the
u=5 y=3 predecessor fan is already in the forbidden odd-right sum-two
image. -/
private theorem u5_q1_parent_unreachable (p : Nat)
    (hp8 : p%8=1) (hpge : 3≤p) :
    ¬ CReach (2*p-3) (7*p-4) := by
  apply blank_no_odd_sum_two
  · omega
  · omega
  · omega

/-- Infinite new u=5 residual cylinder: for M=8*w with w even or
w=3 mod 8, every possible original-source predecessor of the terminal
y=3 state is excluded. The other odd residue classes of w remain open. -/
theorem blank_no_u5_residual_m8w_partial (w s m : Nat)
    (hs : 211*s+129=5*2^(201+3360*w))
    (hm : 32*s=32+840*w+m)
    (hw : w%2=0 ∨ w%8=3) :
    ¬ CReach (302+512*s-4*(201+3360*w)) 3 := by
  have hs' : 211*s+129=5*2^(201+420*(8*w)) := by
    simpa only [show 201+420*(8*w)=201+3360*w by omega] using hs
  have hm' : 32*s=32+105*(8*w)+m := by omega
  have hp8 : (m+1)%8=1 := by omega
  have hpge : 3≤m+1 := by
    have hid := u5_residual_m_identity (8*w) s m hs' hm'
    have hm7 := u5_residual_m_mod7 (8*w) m hid
    omega
  intro hr
  obtain ⟨a,k,hP,hstep⟩ := BB6.Agent11M0SumZeroVerified.cReach_parent_of_left_gt5 _ 3 (by omega) hr
  have hedge : secNext (a,k)=some (302+512*s-4*(201+420*(8*w)),3) := by
    simpa only [show 201+420*(8*w)=201+3360*w by omega] using hstep
  rcases u5_residual_y3_parent_fan (8*w) s m a k hs' hm' hedge with h0 | ⟨q,U,hq,hbound,hdecomp,ha,hk⟩
  · rw [h0.1,h0.2] at hP
    let t := m/8
    have hp : m+1=8*t+1 := by dsimp [t]; omega
    have ht : 1≤t := by omega
    rcases hw with hwEven|hw3
    · exact BB6.Agent11U5M8Q0Partial.blank_no_u5_q0_parent_w_even
        w s m t hs hm hp hwEven ht hP
    · exact BB6.Agent11U5M8Q0Partial.blank_no_u5_q0_parent_w3
        w s m t hs hm hp hw3 ht hP
  · by_cases hq1 : q=1
    · subst q
      simp at hdecomp hk
      have ha1 : a=2*(m+1)-3 := by omega
      have hk1 : k=7*(m+1)-4 := by omega
      rw [ha1,hk1] at hP
      exact u5_q1_parent_unreachable (m+1) hp8 hpge hP
    · have hd : 4∣2^(2*q-2) := by
        change 2^2∣2^(2*q-2)
        exact Nat.pow_dvd_pow 2 (by omega)
      have hd' : 4∣m+1 := hdecomp ▸ Nat.dvd_mul_right_of_dvd hd U
      omega

/-- The u=5 residual B_s cylinder is blank-unreachable for M=8*w
when w is even or w=3 mod 8. -/
theorem blank_no_u5_B_s_m8w_partial (w s m : Nat)
    (hs : 211*s+129=5*2^(201+3360*w))
    (hm : 32*s=32+840*w+m)
    (hw : w%2=0 ∨ w%8=3) :
    ¬ CReach (54+90*s) (127+211*s) := by
  have hs' : 211*s+129=5*2^(201+420*(8*w)) := by
    simpa only [show 201+420*(8*w)=201+3360*w by omega] using hs
  have hm' : 32*s=32+105*(8*w)+m := by omega
  intro h
  have hterminal :=
    (u5_residual_six_even_right_chain (8*w) s hs').mp h
  have hX : 302+512*s-4*(201+3360*w)=16*m+10 := by omega
  have hterminal' : CReach (302+512*s-4*(201+3360*w)) 3 := by
    simpa only [show 201+420*(8*w)=201+3360*w by omega] using hterminal
  exact blank_no_u5_residual_m8w_partial w s m hs hm hw hterminal'

#print axioms u5_residual_six_even_right_chain
#print axioms blank_no_u5_residual_m8w_partial
#print axioms blank_no_u5_B_s_m8w_partial

end BB6.Agent3U5M8
