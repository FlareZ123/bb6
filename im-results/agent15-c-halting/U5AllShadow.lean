import RationalShadow211
import U5Y3M8
import Lean.Elab.Tactic.Omega
set_option maxHeartbeats 1000000
namespace BB6.Agent15U5AllShadow
open BB6.Agent3 BB6.Agent46 BB6.Agent11M0SumZeroVerified
open BB6.Agent15RationalShadow211

def offset (M : Nat) : Nat := 10669+22155*M
def exponent (M : Nat) : Nat := 201+420*M
def depth (q : Nat) : Nat := 2*q-2
def q0Shadow (M : Nat) : Shadow := ⟨8*offset M+633,4*offset M+211⟩
def qShadow (M q : Nat) : Shadow :=
  let d := depth q
  let B := offset M/2^d
  ⟨2*B+633,(8*2^d-1)*B+211*(3*q+1)⟩
def allCheck (f M : Nat) : Bool :=
  check f (exponent M) (q0Shadow M) &&
  (List.range ((offset M).log2/2+1)).all (fun i =>
    let q := i+1
    let d := depth q
    if offset M%2^d=0 then check f (exponent M-d) (qShadow M q) else true)

theorem q0_congruent (M p a k : Nat)
    (h : 211*p+offset M=160*2^(exponent M))
    (ha : a=8*p-3) (hk : k=4*p-1) (hp : 1≤p) :
    congruent (exponent M) a k (q0Shadow M) := by
  constructor
  · refine ⟨1280,?_⟩
    unfold q0Shadow; dsimp; omega
  · refine ⟨640,?_⟩
    unfold q0Shadow; dsimp; omega

theorem q_congruent (M p q U a k : Nat)
    (h : 211*p+offset M=160*2^(exponent M))
    (hq : 1≤q) (hb : 2^(depth q)≤p)
    (hdecomp : p=2^(depth q)*U)
    (ha : a+3=2*U) (hk : k+3*q+1=U*(2^(2*q+1)-1)) :
    depth q≤exponent M ∧ offset M%2^(depth q)=0 ∧ q-1<(offset M).log2/2+1 ∧
    congruent (exponent M-depth q) a k (qShadow M q) := by
  let d := depth q
  let E := exponent M
  let C := offset M
  have hC : 0<C := by dsimp [C,offset]; omega
  have hpow : 2^d≤2^E := by dsimp [d,E] at *; omega
  have hdE : d≤E := (Nat.pow_le_pow_iff_right (by decide : 1<(2:Nat))).mp hpow
  have hdivPow : 2^d∣2^E := Nat.pow_dvd_pow 2 hdE
  have hdp : 2^d∣p := ⟨U,hdecomp⟩
  have hleft : 2^d∣211*p := Nat.dvd_trans hdp (Nat.dvd_mul_left p 211)
  have hright : 2^d∣160*2^E := Nat.dvd_trans hdivPow (Nat.dvd_mul_left (2^E) 160)
  have hsum : 2^d∣211*p+C := by rw [show 211*p+C=160*2^E from h]; exact hright
  have hdC : 2^d∣C := by
    have hh := Nat.dvd_sub hsum hleft
    rwa [show 211*p+C-211*p=C by omega] at hh
  have hCmod := Nat.mod_eq_zero_of_dvd hdC
  have hlog : d≤C.log2 := (Nat.le_log2 (Nat.ne_of_gt hC)).mpr (Nat.le_of_dvd hC hdC)
  let B := C/2^d
  have hB : 2^d*B=C := by rw [Nat.mul_comm]; exact Nat.div_mul_cancel hdC
  have hE : 2^d*2^(E-d)=2^E := by rw [Nat.mul_comm]; exact Nat.pow_sub_mul_pow 2 hdE
  have hscaled : 211*U+B=160*2^(E-d) := by
    apply Nat.mul_left_cancel (Nat.pow_pos (by decide : 0<(2:Nat)))
    calc
      2^d*(211*U+B) = 211*p+C := by rw [Nat.mul_add,Nat.mul_left_comm _ 211,hdecomp,hB]
      _ = 160*2^E := h
      _ = 2^d*(160*2^(E-d)) := by rw [Nat.mul_left_comm _ 160,hE]
  have h8 : 2^(2*q+1)=8*2^d := by
    rw [show 2*q+1=3+d by dsimp [d,depth]; omega,Nat.pow_add]
  rw [h8] at hk
  have hprod := congrArg (fun z : Nat => (8*2^d-1)*z) hscaled
  simp only [Nat.mul_add,Nat.mul_left_comm (8*2^d-1) 211,Nat.mul_left_comm (8*2^d-1) 160] at hprod
  have hprod' : 211*(U*(8*2^d-1))+(8*2^d-1)*B=2^(E-d)*(160*(8*2^d-1)) := by
    calc
      _ = 211*((8*2^d-1)*U)+(8*2^d-1)*B := by rw [Nat.mul_comm U (8*2^d-1)]
      _ = 160*((8*2^d-1)*2^(E-d)) := hprod
      _ = _ := by ac_rfl
  refine ⟨hdE,hCmod,?_,?_⟩
  · change q-1<C.log2/2+1
    dsimp [d,depth] at hlog; omega
  · change congruent (E-d) a k ⟨2*B+633,(8*2^d-1)*B+211*(3*q+1)⟩
    constructor
    · refine ⟨320,?_⟩
      change 211*a+(2*B+633)=2^(E-d)*320
      omega
    · refine ⟨160*(8*2^d-1),?_⟩
      change 211*k+((8*2^d-1)*B+211*(3*q+1))=2^(E-d)*(160*(8*2^d-1))
      simp only [Nat.mul_add] at hprod' ⊢
      omega

theorem all_terminal_of_shadow (f M s m : Nat) (hs : 211*s+129=5*2^(201+420*M))
    (hm : 32*s=32+105*M+m) (hc : allCheck f M=true) :
    ¬ CReach (302+512*s-4*(201+420*M)) 3 := by
  have exclude (f b x y : Nat) (s : Shadow) (h : check f b s=true) (hc : congruent b x y s) : ¬ CReach x y := by
    apply check_sound CReach ?_ BB6.Agent13TwoParent.odd_forbidden_image f b x y s h hc
    intro u v hx hy hr
    obtain ⟨a,k,hp,hedge⟩ := cReach_parent_of_left_gt5 u v hx hr
    exact ⟨a,k,hp,(complete_section_inverse a k u v (by omega)).mp hedge⟩
  have hid : 211*(m+1)+offset M=160*2^(exponent M) := by unfold offset exponent; omega
  simp only [allCheck,Bool.and_eq_true] at hc
  intro hr
  obtain ⟨a,k,hP,hstep⟩ := cReach_parent_of_left_gt5 _ 3 (by omega) hr
  rcases BB6.Agent3U5DepthFan.u5_residual_y3_parent_fan M s m a k hs hm hstep with h0 | ⟨q,U,hq,hbound,hdecomp,ha,hk⟩
  · exact exclude f _ a k _ hc.1 (q0_congruent M (m+1) a k hid h0.1 h0.2 (by omega)) hP
  · obtain ⟨hd,hmod,hidx,hcong⟩ := q_congruent M (m+1) q U a k hid hq hbound hdecomp ha hk
    have htest := (List.all_eq_true.mp hc.2) (q-1) (List.mem_range.mpr hidx)
    rw [show q-1+1=q by omega] at htest
    simp only [hmod,ite_true] at htest
    exact exclude f _ a k _ htest hcong hP

theorem all_high_stop_of_shadow (f M s m : Nat) (hs : 211*s+129=5*2^(201+420*M))
    (hm : 32*s=32+105*M+m) (hc : allCheck f M=true) :
    ¬ CReach (2*(39+64*s)+3) (3*(39+64*s)+7) := by
  have hp : 8 ∣ (2:Nat)^(201+420*M) := by
    change 2^3 ∣ 2^(201+420*M)
    exact Nat.pow_dvd_pow 2 (by omega)
  have hp8 := Nat.mod_eq_zero_of_dvd hp
  have hs8 : s%8=5 := by
    have h8 : (211*s+129)%8=0 := by rw [hs,Nat.mul_mod,hp8]
    omega
  have hB : ¬ CReach (54+90*s) (127+211*s) := by
    intro h
    exact all_terminal_of_shadow f M s m hs hm hc ((BB6.Agent3U5M8.u5_residual_six_even_right_chain M s hs).mp h)
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

#print axioms q_congruent
#print axioms all_terminal_of_shadow
#print axioms all_high_stop_of_shadow
end BB6.Agent15U5AllShadow
