import BB429Forced13

namespace BB429Forced13More
open BB429NewResidue BB429Forced13

set_option maxHeartbeats 30000000
set_option maxRecDepth 30000

/-- A non-special odd output with no S congruence has a uniquely forced,
    authentic blank-root predecessor. -/
theorem forced_F (a b x : Nat)
    (ha : 13 ≤ a) (ho : a%2=1) (hnot : b%4≠2)
    (heq : a=2*x+3) (hr : Reach a b) :
    Reach x (b+a) := by
  rcases odd_back a b ha ho hr with
    ⟨z,w,hp,hz,hw⟩ | ⟨z,w,hp,hz,hw,hb⟩
  · have hez : z=x := by omega
    have hew : w=b+a := by omega
    rw [hez,hew] at hp
    exact hp
  · omega

/-- A non-special even output has its exact unique E-predecessor. -/
theorem forced_E (a b x y : Nat)
    (ha : 6 ≤ a) (he : a%2=0)
    (hx : 4*x+14=4*a+b) (hy : 2*y=b)
    (hr : Reach a b) : Reach x y := by
  obtain ⟨z,w,hp,hz,hw,hmod⟩ := even_back a b ha he hr
  have hzx : z=x := by omega
  have hwy : w=y := by omega
  rw [hzx,hwy] at hp
  exact hp

/-- The first five actual root inverse steps are F F F S F. -/
theorem forced_FFFSF (q : Nat) (hq : 4 ≤ q)
    (hr : Reach (32*q+13) (64*q+23)) :
    Reach (17*q) (94*q+26) := by
  have h4 := BB429Forced13.forced_FFFS q hq hr
  have h5 := forced_F (34*q+3) (60*q+23) (17*q)
    (by omega) (by omega) (by omega) (by omega) h4
  have hh : (60*q+23)+(34*q+3)=94*q+26 := by omega
  rw [hh] at h5
  exact h5

/-- All positive multiples of eight in the 13-line are excluded from
    authentic BB429 blank-start reachability in exactly seven inverse steps. -/
theorem no_q0_mod8 (t : Nat) (ht : 1 ≤ t) :
    ¬ Reach (256*t+13) (512*t+23) := by
  intro hr
  have h0 : Reach (32*(8*t)+13) (64*(8*t)+23) := by
    have ha : 32*(8*t)+13=256*t+13 := by omega
    have hb : 64*(8*t)+23=512*t+23 := by omega
    rw [ha,hb]
    exact hr
  have hf := forced_FFFSF (8*t) (by omega) h0
  have hx : 17*(8*t)=136*t := by omega
  have hy : 94*(8*t)+26=752*t+26 := by omega
  rw [hx,hy] at hf
  have he : Reach (324*t+3) (376*t+13) :=
    forced_E (136*t) (752*t+26) (324*t+3) (376*t+13)
      (by omega) (by omega) (by omega) (by omega) hf
  have h7 : Reach (162*t) ((376*t+13)+(324*t+3)) :=
    forced_F (324*t+3) (376*t+13) (162*t)
      (by omega) (by omega) (by omega) (by omega) he
  have hy7 : (376*t+13)+(324*t+3)=700*t+16 := by omega
  rw [hy7] at h7
  obtain ⟨n,hn⟩ := h7
  have hb8 := BB429RootEven8.rooted_positive_even_eight
    n (162*t) (700*t+16) hn (by omega) (by omega)
  omega

/-- The q≡1(mod8) 13-line cylinder is likewise authentically impossible. -/
theorem no_q1_mod8 (t : Nat) (ht : 1 ≤ t) :
    ¬ Reach (256*t+45) (512*t+87) := by
  intro hr
  have h0 : Reach (32*(8*t+1)+13) (64*(8*t+1)+23) := by
    have ha : 32*(8*t+1)+13=256*t+45 := by omega
    have hb : 64*(8*t+1)+23=512*t+87 := by omega
    rw [ha,hb]
    exact hr
  have hf := forced_FFFSF (8*t+1) (by omega) h0
  have hx : 17*(8*t+1)=136*t+17 := by omega
  have hy : 94*(8*t+1)+26=752*t+120 := by omega
  rw [hx,hy] at hf
  have h6 : Reach (68*t+7) ((752*t+120)+(136*t+17)) :=
    forced_F (136*t+17) (752*t+120) (68*t+7)
      (by omega) (by omega) (by omega) (by omega) hf
  have hy6 : (752*t+120)+(136*t+17)=888*t+137 := by omega
  rw [hy6] at h6
  have h7 : Reach (34*t+2) ((888*t+137)+(68*t+7)) :=
    forced_F (68*t+7) (888*t+137) (34*t+2)
      (by omega) (by omega) (by omega) (by omega) h6
  have hy7 : (888*t+137)+(68*t+7)=956*t+144 := by omega
  rw [hy7] at h7
  obtain ⟨n,hn⟩ := h7
  have hb8 := BB429RootEven8.rooted_positive_even_eight
    n (34*t+2) (956*t+144) hn (by omega) (by omega)
  omega

/-- Exact eighth-step exclusion of the whole q=5(mod16) 13-line cylinder:
    both possible odd inverse edges terminate in a positive-even source
    state violating the already-certified b≡2(mod8) gate. -/
theorem no_q5_mod16 (t : Nat) :
    ¬ Reach (512*t+173) (1024*t+343) := by
  intro hr
  have h0 : Reach (32*(16*t+5)+13) (64*(16*t+5)+23) := by
    have ha : 32*(16*t+5)+13=512*t+173 := by omega
    have hb : 64*(16*t+5)+23=1024*t+343 := by omega
    rw [ha,hb]
    exact hr
  have hf := forced_FFFSF (16*t+5) (by omega) h0
  have hx : 17*(16*t+5)=272*t+85 := by omega
  have hy : 94*(16*t+5)+26=1504*t+496 := by omega
  rw [hx,hy] at hf
  have h6 : Reach (136*t+41) ((1504*t+496)+(272*t+85)) :=
    forced_F (272*t+85) (1504*t+496) (136*t+41)
      (by omega) (by omega) (by omega) (by omega) hf
  have hy6 : (1504*t+496)+(272*t+85)=1776*t+581 := by omega
  rw [hy6] at h6
  have h7 : Reach (68*t+19) ((1776*t+581)+(136*t+41)) :=
    forced_F (136*t+41) (1776*t+581) (68*t+19)
      (by omega) (by omega) (by omega) (by omega) h6
  have hy7 : (1776*t+581)+(136*t+41)=1912*t+622 := by omega
  rw [hy7] at h7
  rcases odd_back (68*t+19) (1912*t+622)
      (by omega) (by omega) h7 with
    ⟨x,y,hp,hxe,hye⟩ | ⟨x,y,hp,hxe,hye,hmod⟩
  · obtain ⟨n,hn⟩ := hp
    have heven : y%8=2 :=
      BB429RootEven8.rooted_positive_even_eight n x y hn
        (by omega) (by omega)
    omega
  · obtain ⟨n,hn⟩ := hp
    have heven : y%8=2 :=
      BB429RootEven8.rooted_positive_even_eight n x y hn
        (by omega) (by omega)
    omega

/-- Exact all-time three-of-sixteen necessary source residue classification
    for the 13-line and all q>=16; NONE of these surviving classes is
    asserted actually blank-reachable. -/
theorem rooted_13_q_mod16 (q : Nat) (hq : 16 ≤ q)
    (hr : Reach (32*q+13) (64*q+23)) :
    q%16=4 ∨ q%16=12 ∨ q%16=13 := by
  have h4 := BB429Forced13.rooted_13_q_mod4 q (by omega) hr
  have hn0 : q%8≠0 := by
    intro h
    let t := q/8
    have ht : 1≤t := by dsimp [t]; omega
    have ha : 32*q+13=256*t+13 := by dsimp [t]; omega
    have hb : 64*q+23=512*t+23 := by dsimp [t]; omega
    rw [ha,hb] at hr
    exact no_q0_mod8 t ht hr
  have hn1 : q%8≠1 := by
    intro h
    let t := q/8
    have ht : 1≤t := by dsimp [t]; omega
    have ha : 32*q+13=256*t+45 := by dsimp [t]; omega
    have hb : 64*q+23=512*t+87 := by dsimp [t]; omega
    rw [ha,hb] at hr
    exact no_q1_mod8 t ht hr
  have hn5 : q%16≠5 := by
    intro h
    let t := q/16
    have ha : 32*q+13=512*t+173 := by dsimp [t]; omega
    have hb : 64*q+23=1024*t+343 := by dsimp [t]; omega
    rw [ha,hb] at hr
    exact no_q5_mod16 t hr
  omega

#print axioms forced_F
#print axioms forced_E
#print axioms forced_FFFSF
#print axioms no_q0_mod8
#print axioms no_q1_mod8
#print axioms no_q5_mod16
#print axioms rooted_13_q_mod16
end BB429Forced13More
