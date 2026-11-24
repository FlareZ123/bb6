
import Lean
import Lean.Elab.Tactic.Omega

namespace NeedleFourStep

structure Data where
  v : Nat
  q : Nat

def Data.a (x : Data) := 2^x.v
def Data.r (x : Data) := 2*x.q+3
def Data.b (x : Data) := x.a*x.r
def Data.g (x : Data) := x.v+3*(x.q+1)
def Data.s (x : Data) (m : Nat) := 2^(x.v-m)
def Data.F (x : Data) (m : Nat) := (2*x.v-3)*x.s m
def Adj (x y : Data) := x.b+x.g=y.b

theorem gain_pos (x : Data) : 0<x.g := by
  simp only [Data.g]; omega

theorem oddpart_le_gain (x : Data) : x.r≤x.g := by
  simp only [Data.r, Data.g]; omega

theorem b_pos (x : Data) : 0<x.b := by
  unfold Data.b Data.a Data.r
  exact Nat.mul_pos (Nat.two_pow_pos _) (by omega)

theorem a_le_b (x : Data) : x.a≤x.b := by
  unfold Data.b
  have hr : 1≤x.r := by unfold Data.r; omega
  simpa using Nat.mul_le_mul_left x.a hr

theorem a_eq (x : Data) (m : Nat) (hm : m≤x.v) :
    x.a=2^m*x.s m := by
  unfold Data.a Data.s
  rw [←Nat.pow_add, show m+(x.v-m)=x.v by omega]

theorem a_dvd (x : Data) (m : Nat) (hm : m≤x.v) :
    2^m ∣ x.b := by
  unfold Data.b
  exact Nat.dvd_trans (Nat.pow_dvd_pow 2 hm) (Nat.dvd_mul_right _ _)

theorem gain_dvd (x y : Data) (m : Nat) (hx : m≤x.v) (hy : m≤y.v)
    (h : Adj x y) : 2^m ∣ x.g := by
  have h0 := a_dvd x m hx
  have h1 := a_dvd y m hy
  unfold Adj at h
  rw [←h] at h1
  exact (Nat.dvd_add_iff_right h0).mpr h1

theorem F_mono (x y : Data) (m : Nat)
    (h : x.v≤y.v) : x.F m≤y.F m := by
  unfold Data.F Data.s
  exact Nat.mul_le_mul (by omega) (Nat.pow_le_pow_right (by omega) (by omega))

theorem v_bound (x : Data) (L : Nat) (h : x.b<2^(L+1)) : x.v≤L := by
  have ha := a_le_b x
  by_cases hh : x.v≤L
  · exact hh
  · have hp := Nat.pow_le_pow_right (n:=2) (by omega : 0<2) (by omega : L+1≤x.v)
    unfold Data.a at ha
    omega

theorem g_identity (x : Data) (hv : 2≤x.v) : 2*x.g = (2*x.v-3)+3*x.r := by
  unfold Data.g Data.r
  omega

theorem small_F (x : Data) (m L b : Nat) (hm : m≤x.v)
    (hv : 2≤x.v) (hL : x.v≤L)
    (hA : 16*L<2^m) (hg : 2^m≤x.g)
    (hb : 4*x.b<5*b) (hlarge : 16*L*b<(2^m)^3) :
    4*x.F m<2^m := by
  let A := 2^m
  have ha : x.a=A*x.s m := a_eq x m hm
  have hApos : 0<A := Nat.two_pow_pos _
  have hspos : 0<x.s m := by unfold Data.s; exact Nat.two_pow_pos _
  have hAspos : 0<A*x.s m := Nat.mul_pos hApos hspos
  have hid := g_identity x hv
  have h2A : 2*A≤2*x.g := Nat.mul_le_mul_left 2 hg
  have hrel : 2*A≤2*L+3*x.r := by
    have hcoeff : 2*x.v-3≤2*L := by omega
    omega
  have hrel8 : 16*A≤16*L+24*x.r := by omega
  have hr : 5*A<8*x.r := by omega
  have hs1 : 5*A*A*x.s m<8*x.b := by
    have hh := Nat.mul_lt_mul_of_pos_left hr hAspos
    unfold Data.b
    rw [ha]
    calc
      5*A*A*x.s m=(A*x.s m)*(5*A) := by ac_rfl
      _ <(A*x.s m)*(8*x.r) := hh
      _ =8*(A*x.s m*x.r) := by ac_rfl
      _ =8*x.b := by rfl
  have hs : A*A*x.s m<2*b := by
    have h1 := Nat.mul_lt_mul_left 4 hs1
    have h2 := Nat.mul_lt_mul_left 8 hb
    nlinarith
  have hf : A*A*x.F m≤4*L*b := by
    unfold Data.F
    have hcoeff : 2*x.v-3≤2*L := by omega
    calc
      A*A*((2*x.v-3)*x.s m)=(2*x.v-3)*(A*A*x.s m) := by ac_rfl
      _ ≤(2*L)*(2*b) := Nat.mul_le_mul hcoeff (Nat.le_of_lt hs)
      _ =4*L*b := by simp [Nat.mul_assoc, Nat.mul_left_comm, Nat.mul_comm]
  have hmul : A*A*(4*x.F m)≤16*L*b := by
    calc
      A*A*(4*x.F m)=4*(A*A*x.F m) := by ac_rfl
      _ ≤4*(4*L*b) := Nat.mul_le_mul_left 4 hf
      _ =16*L*b := by simp [Nat.mul_assoc, Nat.mul_left_comm, Nat.mul_comm]
  change 16*L*b<A^3 at hlarge
  have hp : A^3=A*A*A := by simp [Nat.pow_succ]
  have hlt : A*A*(4*x.F m)<A*A*A := by omega
  exact Nat.lt_of_mul_lt_mul_left hlt

theorem small_k (A L G k : Nat) (_hA : 0<A) (hL : 0<L)
    (hG : A*k≤G) (hlarge : 16*L*G<A*A) : 12*k<A := by
  have h1 : 12≤16*L := by omega
  have h2 : A*(12*k)≤16*L*G := by
    calc
      A*(12*k)=12*(A*k) := by grind
      _ ≤ (16*L)*G := Nat.mul_le_mul h1 hG
      _ = 16*L*G := rfl
  exact Nat.lt_of_mul_lt_mul_left (Nat.lt_of_le_of_lt h2 hlarge)

theorem adjacent_small (x y : Data) (m k l : Nat)
    (hx : m≤x.v) (hy : m≤y.v) (hxv : 2≤x.v) (hyv : 2≤y.v)
    (hg : x.g=2^m*k) (hh : y.g=2^m*l)
    (hF : 4*x.F m<2^m) (hFy : 4*y.F m<2^m)
    (hk : 12*k<2^m) (h : Adj x y) :
    y.v<x.v ∧ x.s m*k=y.s m*l := by
  let A := 2^m
  have hA : 0<A := Nat.two_pow_pos _
  have hscaled : x.s m*x.r+k=y.s m*y.r := by
    unfold Adj Data.b at h
    rw [a_eq x m hx, a_eq y m hy, hg] at h
    change (A*x.s m)*x.r+A*k=(A*y.s m)*y.r at h
    apply Nat.mul_left_cancel hA
    grind
  have hix := g_identity x hxv
  have hiy := g_identity y hyv
  rw [hg] at hix
  rw [hh] at hiy
  change 2*(A*k)=2*x.v-3+3*x.r at hix
  change 2*(A*l)=2*y.v-3+3*y.r at hiy
  have heq : (2*A)*(y.s m*l)+x.F m=(2*A)*(x.s m*k)+y.F m+3*k := by
    unfold Data.F
    have hxmul := congrArg (fun n : Nat => x.s m*n) hix
    have hymul := congrArg (fun n : Nat => y.s m*n) hiy
    have hsmul := congrArg (fun n : Nat => 3*n) hscaled
    grind
  change 4*x.F m<A at hF
  change 4*y.F m<A at hFy
  change 12*k<A at hk
  have hsmallX : x.F m<2*A := by omega
  have hsmallY : y.F m+3*k<2*A := by omega
  have hmod := congrArg (fun n : Nat => n%(2*A)) heq
  have hmod1 : ((2*A)*(y.s m*l)+x.F m)%(2*A)=x.F m := by
    rw [Nat.add_mod]
    simp [Nat.mod_eq_of_lt hsmallX]
  have hmod2 : ((2*A)*(x.s m*k)+y.F m+3*k)%(2*A)=y.F m+3*k := by
    rw [Nat.add_assoc, Nat.add_mod]
    simp [Nat.mod_eq_of_lt hsmallY]
  -- Use direct modular simplification.
  rw [hmod1,hmod2] at hmod
  have hkpos : 0<k := by
    have hp := gain_pos x
    rw [hg] at hp
    cases k with
    | zero => simp at hp
    | succ k => omega
  have hvlt : y.v<x.v := by
    by_cases hnv : x.v≤y.v
    · have hmono := F_mono x y m hnv
      omega
    · omega
  have hprod : x.s m*k=y.s m*l := by
    apply Nat.mul_left_cancel (n:=2*A) (by omega)
    omega
  exact ⟨hvlt,hprod⟩


/-- Four consecutive exact source data with one common total gain.  The
bit-length parameter may be any positive L with x.b < 2^L. -/
theorem four_data_cube_gain (x y z w : Data) (L : Nat)
    (hL : 0<L) (hbits : x.b<2^L)
    (hxy : Adj x y) (hyz : Adj y z) (hzw : Adj z w) :
    x.b^2≤16*L*(x.g+y.g+z.g+w.g)^3 := by
  let b := x.b
  let G := x.g+y.g+z.g+w.g
  let m := min x.v (min y.v (min z.v w.v))
  let A := 2^m
  change b^2≤16*L*G^3
  by_cases hgoal : b^2≤16*L*G^3
  · exact hgoal
  · exfalso
    have hsmall : 16*L*G^3<b^2 := by omega
    have hbpos : 0<b := b_pos x
    have hxg := gain_pos x
    have hyg := gain_pos y
    have hzg := gain_pos z
    have hwg := gain_pos w
    have hGpos : 0<G := by dsimp [G]; omega
    have hGx : x.g≤G := by dsimp [G]; omega
    have hGy : y.g≤G := by dsimp [G]; omega
    have hGz : z.g≤G := by dsimp [G]; omega
    have hGw : w.g≤G := by dsimp [G]; omega
    have hApos : 0<A := Nat.two_pow_pos _
    have hmx : m≤x.v := by dsimp [m]; omega
    have hmy : m≤y.v := by dsimp [m]; omega
    have hmz : m≤z.v := by dsimp [m]; omega
    have hmw : m≤w.v := by dsimp [m]; omega
    have hm_cases : m=x.v ∨ m=y.v ∨ m=z.v ∨ m=w.v := by
      dsimp [m]
      omega
    have hby : b≤y.b := by unfold Adj at hxy; dsimp [b]; omega
    have hbz : b≤z.b := by unfold Adj at hyz; omega
    have hbw : b≤w.b := by unfold Adj at hzw; omega
    have hxbg : x.b≤x.a*G := by
      unfold Data.b
      exact Nat.mul_le_mul_left _ (Nat.le_trans (oddpart_le_gain x) hGx)
    have hybg : y.b≤y.a*G := by
      unfold Data.b
      exact Nat.mul_le_mul_left _ (Nat.le_trans (oddpart_le_gain y) hGy)
    have hzbg : z.b≤z.a*G := by
      unfold Data.b
      exact Nat.mul_le_mul_left _ (Nat.le_trans (oddpart_le_gain z) hGz)
    have hwbg : w.b≤w.a*G := by
      unfold Data.b
      exact Nat.mul_le_mul_left _ (Nat.le_trans (oddpart_le_gain w) hGw)
    have hbAG : b≤A*G := by
      rcases hm_cases with h|h|h|h
      · simpa [A,h,Data.a,b] using hxbg
      · simpa [A,h,Data.a] using Nat.le_trans hby hybg
      · simpa [A,h,Data.a] using Nat.le_trans hbz hzbg
      · simpa [A,h,Data.a] using Nat.le_trans hbw hwbg
    have ha0 : 1≤x.a := by
      unfold Data.a
      have hp := Nat.two_pow_pos x.v
      omega
    have hr0 : 3≤x.r := by unfold Data.r; omega
    have hb3 : 3≤b := by
      dsimp [b,Data.b]
      calc
        3=1*3 := by omega
        _ ≤x.a*x.r := Nat.mul_le_mul ha0 hr0
    have hL2 : 2≤L := by
      by_contra hh
      have hL1 : L≤1 := by omega
      have hp := Nat.pow_le_pow_right (n:=2) (by decide : 0<2) hL1
      omega
    have hGquarter : 4*G<b := by
      by_contra hh
      have hbg : b≤4*G := by omega
      have hbgpow : b^2≤16*G^2 := by
        calc
          b^2≤(4*G)^2 := Nat.pow_le_pow_left hbg
          _ =16*G^2 := by simp [Nat.pow_succ, Nat.mul_assoc, Nat.mul_left_comm, Nat.mul_comm]
      have htmp : 16*G^2*(L*G)<16*G^2 := by
        calc
          16*G^2*(L*G)=16*L*G^3 := by simp [Nat.pow_succ, Nat.mul_assoc, Nat.mul_left_comm, Nat.mul_comm]
          _ <b^2 := hsmall
          _ ≤16*G^2 := hbgpow
      have hLG : L*G<1 := Nat.lt_of_mul_lt_mul_left htmp
      have hGone : 1≤G := by omega
      have hLG2 : 2≤L*G := Nat.mul_le_mul hL2 hGone
      omega
    have hGlt : G<b := by omega
    have hb2 := Nat.pow_le_pow_left hbAG 2
    have hlt : 16*L*G^3<(A*G)^2 := Nat.lt_of_lt_of_le hsmall hb2
    have hlt' : G^2*(16*L*G)<G^2*(A*A) := by
      have h1 : G^2*(16*L*G)=16*L*G^3 := by grind
      have h2 : G^2*(A*A)=(A*G)^2 := by grind
      rwa [h1,h2]
    have hA2 : 16*L*G<A*A := Nat.lt_of_mul_lt_mul_left hlt'
    have hA3 : 16*L*b<A^3 := by
      calc
        16*L*b ≤ (16*L)*(A*G) := Nat.mul_le_mul_left _ hbAG
        _ = A*(16*L*G) := by grind
        _ < A*(A*A) := Nat.mul_lt_mul_of_pos_left hA2 hApos
        _ = A^3 := by grind
    have hdx := gain_dvd x y m hmx hmy hxy
    have hdy := gain_dvd y z m hmy hmz hyz
    have hdz := gain_dvd z w m hmz hmw hzw
    have hAgx : A≤x.g := Nat.le_of_dvd hxg hdx
    have hAgy : A≤y.g := Nat.le_of_dvd hyg hdy
    have hAgz : A≤z.g := Nat.le_of_dvd hzg hdz
    have hAG : A≤G := Nat.le_trans hAgx hGx
    have hAstrong : 16*L<A := by
      apply Nat.lt_of_mul_lt_mul_left (a:=A) (b:=16*L) (c:=A)
      have h1 := Nat.mul_le_mul_left (16*L) hAG
      have h2 : A*(16*L)=(16*L)*A := Nat.mul_comm _ _
      omega
    have hm2 : 2≤m := by
      by_cases hh : 2≤m
      · exact hh
      · have hp := Nat.pow_le_pow_right (n:=2) (by decide : 0<2) (by omega : m≤1)
        change A≤2 at hp
        omega
    have hbound : ∀ u : Nat, u≤2*b → u<2^(L+1) := by
      intro u hu
      rw [Nat.pow_succ]
      change b<2^L at hbits
      omega
    have hprefixB : ∀ u : Nat, u≤b+G → 4*u<5*b := by
      intro u hu
      have hmul := Nat.mul_le_mul_left 4 hu
      dsimp [G] at hGquarter
      omega
    have hxB4 : 4*x.b<5*b := hprefixB x.b (by dsimp [b]; omega)
    have hyB4 : 4*y.b<5*b := by
      have hyPrefix : y.b≤b+G := by
        unfold Adj at hxy
        dsimp [b,G]
        omega
      exact hprefixB y.b hyPrefix
    have hzB4 : 4*z.b<5*b := by
      have hzPrefix : z.b≤b+G := by
        unfold Adj at hxy hyz
        dsimp [b,G]
        omega
      exact hprefixB z.b hzPrefix
    have hxB : x.b≤2*b := by omega
    have hyB : y.b≤2*b := by omega
    have hzB : z.b≤2*b := by omega
    have hxL := v_bound x L (hbound _ hxB)
    have hyL := v_bound y L (hbound _ hyB)
    have hzL := v_bound z L (hbound _ hzB)
    have hxF := small_F x m L b hmx (by omega) hxL hAstrong hAgx hxB4 hA3
    have hyF := small_F y m L b hmy (by omega) hyL hAstrong hAgy hyB4 hA3
    have hzF := small_F z m L b hmz (by omega) hzL hAstrong hAgz hzB4 hA3
    obtain ⟨k,hk⟩ := hdx
    obtain ⟨l,hl⟩ := hdy
    obtain ⟨n,hn⟩ := hdz
    have hkG : A*k≤G := by change x.g= A*k at hk; omega
    have hlG : A*l≤G := by change y.g= A*l at hl; omega
    have hkSmall := small_k A L G k hApos hL hkG hA2
    have hlSmall := small_k A L G l hApos hL hlG hA2
    obtain ⟨hvy,hprod⟩ := adjacent_small x y m k l hmx hmy
      (by omega) (by omega) hk hl hxF hyF hkSmall hxy
    obtain ⟨hvz,_⟩ := adjacent_small y z m l n hmy hmz
      (by omega) (by omega) hl hn hyF hzF hlSmall hyz
    have hraw : x.a*x.g=y.a*y.g := by
      rw [a_eq x m hmx,a_eq y m hmy,hk,hl]
      change (A*x.s m)*(A*k)=(A*y.s m)*(A*l)
      grind
    obtain ⟨p,hp⟩ := gain_dvd x y y.v (by omega) (by omega) hxy
    change x.g=y.a*p at hp
    have hyg_eq : y.g=x.a*p := by
      apply Nat.mul_left_cancel (n:=y.a) (by unfold Data.a; exact Nat.two_pow_pos _)
      rw [hp] at hraw
      grind
    have hdivB := a_dvd y (z.v+1) (by omega)
    have hdivA : 2^(z.v+1)∣x.a := Nat.pow_dvd_pow 2 (by omega)
    have hdivG : 2^(z.v+1)∣y.g := by
      rw [hyg_eq]
      exact Nat.dvd_trans hdivA (Nat.dvd_mul_right _ _)
    have hdivZ : 2^(z.v+1)∣z.b := by
      unfold Adj at hyz
      rw [←hyz]
      exact Nat.dvd_add hdivB hdivG
    unfold Data.b Data.a at hdivZ
    rw [Nat.pow_succ] at hdivZ
    have hbad := Nat.dvd_of_mul_dvd_mul_left (Nat.two_pow_pos z.v) hdivZ
    unfold Data.r at hbad
    omega

#print axioms four_data_cube_gain


/-- Exactly the successful shifted-counter edge of Space Needle. -/
def Edge (b c : Nat) : Prop :=
  ∃ q v, b=2^v*(2*q+3) ∧ c=b+v+3*(q+1)

theorem edge_strict {b c : Nat} (h : Edge b c) : b<c := by
  rcases h with ⟨q,v,_,h⟩
  omega

/-- Four successful updates, in exact arithmetic edge form. -/
theorem four_step_cube_gain {b c d e f L : Nat}
    (hL : 0<L) (hbits : b<2^L)
    (hbc : Edge b c) (hcd : Edge c d)
    (hde : Edge d e) (hef : Edge e f) :
    b^2≤16*L*(f-b)^3 := by
  rcases hbc with ⟨q0,v0,hb,hc⟩
  rcases hcd with ⟨q1,v1,hc',hd⟩
  rcases hde with ⟨q2,v2,hd',he⟩
  rcases hef with ⟨q3,v3,he',hf⟩
  let x : Data := ⟨v0,q0⟩
  let y : Data := ⟨v1,q1⟩
  let z : Data := ⟨v2,q2⟩
  let w : Data := ⟨v3,q3⟩
  have hxb : x.b=b := hb.symm
  have hyb : y.b=c := hc'.symm
  have hzb : z.b=d := hd'.symm
  have hwb : w.b=e := he'.symm
  have hxc : x.b+x.g=c := by
    rw [hxb]
    change b+(v0+3*(q0+1))=c
    omega
  have hyd : y.b+y.g=d := by
    rw [hyb]
    change c+(v1+3*(q1+1))=d
    omega
  have hze : z.b+z.g=e := by
    rw [hzb]
    change d+(v2+3*(q2+1))=e
    omega
  have hwf : w.b+w.g=f := by
    rw [hwb]
    change e+(v3+3*(q3+1))=f
    omega
  have hxy : Adj x y := by unfold Adj; omega
  have hyz : Adj y z := by unfold Adj; omega
  have hzw : Adj z w := by unfold Adj; omega
  have hgain : x.g+y.g+z.g+w.g=f-b := by omega
  have hmain := four_data_cube_gain x y z w L hL (by rwa [hxb]) hxy hyz hzw
  rwa [hxb,hgain] at hmain

theorem four_step_bitlength_gain {b c d e f : Nat}
    (hbc : Edge b c) (hcd : Edge c d)
    (hde : Edge d e) (hef : Edge e f) :
    b^2≤16*(Nat.log2 b+1)*(f-b)^3 := by
  have hb : b≠0 := by
    rcases hbc with ⟨q,v,hb,_⟩
    rw [hb]
    exact Nat.mul_ne_zero (Nat.ne_of_gt (Nat.two_pow_pos _)) (by omega)
  have hbits := ((Nat.log2_eq_iff hb).mp rfl).2
  exact four_step_cube_gain (by omega) hbits hbc hcd hde hef

#print axioms four_step_cube_gain
#print axioms four_step_bitlength_gain

end NeedleFourStep
