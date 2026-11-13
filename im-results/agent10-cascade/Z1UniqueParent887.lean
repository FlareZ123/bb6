import FeederExceptional887

set_option maxHeartbeats 0
set_option maxRecDepth 8192
set_option exponentiation.threshold 5000

namespace CascadeFeeder887SecondTier

open CascadeResetInverse CascadeFeederExceptional CascadeFirstFork CascadeFeederSix

private theorem pow_period4374_6561 (m : Nat) :
    2^(m+4374)%6561=2^m%6561 := by
  rw [Nat.pow_add,Nat.mul_mod]
  have h : (2:Nat)^4374%6561=1 := by decide
  rw [h]
  simp

private theorem pow_period13122_6561 (m : Nat) :
    2^(m+13122)%6561=2^m%6561 := by
  have h1 := pow_period4374_6561 (m+8748)
  have h2 := pow_period4374_6561 (m+4374)
  have h3 := pow_period4374_6561 m
  calc
    2^(m+13122)%6561 = 2^((m+8748)+4374)%6561 := by congr 1 <;> omega
    _ = 2^(m+8748)%6561 := h1
    _ = 2^((m+4374)+4374)%6561 := by congr 1 <;> omega
    _ = 2^(m+4374)%6561 := h2
    _ = 2^m%6561 := h3

private theorem pow_period13122_many (m t : Nat) :
    2^(m+13122*t)%6561=2^m%6561 := by
  induction t with
  | zero => simp
  | succ t ih =>
      have hs : m+13122*(t+1)=(m+13122*t)+13122 := by omega
      rw [hs]
      exact (pow_period13122_6561 (m+13122*t)).trans ih

private theorem exceptional887_numeric_local (n p : Nat)
    (hn : n%13122=887) (hp : p=2^(n-2)) :
    n%6561=887 ∧ p%6561=3869 := by
  let t := n/13122
  have hdecomp : n=887+13122*t := by
    have h := Nat.mod_add_div n 13122
    rw [hn] at h
    simpa [t] using h.symm
  have hnmod : n%6561=887 := by
    rw [hdecomp]
    omega
  have hexp : n-2=885+13122*t := by omega
  have hpow := pow_period13122_many 885 t
  have hpow' : 2^(n-2)%6561=2^885%6561 := by
    rw [hexp]
    exact hpow
  have hval : 2^885%6561=3869 := by decide
  constructor
  · exact hnmod
  · rw [hp]
    exact hpow'.trans hval

theorem no_even_band_gap (k m u : Nat)
    (hlo : 4*2^k≤u+2)
    (hhi : u+1<6*2^k) :
    ¬ (6*2^m-1≤u ∧ u≤8*2^m-3) := by
  intro hband
  rcases hband with ⟨hbandlo,hbandhi⟩
  by_cases hm : m<k
  · have hpow : 2^(m+1)≤2^k :=
      Nat.pow_le_pow_right (by decide : 0<(2:Nat)) (by omega)
    have hdouble : 2*2^m≤2^k := by
      rw [Nat.pow_succ] at hpow
      simpa [Nat.mul_comm] using hpow
    have hscale : 8*2^m≤4*2^k := by
      have hmul := Nat.mul_le_mul_left 4 hdouble
      calc
        8*2^m = 4*(2*2^m) := by omega
        _ ≤ 4*2^k := hmul
    have hband' : u+3≤8*2^m := by omega
    have hcontr : u+3≤4*2^k := Nat.le_trans hband' hscale
    omega
  · have hpow : 2^k≤2^m :=
      Nat.pow_le_pow_right (by decide : 0<(2:Nat)) (by omega)
    have hscale : 6*2^k≤6*2^m := Nat.mul_le_mul_left 6 hpow
    have hband' : 6*2^m≤u+1 := by omega
    have hcontr : 6*2^k≤u+1 := Nat.le_trans hscale hband'
    omega

def A (p n : Nat) : Nat := 40*p - 2059*n - 3084
def T (p n : Nat) : Nat := 80*p - 4118*n - 6123
def z1 (p n : Nat) : Nat := A p n / 9
def z2 (p n : Nat) : Nat := 12*(T p n / 243) - (2*p+n+1)

theorem t0_gap (n p e : Nat)
    (hbig : 10000*n+10000≤p)
    (hT : 27*e+4118*n+6123=80*p) :
    2*p<e ∧ e<3*p := by omega

theorem t1_band (n r e : Nat)
    (hbig : 10000*n+10000≤4*r)
    (hT : 81*e+4118*n+6123=320*r) :
    6*r+1≤2*e ∧ 2*e≤8*r-1 := by omega

theorem t2_gap (n r e : Nat)
    (hbig : 10000*n+10000≤2*r)
    (hT : 243*e+4118*n+6123=160*r) :
    2*r<4*e ∧ 4*e<3*r := by omega

theorem z2_nonnegative (n p d : Nat)
    (hbig : 10000*n+10000≤p)
    (hT : 243*d+4118*n+6123=80*p) :
    2*p+n+1≤12*d := by omega

theorem second_parent_eq (n p q d : Nat) (hn4:4≤n)
    (hscale:8*2^(n-4)=2*p)
    (heq:2*(2*(3*d))=8*2^(n-4)+q+(n-4)+5) :
    12*d=2*p+q+n+1 := by
  rw [hscale] at heq
  omega

theorem z1_unique_parent (n p : Nat)
    (hn : 5≤n)
    (hp : p=2^(n-2))
    (hbig : 10000*n+10000≤p)
    (hTmod : T p n %729=486) :
    ∀q, ResetParent q (z1 p n) → q=z2 p n := by
  let a := A p n
  let tval := T p n
  let u := z1 p n
  let d := tval/243
  let z := 12*d-(2*p+n+1)
  have haPos : 2059*n+3084≤40*p := by omega
  have htPos : 4118*n+6123≤80*p := by omega
  have hTlinear : tval+4118*n+6123=80*p := by
    have h := Nat.sub_add_cancel htPos
    dsimp [tval,T]
    rw [Nat.sub_sub]
    simpa [Nat.add_assoc] using h
  have hta : tval=2*a+45 := by
    dsimp [tval,a,T,A]
    omega
  have hmod9 : tval%9=0 := by
    have h := Nat.mod_mod_of_dvd tval (show 9∣729 from ⟨81,by decide⟩)
    rw [hTmod] at h
    have hc : 486%9=0 := by decide
    simpa [hc] using h.symm
  have hamod : a%9=0 := by omega
  have haeq : 9*u=a := by
    change 9*(a/9)=a
    have h := Nat.mod_add_div a 9
    rw [hamod] at h
    simpa using h
  have htzu : tval=9*(2*u+5) := by
    rw [hta,←haeq]
    omega
  have hmod243 : tval%243=0 := by
    have h := Nat.mod_mod_of_dvd tval (show 243∣729 from ⟨3,by decide⟩)
    rw [hTmod] at h
    have hc : 486%243=0 := by decide
    simpa [hc] using h.symm
  have hdiv243 : 243*d=tval := by
    dsimp [d]
    have h := Nat.mod_add_div tval 243
    rw [hmod243] at h
    omega
  have hnot729 : ¬729∣tval := by
    intro h
    have hz := Nat.mod_eq_zero_of_dvd h
    rw [hTmod] at hz
    exact (by decide : 486≠0) hz
  have hd27 : 27*d=2*u+5 := by
    apply Nat.mul_left_cancel (n:=9) (by decide)
    calc
      9*(27*d)=243*d := by omega
      _=tval := hdiv243
      _=9*(2*u+5) := htzu
  have hAeq2 : a+2059*n+3084=40*p := by
    have h := Nat.sub_add_cancel haPos
    dsimp [a,A]
    rw [Nat.sub_sub]
    simpa [Nat.add_assoc] using h
  have hAlinear : 9*u+2059*n+3084=40*p := by
    rw [haeq]
    exact hAeq2
  have hcoef1 : 2059*n≤10000*n :=
    Nat.mul_le_mul_right n (by decide : 2059≤10000)
  have hcoef2 : 3066≤10000 := by decide
  have hcoef3 : 2059*n+3066≤10000*n+10000 :=
    Nat.add_le_add hcoef1 hcoef2
  have hp4 : p≤4*p := by
    simpa using Nat.mul_le_mul_right p (by decide : 1≤4)
  have hcoef : 2059*n+3066≤4*p :=
    Nat.le_trans hcoef3 (Nat.le_trans hbig hp4)
  have hsum0 : 36*p+(2059*n+3066)≤36*p+4*p :=
    Nat.add_le_add_left hcoef (36*p)
  have hconst : 36+4=40 := by decide
  have hsum : 36*p+(2059*n+3066)≤40*p := by
    calc
      _ ≤36*p+4*p := hsum0
      _ =40*p := by rw [←Nat.add_mul,hconst]
  have hAlinear2 : 40*p=9*u+18+(2059*n+3066) := by
    rw [←hAlinear]
    omega
  have hsum' : 36*p+(2059*n+3066)≤(9*u+18)+(2059*n+3066) := by
    rw [hAlinear2] at hsum
    exact hsum
  have hcancel : 36*p≤9*u+18 := Nat.le_of_add_le_add_right hsum'
  have hmul : 9*(4*p)≤9*(u+2) := by
    rw [show 9*(4*p)=36*p by omega,
        show 9*(u+2)=9*u+18 by omega]
    exact hcancel
  have hulo : 4*p≤u+2 := Nat.le_of_mul_le_mul_left hmul (by decide : 0<9)
  have hsumUpper : 9*(u+1)+(2059*n+3075)=40*p := by
    have hc : 9+3075=3084 := by decide
    calc
      9*(u+1)+(2059*n+3075) = (9*u+9)+(2059*n+3075) := by rw [Nat.mul_add]
      _ = 9*u+(9+(2059*n+3075)) := by rw [Nat.add_assoc]
      _ = 9*u+((9+2059*n)+3075) := by rw [Nat.add_assoc]
      _ = 9*u+((2059*n+9)+3075) := by rw [Nat.add_comm 9 (2059*n)]
      _ = 9*u+(2059*n+(9+3075)) := by rw [Nat.add_assoc]
      _ = 9*u+(2059*n+3084) := by rw [hc]
      _ = 9*u+2059*n+3084 := by rw [Nat.add_assoc]
      _ =40*p := hAlinear
  have hupper1 : 9*(u+1)≤40*p := by
    calc
      _ ≤9*(u+1)+(2059*n+3075) := Nat.le_add_right _ _
      _ =40*p := hsumUpper
  have h10000 : 10000≤10000*n+10000 := by
    simp [Nat.add_comm]
  have hsumPos : 0<10000*n+10000 := Nat.lt_of_lt_of_le (by decide : 0<10000) h10000
  have hpPos : 0<p := Nat.lt_of_lt_of_le hsumPos hbig
  have hupper2 : 40*p<54*p := (Nat.mul_lt_mul_right hpPos).2 (by decide : 40<54)
  have hupper3 : 9*(u+1)<9*(6*p) := by
    have h := Nat.lt_of_le_of_lt hupper1 hupper2
    rw [show 9*(6*p)=54*p by omega]
    exact h
  have huhi : u+1<6*p := Nat.lt_of_mul_lt_mul_left hupper3
  have hpr4 : p=4*2^(n-4) := by
    rw [hp]
    have hn4 : 4≤n := Nat.le_trans (by decide : 4≤5) hn
    have he : n-2=(n-4)+2 := by
      apply (Nat.sub_eq_iff_eq_add (Nat.le_trans (by decide : 2≤5) hn)).2
      have hs := Nat.sub_add_cancel hn4
      calc
        n=(n-4)+4 := hs.symm
        _=(n-4)+2+2 := by simp [Nat.add_assoc]
    rw [he,Nat.pow_add]
    have hfour : 2^2=4 := by decide
    rw [hfour,Nat.mul_comm]
  have hpr3 : p=2*2^(n-3) := by
    rw [hp]
    have hn3 : 3≤n := Nat.le_trans (by decide : 3≤5) hn
    have he : n-2=(n-3)+1 := by
      apply (Nat.sub_eq_iff_eq_add (Nat.le_trans (by decide : 2≤5) hn)).2
      have hs := Nat.sub_add_cancel hn3
      calc
        n=(n-3)+3 := hs.symm
        _=(n-3)+1+2 := by simp [Nat.add_assoc]
    rw [he,Nat.pow_succ,Nat.mul_comm]
  intro q hparent
  rcases hparent with ⟨m,hband,heven⟩ | ⟨m,t,e,heodd,hband,hout,heq⟩
  · have hno : ¬(6*2^m-1≤u ∧ u≤8*2^m-3) :=
      no_even_band_gap (n-2) m u (by simpa [hp] using hulo) (by simpa [hp] using huhi)
    exact False.elim (hno hband)
  · have hpowT : 3^(t+3)=3^(t+1)*9 := by
      rw [show t+3=(t+1)+2 by omega, Nat.pow_add]
    have hTfactor : tval=3^(t+3)*e := by
      calc
        tval=9*(2*u+5) := htzu
        _=9*(3^(t+1)*e) := by rw [hout]
        _=3^(t+3)*e := by rw [hpowT]; simp [Nat.mul_assoc,Nat.mul_comm]
    have htle : t≤2 := by
      by_cases hle : t≤2
      · exact hle
      · have ht3 : 3≤t := by omega
        have hpow : 3^6∣3^(t+3) := Nat.pow_dvd_pow 3 (by omega)
        rcases hpow with ⟨c,hc⟩
        have hdiv : 729∣tval := by
          refine ⟨c*e,?_⟩
          calc
            tval=3^(t+3)*e := hTfactor
            _=(3^6*c)*e := by rw [hc]
            _=3^6*(c*e) := by simp [Nat.mul_assoc]
        exact False.elim (hnot729 hdiv)
    by_cases ht0 : t=0
    · subst t
      have ht27 : tval=27*e := by simpa using hTfactor
      have hTlin27 : 27*e+4118*n+6123=80*p := by rw [ht27] at hTlinear; exact hTlinear
      rcases t0_gap n p e hbig hTlin27 with ⟨hlo,hhi⟩
      have hgaplo : 2*2^(n-2)<e := by rw [←hp]; exact hlo
      have hgaphi : e<3*2^(n-2) := by rw [←hp]; exact hhi
      exact False.elim (CascadeFeederExceptional.odd_gap (n-2) e hgaplo hgaphi m (by simpa using hband))
    · by_cases ht1 : t=1
      · subst t
        have ht81 : tval=81*e := by simpa using hTfactor
        have he3d : e=3*d := by
          apply Eq.symm
          apply Nat.mul_left_cancel (n:=81) (by decide)
          calc
            81*(3*d)=243*d := by omega
            _=tval := hdiv243
            _=81*e := ht81
        let r := 2^(n-4)
        have hr : p=4*r := by simpa [r] using hpr4
        have hTlin81 : 81*e+4118*n+6123=320*r := by
          rw [ht81,hr] at hTlinear
          calc
            81*e+4118*n+6123=80*(4*r) := hTlinear
            _=(80*4)*r := by rw [Nat.mul_assoc]
            _=320*r := by rw [show 80*4=320 by decide]
        have hbigR : 10000*n+10000≤4*r := by rw [←hr]; exact hbig
        rcases t1_band n r e hbigR hTlin81 with ⟨hlow,hhigh⟩
        have hbandTarget :
            6*2^(n-4)+1≤2*e ∧ 2*e≤8*2^(n-4)-1 := by
          simpa [r] using And.intro hlow hhigh
        have hm : m=n-4 := CascadeFirstFork.odd_band_scale_unique (2*e) m (n-4) hband hbandTarget
        have hscale : 8*2^(n-4)=2*p := by rw [hpr4]; omega
        have heq' : 12*d=2*p+q+n+1 := by
          rw [hm] at heq
          have hpow2 : 2^1=2 := by decide
          rw [hpow2,he3d] at heq
          exact second_parent_eq n p q d (Nat.le_trans (by decide : 4≤5) hn) hscale heq
        have hTlinD : 243*d+4118*n+6123=80*p := by
          rw [hdiv243]
          exact hTlinear
        have hzpos : 2*p+n+1≤12*d := z2_nonnegative n p d hbig hTlinD
        have hz : z+(2*p+n+1)=12*d := by
          dsimp [z]
          exact Nat.sub_add_cancel hzpos
        have hsum : z+(2*p+n+1)=q+(2*p+n+1) := by
          calc
            z+(2*p+n+1)=12*d := hz
            _=2*p+q+n+1 := heq'
            _=q+(2*p+n+1) := by
              simp [Nat.add_comm,Nat.add_left_comm]
        have hfinal : z=q := Nat.add_right_cancel hsum
        change q=z
        exact hfinal.symm
      · have ht2 : t=2 := by omega
        subst t
        have ht243 : tval=243*e := by simpa using hTfactor
        let r := 2^(n-3)
        have hr : p=2*r := by simpa [r] using hpr3
        have hTlin243 : 243*e+4118*n+6123=160*r := by
          rw [ht243,hr] at hTlinear
          calc
            243*e+4118*n+6123=80*(2*r) := hTlinear
            _=(80*2)*r := by rw [Nat.mul_assoc]
            _=160*r := by rw [show 80*2=160 by decide]
        have hbigR : 10000*n+10000≤2*r := by rw [←hr]; exact hbig
        rcases t2_gap n r e hbigR hTlin243 with ⟨hlo,hhi⟩
        have hgaplo : 2*2^(n-3)<4*e := by simpa [r] using hlo
        have hgaphi : 4*e<3*2^(n-3) := by simpa [r] using hhi
        exact False.elim (CascadeFeederExceptional.odd_gap (n-3) (4*e) hgaplo hgaphi m (by simpa using hband))

theorem z1_unique_parent_887 (n : Nat) (hn : n%13122=887) :
    ∀q, ResetParent q (z1 (2^(n-2)) n) → q=z2 (2^(n-2)) n := by
  let p := 2^(n-2)
  have hmodle : n%13122≤n := Nat.mod_le n 13122
  have hnge : 887≤n := by rw [hn] at hmodle; omega
  have hn5 : 5≤n := Nat.le_trans (by decide : 5≤887) hnge
  have hp : p=2^(n-2) := rfl
  have hbig : 10000*n+10000≤p := by
    dsimp [p]
    exact CascadeFeederSix.growth n (by omega)
  have hnum := exceptional887_numeric_local n p hn hp
  have hn6561 : n%6561=887 := hnum.1
  have hp6561 : p%6561=3869 := hnum.2
  have hn729 : n%729=158 := by
    have h := Nat.mod_mod_of_dvd n (show 729∣6561 from ⟨9,by decide⟩)
    rw [hn6561] at h
    have hc : 887%729=158 := by decide
    simpa [hc] using h.symm
  have hp729 : p%729=224 := by
    have h := Nat.mod_mod_of_dvd p (show 729∣6561 from ⟨9,by decide⟩)
    rw [hp6561] at h
    have hc : 3869%729=224 := by decide
    simpa [hc] using h.symm
  have hTpos : 4118*n+6123≤80*p := by omega
  have hTlinear : T p n+4118*n+6123=80*p := by
    have h := Nat.sub_add_cancel hTpos
    dsimp [T]
    rw [Nat.sub_sub]
    simpa [Nat.add_assoc] using h
  have hTmod : T p n%729=486 := by
    have h := congrArg (fun x=>x%729) hTlinear
    simp [Nat.add_mod,Nat.mul_mod,hn729,hp729] at h
    omega
  change ∀q, ResetParent q (z1 p n) → q=z2 p n
  exact z1_unique_parent n p hn5 hp hbig hTmod

#print axioms z1_unique_parent_887

end CascadeFeeder887SecondTier