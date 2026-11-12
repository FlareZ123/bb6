import FeederExceptionalFamily
import FeederExceptionalArithmetic
import FirstForkModulo54

set_option maxHeartbeats 0

namespace CascadeFeeder887

open CascadeResetInverse CascadeSweep CascadeUniformFatal CascadeFirstFork
open CascadeFeederSix CascadeFeederExceptional

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
    2^(m+13122)%6561
        = 2^((m+8748)+4374)%6561 := by congr 1 <;> omega
    _ = 2^(m+8748)%6561 := h1
    _ = 2^((m+4374)+4374)%6561 := by congr 1 <;> omega
    _ = 2^(m+4374)%6561 := h2
    _ = 2^((m)+4374)%6561 := by congr 1 <;> omega
    _ = 2^m%6561 := h3

private theorem pow_period13122_many (m t : Nat) :
    2^(m+13122*t)%6561=2^m%6561 := by
  induction t with
  | zero => simp
  | succ t ih =>
      have hs : m+13122*(t+1)=(m+13122*t)+13122 := by omega
      rw [hs]
      exact (pow_period13122_6561 (m+13122*t)).trans ih

private theorem exceptional887_numeric (n p : Nat)
    (hn : n%13122=887) (hp : p=2^(n-2)) :
    n%6561=887 ∧ p%6561=3869 := by
  let t := n/13122
  have hdecomp : n=887+13122*t := by
    have h := Nat.mod_add_div n 13122
    dsimp [t] at h
    omega
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

private theorem no_even_band_from_gap (k u : Nat)
    (hlo : 4*2^k-3<u) (hhi : u<6*2^k-1) :
    ∀j, ¬(6*2^j-1≤u ∧ u≤8*2^j-3) := by
  intro j
  by_cases hk : 1≤k
  · have hshift : (k+1)-1=k := by omega
    apply TerminalExit.no_even_band (k+1) j u
    · omega
    · simpa [hshift] using hlo
    · simpa [hshift] using hhi
  · have hk0 : k=0 := by omega
    subst k
    have hu : u<5 := by simpa using hhi
    intro hb
    rcases hb with ⟨ha,hb⟩
    by_cases hj : j=0
    · subst j
      simp at ha
      omega
    · have hj1 : 1≤j := by omega
      have hp : 2≤2^j :=
        Nat.pow_le_pow_right (by decide : 0<(2:Nat)) hj1
      have hlow : 11≤6*2^j-1 := by omega
      omega

private theorem parent_backward (u v : Nat)
    (hne : u≠2)
    (huniq : ∀q, ResetParent q u → q=v)
    (hr : ReachC (2,0) (u,0)) :
    ReachC (2,0) (v,0) := by
  have hc : ResetChain 2 u := (root_reset_chain_iff u).mp hr
  obtain ⟨q,hqc,hq⟩ := reset_chain_last hc hne
  have hqv : q=v := huniq q hq
  rw [hqv] at hqc
  exact (root_reset_chain_iff v).mpr hqc

/-- A narrow even-band target with a displayed odd t=2 parent and
    243-nondivisibility: t=0,1,3 are quotient gaps, t=2 is the unique
    odd image, and t>=4 is excluded by 243-nondivisibility. -/
private theorem narrow_exact_two_t2 (k x u a q : Nat)
    (hk : 3≤k)
    (hhigh : 6*2^k≤x)
    (hnarrow : 4*x+10<27*2^k)
    (hnot243 : (2*x+5)%243≠0)
    (heven : 2*x=8*2^k+u+k)
    (hodd : 27*(2*2^k+a+k+3)=8*(2*x+5))
    (hband : 6*2^k-1≤x ∧ x≤8*2^k-3)
    (hp : ResetParent q x) : q=u ∨ q=a := by
  have hpow1 : 2^k=2*2^(k-1) := by
    have he : k=(k-1)+1 := by omega
    rw [he,Nat.pow_succ]
    omega
  have hpPos : 1≤2^k := by positivity
  rcases hp with ⟨m,hbm,heq⟩ | ⟨m,t,d,hdodd,hbm,hout,hq⟩
  · have hm : m=k := even_band_scale_unique x m k hbm hband
    left
    rw [hm] at heq
    omega
  · have htbound : t≤3 := by
      by_cases hle : t≤3
      · exact hle
      · have hpow : 243∣3^(t+1) :=
          Nat.pow_dvd_pow 3 (by omega : 5≤t+1)
        have hdiv : 243∣2*x+5 := by
          rcases hpow with ⟨z,hz⟩
          refine ⟨z*d, ?_⟩
          rw [hout,hz]
          ac_rfl
        exact False.elim (hnot243 (Nat.mod_eq_zero_of_dvd hdiv))
    by_cases ht0 : t=0
    · subst t
      have hN : 2*x+5=3*d := by simpa using hout
      have hgap : 4*2^k<d ∧ d<6*2^k := by omega
      exact False.elim
        (CascadeFeederExceptional.odd_gap (k+1) d hgap.1 hgap.2 m
          (by simpa using hbm))
    · by_cases ht1 : t=1
      · subst t
        have hN : 2*x+5=9*d := by simpa using hout
        have hgap : 2*2^k<2*d ∧ 2*d<3*2^k := by omega
        exact False.elim
          (CascadeFeederExceptional.odd_gap k (2*d) hgap.1 hgap.2 m
            (by simpa using hbm))
      · by_cases ht2 : t=2
        · subst t
          have hN : 2*x+5=27*d := by simpa using hout
          have hpow : 2^k=4*2^(k-2) := by
            have he : k=(k-2)+2 := by omega
            calc
              2^k = 2^((k-2)+2) := congrArg (fun z : Nat => 2^z) he
              _ = 4*2^(k-2) := by rw [Nat.pow_add]; norm_num; omega
          have hband2 : 6*2^(k-2)+1≤4*d ∧
              4*d≤8*2^(k-2)-1 := by
            constructor <;> omega
          have hm : m=k-2 :=
            CascadeFirstFork.odd_band_scale_unique (4*d) m (k-2)
              (by simpa using hbm) hband2
          rw [hm] at hq
          right
          have hlinear : 8*d=2*2^k+a+k+3 := by omega
          have hscale : 8*2^(k-2)=2*2^k := by rw [hpow]; omega
          omega
        · have ht3 : t=3 := by omega
          subst t
          have hN : 2*x+5=81*d := by simpa using hout
          have hgap : 2*2^(k-1)<8*d ∧ 8*d<3*2^(k-1) := by omega
          exact False.elim
            (CascadeFeederExceptional.odd_gap (k-1) (8*d) hgap.1 hgap.2 m
              (by simpa using hbm))

/-- An even-band target whose t=0 and t=1 odd quotients are gaps
    has only its displayed even parent when 27 does not divide 2a+5. -/
private theorem only_even_parent_two_gaps (bandK gapK a b q : Nat)
    (hband : 6*2^bandK-1≤a ∧ a≤8*2^bandK-3)
    (heven : 2*a=8*2^bandK+b+bandK)
    (hnot27 : (2*a+5)%27≠0)
    (hgap0 : 2*2^(gapK-1)<(2*a+5)/3 ∧
      (2*a+5)/3<3*2^(gapK-1))
    (hgap1 : 2*2^(gapK-2)<2*((2*a+5)/9) ∧
      2*((2*a+5)/9)<3*2^(gapK-2))
    (hp : ResetParent q a) : q=b := by
  rcases hp with ⟨m,hbm,heq⟩ | ⟨m,t,d,hdodd,hbm,hout,hq⟩
  · have hm : m=bandK := even_band_scale_unique a m bandK hbm hband
    rw [hm] at heq
    omega
  · have htbound : t≤1 := by
      by_cases hle : t≤1
      · exact hle
      · have hpow : 27∣3^(t+1) :=
          Nat.pow_dvd_pow 3 (by omega : 3≤t+1)
        have hdiv : 27∣2*a+5 := by
          rcases hpow with ⟨z,hz⟩
          refine ⟨z*d, ?_⟩
          rw [hout,hz]
          ac_rfl
        exact False.elim (hnot27 (Nat.mod_eq_zero_of_dvd hdiv))
    by_cases ht0 : t=0
    · subst t
      have hN : 2*a+5=3*d := by simpa using hout
      have hdq : d=(2*a+5)/3 := by omega
      have hgap : 2*2^(gapK-1)<d ∧ d<3*2^(gapK-1) := by
        simpa [hdq] using hgap0
      exact False.elim
        (CascadeFeederExceptional.odd_gap (gapK-1) d hgap.1 hgap.2 m
          (by simpa using hbm))
    · have ht1 : t=1 := by omega
      subst t
      have hN : 9*d=2*a+5 := by simpa using hout.symm
      have hdq : d=(2*a+5)/9 := by omega
      have hgap : 2*2^(gapK-2)<2*d ∧ 2*d<3*2^(gapK-2) := by
        simpa [hdq] using hgap1
      exact False.elim
        (CascadeFeederExceptional.odd_gap (gapK-2) (2*d) hgap.1 hgap.2 m
          (by simpa using hbm))

private theorem middle_low_unique_odd_t0 (u j f q : Nat)
    (hlo : 4*2^j≤u)
    (hhi : u<6*2^j-1)
    (hdiv3 : (2*u+5)%3=0)
    (hnot9 : (2*u+5)%9≠0)
    (hband : 6*2^(j-1)+1≤(2*u+5)/3 ∧
      (2*u+5)/3≤8*2^(j-1)-1)
    (hf : 2*((2*u+5)/3)=8*2^(j-1)+f+(j-1)+5)
    (hp : ResetParent q u) : q=f := by
  have hgap : ∀m, ¬(6*2^m-1≤u ∧ u≤8*2^m-3) :=
    no_even_band_from_gap j u (by omega) hhi
  rcases hp with ⟨m,hbm,heq⟩ | ⟨m,t,d,hdodd,hbm,hout,hq⟩
  · exact False.elim (hgap m hbm)
  · have ht0 : t=0 := by
      by_cases ht : t=0
      · exact ht
      · have hpow : 9∣3^(t+1) :=
          Nat.pow_dvd_pow 3 (by omega : 2≤t+1)
        have hdiv : 9∣2*u+5 := by
          rcases hpow with ⟨z,hz⟩
          refine ⟨z*d, ?_⟩
          rw [hout,hz]
          ac_rfl
        exact False.elim (hnot9 (Nat.mod_eq_zero_of_dvd hdiv))
    subst t
    have hdval : 3*d=2*u+5 := by simpa using hout.symm
    have hdd : d=(2*u+5)/3 := by omega
    have hj : m=j-1 :=
      CascadeFirstFork.odd_band_scale_unique ((2*u+5)/3) m (j-1)
        (by simpa [hdd] using hbm) hband
    rw [hj,hdd] at hq
    omega

private theorem only_even_parent_band (k c d q : Nat)
    (hband : 6*2^k-1≤c ∧ c≤8*2^k-3)
    (heven : 2*c=8*2^k+d+k)
    (hnot3 : (2*c+5)%3≠0)
    (hp : ResetParent q c) : q=d := by
  rcases hp with ⟨m,hbm,heq⟩ | ⟨m,t,e,heodd,hbm,hout,hq⟩
  · have hm : m=k := even_band_scale_unique c m k hbm hband
    rw [hm] at heq
    omega
  · have hpow : 3∣3^(t+1) :=
      Nat.pow_dvd_pow 3 (by omega : 1≤t+1)
    have hdiv : 3∣2*c+5 := by
      rcases hpow with ⟨z,hz⟩
      refine ⟨z*e, ?_⟩
      rw [hout,hz]
      ac_rfl
    exact False.elim (hnot3 (Nat.mod_eq_zero_of_dvd hdiv))

/-- On the single lift n=887 (mod 13122), the t=1 fatal feeder has
    the complete six-node inverse tree x->{u,a}, a->b, b->c, c->d,
    with u and d terminal. -/
theorem fatal_feeder_887_subresidue_root_exclusion (n : Nat)
    (hn : n%13122=887) :
    ResetParent (CascadeFirstFork.oddPre n (CascadeManyShield.fatal n))
      (CascadeManyShield.fatal n) ∧
    ¬ReachC (2,0)
      (CascadeFirstFork.oddPre n (CascadeManyShield.fatal n),0) := by
  have hn4 : 4≤n := by omega
  have h18 : n%18=5 := by omega
  let p : Nat := 2^(n-2)
  let k : Nat := n-2
  let j : Nat := n-4
  let x : Nat := CascadeFirstFork.oddPre n (CascadeManyShield.fatal n)
  have hp4 : 2^n=4*p := by
    dsimp [p]
    have he : n=(n-2)+2 := by omega
    rw [he,Nat.pow_add]
    norm_num
    omega
  have hfdiv : (2*CascadeManyShield.fatal n+5)%9=0 :=
    CascadeFirstFork.fatal_divnine n hn4 (Or.inr h18)
  have hfquot : 9*((2*CascadeManyShield.fatal n+5)/9)=
      2*CascadeManyShield.fatal n+5 := by
    have h := Nat.mod_add_div (2*CascadeManyShield.fatal n+5) 9
    rw [hfdiv] at h
    omega
  have hFlinear :
      2*CascadeManyShield.fatal n+5+2*n+3=32*p := by
    dsimp [CascadeManyShield.fatal]
    rw [hp4]
    omega
  have hx : 9*x+17*n+39=56*p := by
    dsimp [x,CascadeFirstFork.oddPre]
    omega
  have hbig : 10000*n+10000≤p :=
    CascadeFeederSix.growth n (by omega)
  have hnmod : n%6561=887 ∧ p%6561=3869 :=
    exceptional887_numeric n p hn (by rfl)
  rcases hnmod with ⟨hn6561,hp6561⟩
  have h2xmod729 : (2*x+5)%729=324 := by omega
  have hpk : p=2^k := by rfl
  have hpk1 : 2^k=2*2^(k-1) := by
    have he : k=(k-1)+1 := by omega
    rw [he,Nat.pow_succ]
    omega
  have hpk2 : 2^k=4*2^(k-2) := by
    have he : k=(k-2)+2 := by omega
    calc
      2^k = 2^((k-2)+2) := congrArg (fun z : Nat => 2^z) he
      _ = 4*2^(k-2) := by rw [Nat.pow_add]; norm_num; omega
  have hpj : p=4*2^j := by
    dsimp [p,j]
    have he : n-2=(n-4)+2 := by omega
    rw [he,Nat.pow_add]
    norm_num
    omega
  have hjpos : 1≤j := by dsimp [j]; omega
  have hkpos : 3≤k := by dsimp [k]; omega

  let u : Nat := 2*x-8*p-k
  have hxeq : 2*x=8*2^k+u+k := by
    dsimp [u]
    rw [←hpk]
    omega
  have huLin : 9*u+43*n+60=40*p := by
    dsimp [k] at hxeq
    omega
  have humod729 : u%729=558 := by omega

  have h2xmod27 : (2*x+5)%27=0 := by omega
  let dx : Nat := (2*x+5)/27
  have hdx : 27*dx=2*x+5 := by
    have h := Nat.mod_add_div (2*x+5) 27
    rw [h2xmod27] at h
    dsimp [dx]
    omega
  let a : Nat := 8*dx-2*p-n-1
  have hlinearA : 8*dx=2*2^k+a+k+3 := by
    dsimp [a]
    rw [←hpk]
    omega
  have haxeq : 27*(2*2^k+a+k+3)=8*(2*x+5) := by
    calc
      27*(2*2^k+a+k+3) = 27*(8*dx) := by rw [hlinearA]
      _ = 8*(27*dx) := by ring
      _ = 8*(2*x+5) := by rw [hdx]
  have haLin : 243*a+515*n+507=410*p := by omega
  have hamod27 : a%27=2 := by
    dsimp [a]
    omega

  let b : Nat := 2*a-2*p-n+4
  have hscaleA : 8*2^j=2*p := by
    calc
      8*2^j = 2*(4*2^j) := by omega
      _ = 2*p := by rw [hpj]
  have habeq : 2*a=8*2^j+b+j := by
    dsimp [b]
    rw [hscaleA]
    dsimp [j]
    omega
  have hbLin : 243*b+1273*n+42=334*p := by omega
  have hbmod27 : b%27=23 := by
    dsimp [b]
    omega

  have h2bmod9 : (2*b+5)%9=6 := by omega
  have hdivb3 : (2*b+5)%3=0 := by omega
  have hnotb9 : (2*b+5)%9≠0 := by omega
  let db : Nat := (2*b+5)/3
  have hdb : 3*db=2*b+5 := by
    have h := Nat.mod_add_div (2*b+5) 3
    rw [hdivb3] at h
    dsimp [db]
    omega
  have hpj1 : p=8*2^(j-1) := by
    have hj : j=(j-1)+1 := by omega
    calc
      p = 4*2^j := hpj
      _ = 4*(2^(j-1)*2) := by rw [hj,Nat.pow_succ]
      _ = 8*2^(j-1) := by omega
  let c : Nat := 2*db-p-n
  have hbcEq : 2*db=8*2^(j-1)+c+(j-1)+5 := by
    dsimp [c]
    rw [←hpj1]
    dsimp [j]
    omega
  have hcLin : 729*c+5821*n-2262=607*p := by omega
  have hcmod9 : c%9=3 := by
    dsimp [c]
    omega

  let d : Nat := 2*c-p-n+5
  have hcdEq : 2*c=8*2^(j-1)+d+(j-1) := by
    dsimp [d]
    rw [←hpj1]
    dsimp [j]
    omega
  have hdLin : 729*d+12371*n-8169=485*p := by omega
  have hdmod9 : d%9=7 := by
    dsimp [d]
    omega

  have hxband : 6*2^k-1≤x ∧ x≤8*2^k-3 := by
    rw [←hpk]
    omega
  have hxhigh : 6*2^k≤x := by
    rw [←hpk]
    omega
  have hxnarrow : 4*x+10<27*2^k := by
    rw [←hpk]
    omega
  have hxnot243 : (2*x+5)%243≠0 := by omega
  have huGap : 4*2^k-3<u ∧ u<6*2^k-1 := by
    rw [←hpk]
    omega
  have haBand : 6*2^j-1≤a ∧ a≤8*2^j-3 := by
    rw [←hpj]
    omega
  have hbGap : 4*2^j-3<b ∧ b<6*2^j-1 := by
    rw [←hpj]
    omega
  have hcBand : 6*2^(j-1)-1≤c ∧ c≤8*2^(j-1)-3 := by
    rw [←hpj1]
    omega
  have hdGap : 4*2^(j-1)-3<d ∧ d<6*2^(j-1)-1 := by
    rw [←hpj1]
    omega

  have hdxOdd : dx%2=1 := by omega
  have hdxBand : 6*2^j+1≤4*dx ∧ 4*dx≤8*2^j-1 := by
    rw [←hpj]
    omega
  have hdxOut : 2*x+5=3^(2+1)*dx := by norm_num; omega
  have hdxParentEq :
      2*(2^2*dx)=8*2^j+a+j+5 := by
    have hlinear : 8*dx=2*2^k+a+k+3 := by omega
    have hscale : 2*2^k=8*2^j := by
      calc
        2*2^k = 2*p := by rw [←hpk]
        _ = 8*2^j := hscaleA.symm
    have hshift : k+3=j+5 := by dsimp [k,j]; omega
    omega
  have hxeven : ResetParent u x := Or.inl ⟨k,hxband,hxeq⟩
  have hxa : ResetParent a x :=
    Or.inr ⟨j,2,dx,hdxOdd,hdxBand,hdxOut,hdxParentEq⟩

  have hxParents : ∀q, ResetParent q x ↔ q=u∨q=a := by
    intro q
    constructor
    · intro hq
      exact narrow_exact_two_t2 k x u a q hkpos hxhigh hxnarrow
        hxnot243 hxeq haxeq hxband hq
    · intro hq
      rcases hq with hq|hq
      · simpa [hq] using hxeven
      · simpa [hq] using hxa

  have haEq : 2*a=8*2^j+b+j := habeq
  have h2amod27 : (2*a+5)%27=9 := by omega
  have hnotA27 : (2*a+5)%27≠0 := by omega
  have hdivA3 : (2*a+5)%3=0 := by omega
  have hdivA9 : 9*((2*a+5)/9)=2*a+5 := by
    have h := Nat.mod_add_div (2*a+5) 9
    rw [by omega : (2*a+5)%9=0] at h
    omega
  have hdivA3q : 3*((2*a+5)/3)=2*a+5 := by
    have h := Nat.mod_add_div (2*a+5) 3
    rw [hdivA3] at h
    omega
  have haGap0 :
      2*2^(k-1)<(2*a+5)/3 ∧ (2*a+5)/3<3*2^(k-1) := by
    omega
  have haGap1 :
      2*2^(k-2)<2*((2*a+5)/9) ∧
      2*((2*a+5)/9)<3*2^(k-2) := by
    omega
  have haUniq : ∀q, ResetParent q a → q=b := by
    intro q hq
    exact only_even_parent_two_gaps j k a b q haBand haEq hnotA27
      haGap0 haGap1 hq

  have hbLo : 4*2^j≤b := by omega
  have hbHi : b<6*2^j-1 := hbGap.2
  have hqBband :
      6*2^(j-1)+1≤(2*b+5)/3 ∧
      (2*b+5)/3≤8*2^(j-1)-1 := by
    rw [←hpj1]
    omega
  have hdbq : (2*b+5)/3=db := by omega
  have hqBEq :
      2*((2*b+5)/3)=8*2^(j-1)+c+(j-1)+5 := by
    rw [hdbq]
    exact hbcEq
  have hbUniq : ∀q, ResetParent q b → q=c := by
    intro q hq
    exact middle_low_unique_odd_t0 b j c q hbLo hbHi hdivb3 hnotb9
      hqBband hqBEq hq

  have hcmod3 : c%3=0 := by omega
  have hnotC3 : (2*c+5)%3≠0 := by omega
  have hcUniq : ∀q, ResetParent q c → q=d := by
    intro q hq
    exact only_even_parent_band (j-1) c d q hcBand hcdEq hnotC3 hq

  have huNoBand : ∀m, ¬(6*2^m-1≤u ∧ u≤8*2^m-3) :=
    no_even_band_from_gap k u huGap.1 huGap.2
  have huDead : ¬ReachC (2,0) (u,0) :=
    CascadeSweep.root_excludes_nonimage u (by omega) huNoBand
  have hdNoBand : ∀m, ¬(6*2^m-1≤d ∧ d≤8*2^m-3) :=
    no_even_band_from_gap (j-1) d hdGap.1 hdGap.2
  have hdDead : ¬ReachC (2,0) (d,0) :=
    CascadeSweep.root_excludes_nonimage d (by omega) hdNoBand

  have hxNe : x≠2 := by omega
  have hsplit :
      ReachC (2,0) (x,0) ↔
        ReachC (2,0) (u,0) ∨ ReachC (2,0) (a,0) :=
    CascadeFirstFork.rooted_two_parents x u a hxNe hxeven hxa hxParents
  have haNe : a≠2 := by omega
  have hbNe : b≠2 := by omega
  have hcNe : c≠2 := by omega
  have hNoX : ¬ReachC (2,0) (x,0) := by
    intro hxroot
    rcases hsplit.mp hxroot with huroot|haroot
    · exact huDead huroot
    · have hbroot := parent_backward a b haNe haUniq haroot
      have hcroot := parent_backward b c hbNe hbUniq hbroot
      have hdroot := parent_backward c d hcNe hcUniq hcroot
      exact hdDead hdroot

  have hxfatal : ResetParent x (CascadeManyShield.fatal n) :=
    CascadeFirstFork.fatal_has_odd_parent n hn4 h18
  exact ⟨by simpa [x] using hxfatal, by simpa [x] using hNoX⟩

/-- The generic exact fatal parent set then reduces this lift to its
    even fatal predecessor. -/
theorem fatal_root_iff_even_parent_887_subresidue (n : Nat)
    (hn : n%13122=887) :
    ReachC (2,0) (CascadeManyShield.fatal n,0) ↔
      ReachC (2,0) (CascadeFirstFork.evenPre n (n+4),0) := by
  have hdecomp : n=887+13122*(n/13122) := by
    have h := Nat.mod_add_div n 13122
    omega
  have h1458 : n%1458=887 := by
    rw [hdecomp]
    omega
  have hEight :
      n%1458=113 ∨ n%1458=400 ∨ n%1458=526 ∨ n%1458=599 ∨
        n%1458=886 ∨ n%1458=887 ∨ n%1458=1085 ∨ n%1458=1372 :=
    Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h1458)))))
  have hfeed := fatal_feeder_887_subresidue_root_exclusion n hn
  exact CascadeFeederExceptional.fatal_root_iff_even_parent_eight_exceptional
    n hEight hfeed.2

#print axioms fatal_feeder_887_subresidue_root_exclusion
#print axioms fatal_root_iff_even_parent_887_subresidue

end CascadeFeeder887
