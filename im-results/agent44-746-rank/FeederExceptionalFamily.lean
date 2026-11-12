import FeederExceptionalArithmetic
set_option maxHeartbeats 0

namespace CascadeFeederExceptional
open CascadeFeederSix CascadeSweep CascadeResetInverse
open CascadeUniformFatal CascadeFirstFork CascadeAncestry

/-- The two 1458-adic t=1 feeder exceptions 1085 and 1372 are also
    blank-root unreachable. Their exact inverse chain has one extra
    terminal odd-t0 edge beyond the established six-stage template. -/
theorem fatal_feeder_1085_1372_root_exclusion (n : Nat)
    (hn : n%1458=1085 ∨ n%1458=1372) :
    ResetParent (oddPre n (fatal n)) (fatal n) ∧
      ¬ReachC (2,0) (oddPre n (fatal n),0) := by
  let k := n-2
  let j := k-2
  let p := 2^k
  let u := fatal n
  let d0 := (2*u+5)/9
  let x := oddPre n u
  have hnlow : 1085≤n := by omega
  have hk : 3≤k := by dsimp [k]; omega
  have hjlow : 1≤j := by dsimp [j,k]; omega
  have hp : p=2^(n-2) := by rfl
  have hpow : 2^n=4*p := by
    have he : n=k+2 := by dsimp [k]; omega
    rw [he,Nat.pow_add]
    simp only [show 2^2=4 by decide]
    dsimp [p]
    omega
  have hclose : u+n+4=16*p := by
    dsimp [u,fatal]
    rw [hpow]
    omega
  have hnum : 2*u+5=32*p-2*n-3 := by omega
  have hres : n%18=4 ∨ n%18=5 := by omega
  have hfdiv : (2*u+5)%9=0 := by
    simpa [u] using fatal_divnine n (by omega) hres
  have hd : 9*d0=2*u+5 := by dsimp [d0]; omega
  have hdx : x+8*p+n+3=4*d0 := by
    dsimp [x,oddPre,d0]
    have he : n-2=k := by dsimp [k]; omega
    rw [he]
    dsimp [p]
    omega
  have hxl : 9*x+17*n+39=56*p := by omega
  have hxparent : ResetParent x u :=
    odd_parent_near_top n u (n+4) (by omega)
      (by simpa only [u] using fatal_close n (by omega))
      (by simpa only [u] using fatal_size n (by omega))
      (by simpa only [u] using hfdiv)

  have hgrowth : 10000*n+10000≤p := by
    simpa only [p,k] using growth n (by omega)
  have hkj : j+2=k := by dsimp [j,k]; omega
  have hjn : j+4=n := by dsimp [j,k]; omega
  have hjm1 : (j-1)+5=n := by omega
  have hpj : p=4*2^j := by
    have he : k=j+2 := hkj
    change 2^k=4*2^j
    rw [he,Nat.pow_add]
    simp only [show (2:Nat)^2=4 by decide]
    omega
  have hpj2 : p=8*2^(j-1) := by
    have he : k=(j-1)+3 := by omega
    change 2^k=8*2^(j-1)
    rw [he,Nat.pow_add]
    simp only [show (2:Nat)^3=8 by decide]
    omega

  let h := 2*x-(8*p+k)
  have hpos : 8*p+k≤2*x := by omega
  have hxeq : 2*x=8*p+h+k := by dsimp [h]; omega
  have hlin : 9*h+43*n+60=40*p := by omega
  clear_value h

  let z := (2*h+5)/9
  have hz : 9*z=2*h+5 := by dsimp [z]; omega
  have hhlo0 : 4*p≤h := (geom_h n p h hgrowth hlin).1
  have hhtop0 : 2*h+5<9*p := (geom_h n p h hgrowth hlin).2
  have haPos : 8*2^j+j+5≤4*z := by
    rw [hpj] at hhlo0 hhtop0
    omega
  let a := 4*z-(8*2^j+j+5)
  have haEq : 4*z=8*2^j+a+j+5 := by dsimp [a]; omega
  have haLin : 81*a+425*n+381=158*p :=
    affine_a n p j h z a hjn hpj hlin hz haEq
  clear_value a

  let b := 2*a-(8*2^j+j)
  have hbPos : 8*2^j+j≤2*a :=
    positive_even n p j a hgrowth hpj hjn
      (geom_a n p a hgrowth haLin).1
  have hbEq : 2*a=8*2^j+b+j := by dsimp [b]; omega
  have hbLin : 81*b+931*n+438=154*p :=
    affine_b n p j a b hjn hpj haLin hbEq
  clear_value b

  let c := 2*b-(8*2^j+j)
  have hcPos : 8*2^j+j≤2*b :=
    positive_even n p j b hgrowth hpj hjn
      (geom_b n p b hgrowth hbLin).1
  have hcEq : 2*b=8*2^j+c+j := by dsimp [c]; omega
  have hcLin : 81*c+1943*n+552=146*p :=
    affine_c n p j b c hjn hpj hbLin hcEq
  clear_value c

  let d := 2*c-(8*2^j+j)
  have hdPos : 8*2^j+j≤2*c :=
    positive_even n p j c hgrowth hpj hjn
      (geom_c n p c hgrowth hcLin).1
  have hdEq : 2*c=8*2^j+d+j := by dsimp [d]; omega
  have hdLin : 81*d+3967*n+780=130*p :=
    affine_d n p j c d hjn hpj hcLin hdEq
  clear_value d

  let e := 2*d-(8*2^j+j)
  have hePos : 8*2^j+j≤2*d :=
    positive_even n p j d hgrowth hpj hjn
      (geom_d n p d hgrowth hdLin).1
  have heEq : 2*d=8*2^j+e+j := by dsimp [e]; omega
  have heLin : 81*e+8015*n+1236=98*p :=
    affine_e n p j d e hjn hpj hdLin heEq
  clear_value e

  let q := (2*e+5)/3
  have hq : 3*q=2*e+5 := by dsimp [q]; omega
  have hqband0 := q_e_band n p e q heLin hq hgrowth
  have hqpos : p+n≤2*q := by omega
  let f := 2*q-p-n
  have hfEq0 : 2*q=p+f+n := by dsimp [f]; omega
  have hfLin : 243*f+32303*n+4134=149*p :=
    affine_f n p e q f heLin hq hfEq0
  clear_value f

  have hnumres := exceptional_numeric n p hp hn
  have hxmod : x%3≠2 := mod_x n p x hxl hnumres
  obtain ⟨hhmod,hh27,hh81eq⟩ := mod_h n p h hlin hnumres
  have hh81 : (2*h+5)%81≠0 := by omega
  have haMods := mod_a n p a haLin hnumres
  have hbMods := mod_b n p b hbLin hnumres
  have hcMods := mod_c n p c hcLin hnumres
  have hdMods := mod_d n p d hdLin hnumres
  have heMods := mod_e n p e heLin hnumres
  have hfmod : f%3≠2 := mod_f n p f hfLin hnumres
  have haDiv3 : (2*a+5)%3=0 := by omega
  have hbDiv3 : (2*b+5)%3=0 := by omega
  have hcDiv3 : (2*c+5)%3=0 := by omega
  have hdDiv3 : (2*d+5)%3=0 := by omega
  have heDiv3 : (2*e+5)%3=0 := by omega
  have haNot9 : (2*a+5)%9≠0 := by omega
  have hbNot9 : (2*b+5)%9≠0 := by omega
  have hcNot9 : (2*c+5)%9≠0 := by omega
  have hdNot9 : (2*d+5)%9≠0 := by omega
  have heNot9 : (2*e+5)%9≠0 := by omega

  obtain ⟨hbxlo,hbxhi⟩ := geom_x n p x hgrowth hxl
  obtain ⟨hhlo,hhhi⟩ := geom_h n p h hgrowth hlin
  obtain ⟨hbalo,hbahi⟩ := geom_a n p a hgrowth haLin
  obtain ⟨hbblo,hbbhi⟩ := geom_b n p b hgrowth hbLin
  obtain ⟨hbclo,hbchi⟩ := geom_c n p c hgrowth hcLin
  obtain ⟨hbdlo,hbdhi⟩ := geom_d n p d hgrowth hdLin
  obtain ⟨helo,hehi⟩ := geom_e n p e hgrowth heLin
  have hhlo' : 4*2^k≤h := by simpa [p,k] using hhlo
  have hhtop : 2*h+5<9*2^k := by simpa [p,k] using hhhi
  have hxband : 6*2^k-1≤x ∧ x≤8*2^k-3 := by
    have hpowp : p=2^k := by rfl
    rw [hpowp] at hbxlo hbxhi
    omega
  have haBand : 6*2^j-1≤a ∧ a≤8*2^j-3 := by
    rw [hpj] at hbalo hbahi
    omega
  have hbBand : 6*2^j-1≤b ∧ b≤8*2^j-3 := by
    rw [hpj] at hbblo hbbhi
    omega
  have hcBand : 6*2^j-1≤c ∧ c≤8*2^j-3 := by
    rw [hpj] at hbclo hbchi
    omega
  have hdBand : 6*2^j-1≤d ∧ d≤8*2^j-3 := by
    rw [hpj] at hbdlo hbdhi
    omega
  have heLo : 4*2^j≤e := by rw [hpj] at helo; omega
  have heHi : e<6*2^j-1 := by rw [hpj] at hehi; omega

  have hz2 : z=(2*h+5)/9 := by omega
  have haOdd : 4*((2*h+5)/9)=8*2^j+a+j+5 := by
    rw [←hz2]
    exact haEq
  have hab : 2*a=8*2^j+b+j := hbEq
  have hbc : 2*b=8*2^j+c+j := hcEq
  have hcd : 2*c=8*2^j+d+j := hdEq
  have hde : 2*d=8*2^j+e+j := heEq

  let qa := (2*a+5)/3
  let qb := (2*b+5)/3
  let qc := (2*c+5)/3
  let qd := (2*d+5)/3
  have hqa : 3*qa=2*a+5 := by dsimp [qa]; omega
  have hqb : 3*qb=2*b+5 := by dsimp [qb]; omega
  have hqc : 3*qc=2*c+5 := by dsimp [qc]; omega
  have hqd : 3*qd=2*d+5 := by dsimp [qd]; omega
  have haGap0 := q_a_gap n p a qa haLin hqa hgrowth
  have hbGap0 := q_b_gap n p b qb hbLin hqb hgrowth
  have hcGap0 := q_c_gap n p c qc hcLin hqc hgrowth
  have hdGap0 := q_d_gap n p d qd hdLin hqd hgrowth
  have qGapConvert (v : Nat) (hlo : p<v) (hhi : 2*v<3*p) :
      2*2^(j+1)<v ∧ v<3*2^(j+1) := by
    have hpow1 : 2*2^(j+1)=4*2^j := by rw [Nat.pow_succ]; omega
    have hpow2 : 3*2^(j+1)=6*2^j := by rw [Nat.pow_succ]; omega
    rw [hpj] at hlo hhi
    constructor
    · rw [hpow1]
      exact hlo
    · rw [hpow2]
      omega
  have haGap : 2*2^(j+1)<(2*a+5)/3 ∧ (2*a+5)/3<3*2^(j+1) := by
    simpa [qa] using qGapConvert qa haGap0.1 haGap0.2
  have hbGap : 2*2^(j+1)<(2*b+5)/3 ∧ (2*b+5)/3<3*2^(j+1) := by
    simpa [qb] using qGapConvert qb hbGap0.1 hbGap0.2
  have hcGap : 2*2^(j+1)<(2*c+5)/3 ∧ (2*c+5)/3<3*2^(j+1) := by
    simpa [qc] using qGapConvert qc hcGap0.1 hcGap0.2
  have hdGap : 2*2^(j+1)<(2*d+5)/3 ∧ (2*d+5)/3<3*2^(j+1) := by
    simpa [qd] using qGapConvert qd hdGap0.1 hdGap0.2

  have heBand : 6*2^(j-1)+1≤(2*e+5)/3 ∧
      (2*e+5)/3≤8*2^(j-1)-1 := by
    rw [hpj2] at hqband0
    omega
  have hfEq : 2*((2*e+5)/3)=8*2^(j-1)+f+(j-1)+5 := by
    have hq2 : q=(2*e+5)/3 := rfl
    rw [←hq2,hpj2,hjm1]
    exact hfEq0
  obtain ⟨hfGapLo,hfGapHi⟩ := geom_f n p (j-1) f hpj2 hfLin hgrowth

  have hroot : ¬ReachC (2,0) (x,0) :=
    seven_stage_root_exclusion k j x h a b c d e f hk hjlow hkj
      hxband (by simpa [p] using hxeq) hxmod hhlo' hhtop hh27 hh81 haOdd
      haBand hbBand hcBand hdBand hab hbc hcd hde
      haDiv3 hbDiv3 hcDiv3 hdDiv3
      haNot9 hbNot9 hcNot9 hdNot9
      haGap hbGap hcGap hdGap
      heLo heHi heDiv3 heNot9 heBand hfEq hfGapLo hfGapHi hfmod
  exact ⟨hxparent,by simpa only [x,u] using hroot⟩


/-- In the 1085/1372 residue classes, the fatal height has exactly two
    ResetParent predecessors: its even predecessor and the distinguished
    odd t=1 feeder. This isolates the only remaining immediate branch once
    the odd feeder is excluded. -/
theorem fatal_parent_set_1085_1372 (n : Nat)
    (hn : n%1458=1085 ∨ n%1458=1372) :
    ResetParent (16*2^(n-2)-3*n-7) (fatal n) ∧
      ResetParent (oddPre n (fatal n)) (fatal n) ∧
      (∀ q, ResetParent q (fatal n) →
        q=16*2^(n-2)-3*n-7 ∨ q=oddPre n (fatal n)) := by
  let k := n-2
  let p := 2^k
  let u := fatal n
  let d0 := (2*u+5)/9
  let x := oddPre n u
  let y := 16*p-3*n-7
  have hnlow : 1085≤n := by omega
  have hk : 3≤k := by dsimp [k]; omega
  have hp : p=2^(n-2) := by rfl
  have hpow : 2^n=4*p := by
    have he : n=k+2 := by dsimp [k]; omega
    rw [he,Nat.pow_add]
    simp only [show 2^2=4 by decide]
    dsimp [p]
    omega
  have hclose : u+n+4=16*p := by
    dsimp [u,fatal]
    rw [hpow]
    omega
  have hnum : 2*u+5=32*p-2*n-3 := by omega
  have hres : n%18=4 ∨ n%18=5 := by omega
  have hfdiv : (2*u+5)%9=0 := by
    simpa [u] using fatal_divnine n (by omega) hres
  have hd0 : 9*d0=2*u+5 := by dsimp [d0]; omega
  have hdx : x+8*p+n+3=4*d0 := by
    dsimp [x,oddPre,d0]
    have he : n-2=k := by dsimp [k]; omega
    rw [he]
    dsimp [p]
    omega
  have hxl : 9*x+17*n+39=56*p := by omega
  have hxparent : ResetParent x u :=
    odd_parent_near_top n u (n+4) (by omega)
      (by simpa only [u] using fatal_close n (by omega))
      (by simpa only [u] using fatal_size n (by omega))
      (by simpa only [u] using hfdiv)

  have hgrowth : 10000*n+10000≤p := by
    simpa only [p,k] using growth n (by omega)
  have hEvenScale : 2^(n-1)=2*p := by
    have he : n-1=k+1 := by dsimp [k]; omega
    rw [he,Nat.pow_succ]
    dsimp [p]
    omega
  have hEvenBand : 6*2^(n-1)-1≤u ∧ u≤8*2^(n-1)-3 := by
    rw [hEvenScale]
    dsimp [u,fatal]
    rw [hpow]
    omega
  have hyPos : 3*n+7≤16*p := by omega
  have hyEq : 2*u=8*2^(n-1)+y+(n-1) := by
    rw [hEvenScale]
    dsimp [u,fatal,y]
    rw [hpow]
    omega
  have hyparent : ResetParent y u := Or.inl ⟨n-1,hEvenBand,hyEq⟩

  have hnumres := exceptional_numeric n p hp hn
  have hnum729 : (2*u+5)%729=432 ∨ (2*u+5)%729=108 := by
    rcases hnumres with ⟨hnmod,hpmod⟩ | ⟨hnmod,hpmod⟩ <;> omega
  have hnot81 : (2*u+5)%81≠0 := by
    rcases hnum729 with h | h <;> omega

  have huniq : ∀ q, ResetParent q u → q=y ∨ q=x := by
    intro q hpq
    rcases hpq with ⟨m,hbm,heq⟩ | ⟨m,t,d,hdodd,hbm,hout,hq⟩
    · have hm : m=n-1 := even_band_unique u m (n-1) hbm hEvenBand
      rw [hm] at heq
      left
      dsimp [y]
      omega
    · have htle : t≤2 := by
        by_cases ht : t≤2
        · exact ht
        · have hpow81 : 81∣3^(t+1) := by
            have ht' : 4≤t+1 := by omega
            simpa using Nat.pow_dvd_pow 3 ht'
          have hdiv81 : 81∣2*u+5 := by
            rw [←hout]
            exact dvd_mul_of_dvd_left hpow81 d
          exact False.elim (hnot81 (Nat.mod_eq_zero_of_dvd hdiv81))
      by_cases ht0 : t=0
      · subst t
        have hdval : 3*d=2*u+5 := by simpa using hout.symm
        have hdq : d=(2*u+5)/3 := by omega
        have hgap0 : 2*2^n<d ∧ d<3*2^n := by
          rw [hdq,hnum,hpow]
          omega
        exact False.elim (odd_gap n d hgap0.1 hgap0.2 m (by simpa using hbm))
      · by_cases ht1 : t=1
        · subst t
          have hdval : 9*d=2*u+5 := by simpa using hout.symm
          have hdq : d=(2*u+5)/9 := by omega
          have hband1 : 6*2^(n-2)+1≤2*d ∧ 2*d≤8*2^(n-2)-1 := by
            rw [hdq,hnum,←hp]
            omega
          have hm : m=n-2 :=
            odd_band_scale_unique (2*d) m (n-2) (by simpa using hbm) hband1
          rw [hm] at hq
          have hdx' : x+8*2^(n-2)+n+3=4*d := by
            dsimp [d0] at hdx
            rw [←hp,←hdq] at hdx
            exact hdx
          right
          omega
        · have ht2 : t=2 := by omega
          subst t
          have hdval : 27*d=2*u+5 := by simpa using hout.symm
          have hdq : d=(2*u+5)/27 := by omega
          have hgap2 : 2*2^(n-1)<4*d ∧ 4*d<3*2^(n-1) := by
            rw [hdq,hnum,hEvenScale]
            omega
          exact False.elim
            (odd_gap (n-1) (4*d) hgap2.1 hgap2.2 m (by simpa using hbm))

  simpa [p,k,u,x,y] using ⟨hyparent,hxparent,huniq⟩

/-- If a fatal height in the 1085/1372 classes is root-reachable, its
    even predecessor is root-reachable: the only other immediate parent
    is the distinguished odd feeder, already excluded by the theorem above. -/
theorem fatal_root_reduces_to_even_parent_1085_1372 (n : Nat)
    (hn : n%1458=1085 ∨ n%1458=1372) :
    ReachC (2,0) (fatal n,0) →
      ReachC (2,0) (16*2^(n-2)-3*n-7,0) := by
  let u := fatal n
  let x := oddPre n u
  let y := 16*2^(n-2)-3*n-7
  have hne : u≠2 := by dsimp [u,fatal]; omega
  have huniq : ∀q, ResetParent q u → q=y ∨ q=x := by
    simpa [u,x,y] using (fatal_parent_set_1085_1372 n hn).2.2
  have hxNo : ¬ReachC (2,0) (x,0) := by
    simpa [x,u] using (fatal_feeder_1085_1372_root_exclusion n hn).2
  intro hu
  have hc : ResetChain 2 u := (root_reset_chain_iff u).mp hu
  obtain ⟨q,hqc,hq⟩ := reset_chain_last hc hne
  rcases huniq q hq with hqy | hqx
  · rw [hqy] at hqc
    exact (root_reset_chain_iff y).mpr hqc
  · rw [hqx] at hqc
    exact False.elim (hxNo ((root_reset_chain_iff x).mpr hqc))

end CascadeFeederExceptional
