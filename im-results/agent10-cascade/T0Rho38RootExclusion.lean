import ResetChain

set_option maxHeartbeats 0
set_option maxRecDepth 8192

namespace CascadeT0Rho38

open CascadeResetInverse CascadeSweep

def entry (a K : Nat) : Nat :=
  8*2^K + K -
    (( (2*K+7)*2^(K+4-a) + 2*K+1 - 16*2^K) / 3)

private theorem pow_period_two (n : Nat) :
    2^(n+2)%3 = 2^n%3 := by
  rw [Nat.pow_add]
  simp [Nat.mul_mod]

private theorem pow_mod_two (n : Nat) :
    2^n%3 = 2^(n%2)%3 := by
  induction n using Nat.strongRecOn with
  | ind n ih =>
    by_cases hn : n < 2
    · simp [Nat.mod_eq_of_lt hn]
    · have hm : n-2<n := by omega
      have he : n=(n-2)+2 := by omega
      rw [he,pow_period_two]
      rw [ih (n-2) hm]
      have hemod : ((n-2)+2)%2=(n-2)%2 := by omega
      rw [hemod]

private theorem pow_two_mod3_even (n : Nat) (hn : n%2=0) :
    2^n%3=1 := by
  have hp := pow_mod_two n
  rw [hn] at hp
  norm_num at hp
  exact hp

private theorem pow_period_eighteen (n : Nat) :
    2^(n+18)%27 = 2^n%27 := by
  rw [Nat.pow_add]
  simp [Nat.mul_mod]

private theorem pow_mod_eighteen (n : Nat) :
    2^n%27 = 2^(n%18)%27 := by
  induction n using Nat.strongRecOn with
  | ind n ih =>
    by_cases hn : n < 18
    · simp [Nat.mod_eq_of_lt hn]
    · have hm : n-18<n := by omega
      have he : n=(n-18)+18 := by omega
      rw [he,pow_period_eighteen]
      rw [ih (n-18) hm]
      have hemod : ((n-18)+18)%18=(n-18)%18 := by omega
      rw [hemod]

private theorem pow_two_mono (m n : Nat) (hmn : m≤n) :
    2^m≤2^n :=
  Nat.pow_le_pow_right (by decide : 0<(2:Nat)) hmn

private theorem four_mul_le_pow (n : Nat) :
    4≤n → 4*n≤2^n := by
  induction n with
  | zero => omega
  | succ n ih =>
    intro hn
    by_cases hs : n<4
    · interval_cases n <;> norm_num at *
    · have hp := ih (by omega)
      rw [Nat.pow_succ]
      nlinarith

private theorem reset_chain_last {s u : Nat}
    (hr : ResetChain s u) (hne : u≠s) :
    ∃h, ResetChain s h ∧ ResetParent h u := by
  cases hr with
  | root => exact False.elim (hne rfl)
  | append hc hp => exact ⟨_,hc,hp⟩

/-- The rho=38 phase of the t=0 candidate family is excluded from the
    genuine blank-root reset graph.  The hypotheses describe the dyadic
    source interval 97/64 <= (2K+7)/2^a <= 13/8. -/
theorem entry_not_root (a K : Nat)
    (ha18 : a%18=0)
    (hK54 : K%54=38)
    (hKlarge : 266≤K)
    (haK : a≤K)
    (hlo : 97*2^a≤64*(2*K+7))
    (hhi : 8*(2*K+7)≤13*2^a) :
    ¬ReachC (2,0) (entry a K,0) := by
  let p : Nat := 2^K
  let r : Nat := K+4-a
  let c : Nat := 2*K+7
  let B : Nat := c*2^r
  let N : Nat := B+2*K+1-16*p
  let D : Nat := N/3
  let E : Nat := 8*p+K-D
  let X : Nat := 2*E+5
  let d : Nat := X/3
  let h : Nat := 2*d-(4*p+K+4)

  have hEntry : entry a K=E := by
    simp [entry,p,r,c,B,N,D,E]

  have hK18 : K%18=2 := by omega
  have hK27 : K%27=11 := by omega
  have hK3 : K%3=2 := by omega
  have hK2 : K%2=0 := by omega
  have ha2 : a%2=0 := by omega
  have hra : r+a=K+4 := by
    dsimp [r]
    omega
  have hr18 : r%18=6 := by omega
  have hr2 : r%2=0 := by omega
  have hp3 : p%3=1 := by
    dsimp [p]
    exact pow_two_mod3_even K hK2
  have hrp3 : 2^r%3=1 := pow_two_mod3_even r hr2
  have hc3 : c%3=2 := by dsimp [c]; omega
  have hp27 : p%27=4 := by
    dsimp [p]
    rw [pow_mod_eighteen K,hK18]
    decide
  have hrp27 : 2^r%27=10 := by
    rw [pow_mod_eighteen r,hr18]
    decide
  have hc27 : c%27=2 := by dsimp [c]; omega

  have hpowK4 : 2^(K+4)=16*p := by
    dsimp [p]
    rw [Nat.pow_add]
    norm_num
  have hpowAr : 2^a*2^r=16*p := by
    calc
      2^a*2^r = 2^(a+r) := (Nat.pow_add 2 a r).symm
      _ = 2^(K+4) := by congr 1 <;> omega
      _ = 16*p := hpowK4

  have hBupper : 8*B≤208*p := by
    calc
      8*B = (8*c)*2^r := by dsimp [B]; ring
      _ ≤ (13*2^a)*2^r := Nat.mul_le_mul_right (2^r) hhi
      _ = 13*(2^a*2^r) := by ring
      _ = 13*(16*p) := by rw [hpowAr]
      _ = 208*p := by ring
  have hBupper' : B≤26*p := by omega
  have hBlower : 97*p≤4*B := by
    have hmul := Nat.mul_le_mul_right (2^r) hlo
    have hbig : 97*(16*p)≤64*B := by
      calc
        97*(16*p) = 97*(2^a*2^r) := by rw [hpowAr]
        _ = (97*2^a)*2^r := by ring
        _ ≤ (64*c)*2^r := hmul
        _ = 64*B := by dsimp [B]; ring
    omega
  have h16pB : 16*p≤B := by omega
  have hNadd : N+16*p=B+2*K+1 := by
    dsimp [N]
    exact Nat.sub_add_cancel h16pB
  have hB3 : B%3=2 := by
    dsimp [B]
    rw [Nat.mul_mod,hc3,hrp3]
    norm_num
  have h2K3 : (2*K)%3=1 := by
    rw [Nat.mul_mod,hK3]
    norm_num
  have hA3 : (B+2*K+1)%3=1 := by
    rw [Nat.add_mod,Nat.add_mod,hB3,h2K3]
    norm_num
  have h16p3 : (16*p)%3=1 := by
    rw [Nat.mul_mod,hp3]
    norm_num
  have hNmodEq := congrArg (fun z : Nat => z%3) hNadd
  rw [Nat.add_mod,h16p3,hA3] at hNmodEq
  have hNmod : N%3=0 := by omega
  have hDmul : 3*D=N := by
    dsimp [D]
    have hdv := Nat.mod_add_div N 3
    omega
  have hNupper : N≤24*p+3*K := by
    have hNupper' : N+16*p≤26*p+2*K+1 := by omega
    omega
  have hDle : D≤8*p+K := by omega
  have hEadd : E+D=8*p+K := by
    dsimp [E]
    exact Nat.sub_add_cancel hDle
  have hDplus : 3*D+16*p=B+2*K+1 := by omega
  have hDdouble : 6*D+32*p=2*B+4*K+2 := by omega
  have h3Xeq : 3*X+2*B=80*p+2*K+13 := by
    dsimp [X,E]
    omega

  have hB27 : B%27=20 := by
    dsimp [B]
    rw [Nat.mul_mod,hc27,hrp27]
    norm_num
  have h2B27 : (2*B)%27=13 := by
    rw [Nat.mul_mod,hB27]
    norm_num
  have h80p27 : (80*p)%27=23 := by
    rw [Nat.mul_mod,hp27]
    norm_num
  have h2K27 : (2*K)%27=22 := by
    rw [Nat.mul_mod,hK27]
    norm_num
  have hT27 : (80*p+2*K+13)%27=4 := by
    rw [Nat.add_mod,Nat.add_mod,h80p27,h2K27]
    norm_num
  have h3XmodEq := congrArg (fun z : Nat => z%27) h3Xeq
  rw [Nat.add_mod,h2B27,hT27] at h3XmodEq
  have h3Xmod : (3*X)%27=18 := by omega
  have h3Xrepr : 3*X=27*(X/9)+3*(X%9) := by
    have hxdiv := Nat.mod_add_div X 9
    omega
  have h3Xmod' : (3*X)%27=3*(X%9) := by
    have hxlt := Nat.mod_lt X (by decide : 0<9)
    rw [h3Xrepr]
    omega
  have hXmod9 : X%9=6 := by omega
  have hXmod3 : X%3=0 := by
    have hxdiv := Nat.mod_add_div X 9
    omega
  have hXeq : X=3*d := by
    have hxdiv := Nat.mod_add_div X 3
    dsimp [d]
    omega
  have hdrepr : X=9*(d/3)+3*(d%3) := by
    have hddiv := Nat.mod_add_div d 3
    omega
  have hdmod3 : d%3=2 := by
    have hdlt := Nat.mod_lt d (by decide : 0<3)
    have hxmod := hXmod9
    rw [hdrepr] at hxmod
    omega
  have hXodd : X%2=1 := by dsimp [X]; omega
  have hdodd : d%2=1 := by
    have hmul : (3*d)%2=d%2 := by
      rw [Nat.mul_mod]
      norm_num
    rw [hXeq] at hXodd
    omega
  have h9d : 9*d+2*B=80*p+2*K+13 := by
    calc
      9*d+2*B = 3*X+2*B := by rw [hXeq]; ring
      _ = 80*p+2*K+13 := h3Xeq
  have hdlo : 3*p<d := by omega
  have h18d : 18*d+4*B=160*p+4*K+26 := by omega
  have hp4 : 4*K≤p := by
    dsimp [p]
    exact four_mul_le_pow K (by omega)
  have hdhi : d<4*p := by omega

  have hpK1 : 2^K=2*2^(K-1) := by
    have he : K=(K-1)+1 := by omega
    rw [he,Nat.pow_succ]
    omega
  have hpK2 : 2^K=4*2^(K-2) := by
    have he : K=(K-2)+2 := by omega
    rw [he,Nat.pow_add]
    norm_num
  have hscaleK1 : 6*2^(K-1)=3*p := by
    dsimp [p]
    rw [←hpK1]
    ring
  have hscaleK2 : 8*2^(K-2)=2*p := by
    dsimp [p]
    rw [←hpK2]
    ring

  have hElo : 4*p<E := by omega
  have hEhi : E<6*p-1 := by omega
  have hNoEvenE : ∀q, (∃k, (6*2^k-1≤E ∧ E≤8*2^k-3) ∧
      2*E=8*2^k+q+k) → False := by
    intro q hp
    rcases hp with ⟨k,hband,heq⟩
    by_cases hk : k<K
    · have hpow := pow_two_mono k (K-1) (by omega)
      have hscale : 8*2^k≤4*p := by
        have hs : 8*2^(K-1)=4*p := by
          dsimp [p]
          rw [←hpK1]
          ring
        omega
      have htop : E≤4*p-3 := by omega
      omega
    · have hpow := pow_two_mono K k (by omega)
      have hlow : 6*p-1≤6*2^k-1 := by dsimp [p]; omega
      omega

  have hsub : 4*p+K+4≤2*d := by
    have h6 : 6*p<2*d := by omega
    omega
  have hAdd : h+4*p+K+4=2*d := by
    dsimp [h]
    exact Nat.sub_add_cancel hsub
  have h18dlo : 56*p+4*K+26≤18*d := by omega
  have hpGap : 5*K+10<2*p := by omega
  have h18dneed : 54*p+9*K+36<18*d := by omega
  have hhlo : 2*p<h := by omega
  have h18dhi : 18*d≤63*p+4*K+26 := by omega
  have h18dneedHi : 18*d<63*p+9*K+27 := by omega
  have hhhi : h<3*p-1 := by omega
  have hmodEq := congrArg (fun z : Nat => z%3) hAdd
  simp only [Nat.add_mod,Nat.mul_mod] at hmodEq
  rw [hp3,hK3,hdmod3] at hmodEq
  norm_num at hmodEq
  have hmodh : h%3=0 := by omega

  have hNoParentH : ∀q, ¬ResetParent q h := by
    intro q hp
    rcases hp with ⟨k,hband,heq⟩ | ⟨k,t,d',hd',hband,hout,heq⟩
    · by_cases hk : k<K-1
      · have hpow := pow_two_mono k (K-2) (by omega)
        have hscale : 8*2^k≤2*p := by omega [hscaleK2]
        have htop : 8*2^k-3≤2*p-3 := by omega
        omega
      · have hpow := pow_two_mono (K-1) k (by omega)
        have hlow : 3*p-1≤6*2^k-1 := by omega [hscaleK1]
        omega
    · have hdiv : 3∣2*h+5 := by
        refine ⟨3^t*d', ?_⟩
        calc
          2*h+5 = 3^(t+1)*d' := hout
          _ = 3*(3^t*d') := by rw [Nat.pow_succ]; ring
      have hmodout : (2*h+5)%3=2 := by omega
      have hmodzero := Nat.mod_eq_zero_of_dvd hdiv
      omega

  have hParentUnique : ∀q, ResetParent q E → q=h := by
    intro q hp
    rcases hp with heven | hodd
    · exact False.elim (hNoEvenE q heven)
    · rcases hodd with ⟨k,t,d',hd',hband,hout,heq⟩
      have ht : t=0 := by
        by_contra htn
        have htpos : 1≤t := by omega
        have hpow : 3^(t+1)=9*3^(t-1) := by
          have he : t+1=(t-1)+2 := by omega
          rw [he,Nat.pow_add]
          norm_num [Nat.mul_comm]
        have hdiv9 : 9∣X := by
          refine ⟨3^(t-1)*d', ?_⟩
          have houtX : X=3^(t+1)*d' := by simpa [X] using hout
          calc
            X = 3^(t+1)*d' := houtX
            _ = 9*(3^(t-1)*d') := by rw [hpow]; ring
        have hmod9zero := Nat.mod_eq_zero_of_dvd hdiv9
        omega
      subst t
      have houtX : X=3*d' := by simpa [X] using hout
      have hdEq : d'=d := by
        have hmul : 3*d'=3*d := by
          calc
            3*d' = X := houtX.symm
            _ = 3*d := hXeq
        exact Nat.mul_left_cancel hmul
      subst d'
      have hkEq : k=K-1 := by
        by_cases hkl : k<K-1
        · have hpow := pow_two_mono k (K-2) (by omega)
          have hscale : 8*2^k≤2*p := by omega [hscaleK2]
          have htop : d≤2*p-1 := by omega
          omega
        · by_cases hku : K-1<k
          · have hpow := pow_two_mono K k (by omega)
            have hscale : 6*p≤6*2^k := by dsimp [p]; omega
            have hlow : 6*p+1≤6*2^k+1 := by omega
            omega
          · omega
      subst k
      have hscale : 8*2^(K-1)=4*p := by
        dsimp [p]
        rw [←hpK1]
        ring
      have heq'' : 2*d=4*p+q+(K-1)+5 := by
        simpa only [Nat.pow_zero, one_mul] using heq
      rw [hscale] at heq''
      omega [hAdd]

  have hEne : E≠2 := by omega
  have hHne : h≠2 := by omega
  rw [hEntry]
  change ¬ReachC (2,0) (E,0)
  intro hr
  have hc : ResetChain 2 E := (root_reset_chain_iff E).mp hr
  obtain ⟨q,hprefix,hparent⟩ := reset_chain_last hc hEne
  have hq : q=h := hParentUnique q hparent
  subst q
  obtain ⟨q',_,hp'⟩ := reset_chain_last hprefix hHne
  exact hNoParentH q' hp'

#print axioms entry_not_root

end CascadeT0Rho38
