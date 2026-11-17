import CancellationMidBand
import Lean.Elab.Tactic.Omega

namespace BB6.Agent46.CancellationMidBandResidue

open CancellationMidBand CancellationNat CancellationGap CancellationStrip

def cutIndex (a s : Nat) : Nat := (a+s-1)/s

def cutRemainder (a s : Nat) : Nat := a+s-cutIndex a s*s

theorem geomSum_add (t m n : Nat) :
    geomSum t (m+n) = geomSum t m + t^m*geomSum t n := by
  induction n with
  | zero =>
      simp [geomSum]
  | succ n ih =>
      calc
        geomSum t (m+(n+1)) = geomSum t ((m+n)+1) := by congr 1; omega
        _ = geomSum t (m+n)+t^(m+n) := by rw [geomSum]
        _ = (geomSum t m+t^m*geomSum t n)+t^m*t^n := by
          rw [ih, Nat.pow_add]
        _ = geomSum t m+t^m*(geomSum t n+t^n) := by
          rw [Nat.mul_add]
          omega
        _ = geomSum t m+t^m*geomSum t (n+1) := by rw [geomSum]

theorem geomSum_weighted_lt_general (n t L : Nat)
    (ht : 2 ≤ t) (hn : n+2 ≤ t) :
    n*geomSum t (L+1) < (n+1)*t^L := by
  let G := geomSum t L
  let T := t^L
  have hsplit : geomSum t (L+1)=G+T := by
    simp [G,T,geomSum]
  have hgeom := geomSum_mul t L (by omega)
  have hgeom' : G*(t-1)+1=T := by
    simpa [G,T] using hgeom
  have hgeom'' : (t-1)*G+1=T := by
    simpa [Nat.mul_comm] using hgeom'
  have hnle : n≤t-1 := by omega
  have hprod : n*G≤(t-1)*G := Nat.mul_le_mul_right G hnle
  have hsmall : n*G<T := lt_of_le_of_lt hprod (by omega)
  calc
    n*geomSum t (L+1) = n*(G+T) := by rw [hsplit]
    _ = n*G+n*T := by rw [Nat.mul_add]
    _ < T+n*T := Nat.add_lt_add_right hsmall (n*T)
    _ = (n+1)*T := by rw [Nat.add_mul]; simp [Nat.mul_comm]
    _ = (n+1)*t^L := by rfl

theorem small_factor_bound (r s : Nat) (hr : 2 ≤ r)
    (hs : cancellation_threshold r ≤ s)
    (hupper : r*s ≤ valuationA r) :
    9^r+2*s < 4*2^s := by
  have hgap := log2_gap_five r hr
  have hpow : 3^(2*r-1)+5 ≤ 2^s := by
    have hpow' := pow2_mono (cancellation_threshold r) s hs
    simpa [cancellation_threshold] using Nat.le_trans hgap hpow'
  by_cases hr2 : r=2
  · subst r
    have ha : valuationA 2=43 := by norm_num [valuationA]
    have hsBound : s≤21 := by
      rw [ha] at hupper
      omega
    have hpow32 : 32≤2^s := by norm_num at hpow ⊢; exact hpow
    have hleft : 9^2+2*s≤123 := by norm_num; omega
    have hright : 128≤4*2^s := by omega
    norm_num
    omega
  · have hr3 : 3≤r := by omega
    have hmul' : 2*(r*s)≤9^r+5 := by
      calc
        2*(r*s) ≤ 2*valuationA r := Nat.mul_le_mul_left 2 hupper
        _ = 9^r+5 := valuationA_double r
    have hmul : 2*r*s≤9^r+5 := by
      simpa [Nat.mul_assoc] using hmul'
    have h6 : 6*s≤2*r*s :=
      Nat.mul_le_mul_right s (by omega : 6≤2*r)
    have hpow3 : 9^r=3*3^(2*r-1) := by
      rw [show (9:Nat)=3^2 by decide, Nat.pow_mul]
      rw [show 2*r=(2*r-1)+1 by omega, Nat.pow_succ]
    have h2s : 2*s≤3^(2*r-1)+2 := by
      rw [hpow3] at hmul
      omega
    have hleft : 9^r+2*s≤4*3^(2*r-1)+2 := by
      rw [hpow3]
      omega
    have hright : 4*3^(2*r-1)+20≤4*2^s :=
      Nat.mul_le_mul_left 4 hpow
    omega

/-- A residue-dependent extension of the all-r cancellation-feeder parent band. -/
theorem midband_no_parent_remainder (r s : Nat) (hr : 2 ≤ r)
    (hs : cancellation_threshold r ≤ s)
    (hcase : valuationA r ≤ (2*r-1)*s)
    (hupper : r*s ≤ valuationA r)
    (hrem : cancellation_threshold r ≤ cutRemainder (valuationA r) s) :
    ¬ (2^(valuationA r+s)+3) ∣
      (2^(valuationA r)*P (2^(valuationA r)) r+3-
        2*(valuationA r-1+s)) := by
  let a := valuationA r
  let A := 2^a
  let t := 2^s
  let T := t^(2*r)
  let S := geomSum t (2*r)
  let n := 3^(2*r-1)
  let u := a-1+s
  let B := 2^(a+s)
  let D := B+3
  let N := A*P A r+3-2*u
  let Y := 3^(2*r)*S
  let U := (2*u-3)*T
  let Q := U-Y
  let R := n*S
  have haLin : 4*r+3≤a := by dsimp [a]; exact valuationA_linear r
  have ha4 : 4≤a := by omega
  have hsLeA : s≤a := by
    have hmul : s≤r*s := Nat.mul_le_mul_right s (by omega : 1≤r)
    dsimp [a] at hupper ⊢
    omega
  have hA8 : 8≤A := by
    dsimp [A]
    have hp := pow2_mono 3 a (by omega)
    norm_num at hp ⊢
    exact hp
  have ht2 : 2≤t := by
    dsimp [t]
    have hp := pow2_mono 1 s (by omega)
    norm_num at hp ⊢
    exact hp
  have ht1 : 1≤t := by omega
  have hfourA : 4*a≤2^a := four_mul_le_pow a ha4
  have h2uBound : 2*u≤4*a := by
    dsimp [u]
    omega
  have hPpos : 0<P A r := P_pos A r (by dsimp [A]; omega) (by omega)
  have hAP : A≤A*P A r := Nat.le_mul_of_pos_right A hPpos
  have hNoTrunc : 2*u≤A*P A r+3 := by
    dsimp [A] at hAP ⊢
    omega
  have h2uEq : 2*u-3=9^r+2*s := by
    dsimp [u,a]
    have hd := valuationA_double r
    omega
  have hTpow : T=2^(2*r*s) := by
    dsimp [T,t]
    rw [← Nat.pow_mul]
    congr 1
    simp [Nat.mul_comm, Nat.mul_left_comm]
  have hBpow : A*t=B := by
    dsimp [A,t,B]
    rw [Nat.pow_add]
  have hSpos : 0<S := by
    dsimp [S]
    exact geomSum_pos t (2*r) (by omega)
  have hSltT : S<T := by
    have hgeom := geomSum_mul t (2*r) ht1
    have hmul0 : geomSum t (2*r)*1≤geomSum t (2*r)*(t-1) :=
      Nat.mul_le_mul_left (geomSum t (2*r)) (by omega)
    have hmul : geomSum t (2*r)≤geomSum t (2*r)*(t-1) := by simpa using hmul0
    dsimp [S,T]
    omega
  have hYpos : 0<Y := by
    dsimp [Y]
    exact Nat.mul_pos (Nat.pow_pos (by decide : 0<3)) hSpos
  have h9pow : 3^(2*r)=9^r := by
    rw [show (9:Nat)=3^2 by decide, Nat.pow_mul]
  have hYltU : Y<U := by
    dsimp [Y,U]
    rw [h9pow,h2uEq]
    have h9pos : 0<9^r := Nat.pow_pos (by decide : 0<9)
    have hlt : 9^r*S<9^r*T := Nat.mul_lt_mul_of_pos_left hSltT h9pos
    have hle : 9^r*T≤(9^r+2*s)*T :=
      Nat.mul_le_mul_right T (by omega)
    exact Nat.lt_of_lt_of_le hlt hle
  have hQpos : 0<Q := by dsimp [Q]; omega
  have hYleU : Y≤U := by omega
  have hQplusY : Q+Y=U := by dsimp [Q]; exact Nat.sub_add_cancel hYleU
  have hcert := cert_identity A t r (by omega) ht2
  have hcert' : T*A*P A r=Y+D*(certC A t r) := by
    dsimp [T,Y,D,S,A,t,B] at hcert ⊢
    rw [← Nat.pow_add] at hcert
    exact hcert
  have hNplus : N+2*u=A*P A r+3 := by
    dsimp [N]
    exact Nat.sub_add_cancel hNoTrunc
  have hNred : N+(2*u-3)=A*P A r := by omega
  have hMul : T*N+U=Y+D*(certC A t r) := by
    calc
      T*N+U=T*N+T*(2*u-3) := by dsimp [U]; simp [Nat.mul_comm]
      _=T*(N+(2*u-3)) := by rw [← Nat.mul_add]
      _=T*(A*P A r) := by rw [hNred]
      _=T*A*P A r := by rw [Nat.mul_assoc]
      _=Y+D*(certC A t r) := hcert'
  have hEq : T*N+Q=D*(certC A t r) := by
    have hMul' := hMul
    rw [← hQplusY] at hMul'
    omega
  intro hDvd
  have hDpos : 0<D := by dsimp [D,B]; omega
  have hDdivQ : D∣Q := by
    have hTN : D∣T*N := Nat.dvd_mul_left_of_dvd hDvd T
    have hDC : D∣D*(certC A t r) := ⟨certC A t r,rfl⟩
    have hdiff := Nat.dvd_sub hDC hTN
    rw [← hEq,Nat.add_sub_cancel_left] at hdiff
    exact hdiff
  let z := Q/D
  have hz : D*z=Q := by
    have hdiv := Nat.div_mul_cancel hDdivQ
    dsimp [z]
    simpa [Nat.mul_comm] using hdiv
  have hUeq : U=D*z+Y := by
    calc
      U=Q+Y := hQplusY.symm
      _=D*z+Y := by rw [hz]
  let M := 2^(a+s)
  have hMpow : M=2^(a+s) := rfl
  have hExpM : a+s≤2*r*s := by
    have hcoeff : 2*r=(2*r-1)+1 := by omega
    have hmul : 2*r*s=(2*r-1)*s+s := by
      rw [hcoeff,Nat.add_mul]
      simp
    omega
  have hMdivT : M∣T := by
    dsimp [M]
    rw [hTpow]
    refine ⟨2^(2*r*s-(a+s)), ?_⟩
    rw [← Nat.pow_add]
    congr 1
    omega
  have hMB : M∣B := by dsimp [M,B]; exact ⟨1,by simp⟩
  have hModular : M∣z+R := by
    have hMU : M∣U := by
      dsimp [U]
      exact Nat.dvd_mul_left_of_dvd hMdivT (2*u-3)
    have hMsum : M∣D*z+Y := by rw [← hUeq]; exact hMU
    have hMBz : M∣B*z := Nat.dvd_mul_right_of_dvd hMB z
    have hSplit : D*z+Y=B*z+(3*z+Y) := by
      dsimp [D]
      rw [Nat.add_mul]
      omega
    have hM3zY : M∣3*z+Y := by
      rw [hSplit] at hMsum
      exact (Nat.dvd_add_right hMBz).mp hMsum
    have hpow3 : 3^(2*r)=3^(2*r-1)*3 := by
      calc
        3^(2*r)=3^((2*r-1)+1) := congrArg (fun e=>3^e) (by omega)
        _=3^(2*r-1)*3 := by rw [Nat.pow_succ]
    have hY : Y=3*R := by
      dsimp [Y,R,n,S]
      rw [hpow3]
      simp [Nat.mul_comm,Nat.mul_left_comm]
    have hM3 : M∣3*(z+R) := by
      have hsum : 3*z+3*R=3*(z+R) := by simp [Nat.mul_add]
      rw [hY,hsum] at hM3zY
      exact hM3zY
    have hpowdiv : 2^(a+s)∣3*(z+R) := by simpa [hMpow] using hM3
    simpa using pow_two_dvd_three_mul hpowdiv
  let L := cutIndex a s
  let c := cutRemainder a s
  let Rlow := n*geomSum t (L+1)
  have hsPos : 0<s := by
    have h := hs
    dsimp [cancellation_threshold] at h
    omega
  have hLprod : L*s≤a+s-1 := by
    dsimp [L,cutIndex]
    simpa [Nat.mul_comm] using Nat.div_mul_le_self (a+s-1) s
  have hmod : (a+s-1)%s+L*s=a+s-1 := by
    dsimp [L,cutIndex]
    simpa [Nat.mul_comm] using Nat.mod_add_div (a+s-1) s
  have hremLt : (a+s-1)%s<s := Nat.mod_lt _ hsPos
  have hcEq : c=(a+s-1)%s+1 := by
    dsimp [c,cutRemainder,L,cutIndex]
    omega
  have hcPos : 1≤c := by rw [hcEq]; omega
  have hcLeS : c≤s := by rw [hcEq]; omega
  have hcut : L*s+c=a+s := by
    dsimp [c,cutRemainder]
    omega
  have hLlt : L<2*r := by
    by_contra hnot
    have hle : 2*r≤L := by omega
    have hmul := Nat.mul_le_mul_right s hle
    have hcoeff : 2*r=(2*r-1)+1 := by omega
    have hmulEq : 2*r*s=(2*r-1)*s+s := by
      rw [hcoeff,Nat.add_mul]
      simp
    omega
  have hLlen : L+1≤2*r := by omega
  have hsumLen : (L+1)+(2*r-(L+1))=2*r := Nat.add_sub_of_le hLlen
  have hTail : S=geomSum t (L+1)+t^(L+1)*geomSum t (2*r-(L+1)) := by
    dsimp [S]
    have h := geomSum_add t (L+1) (2*r-(L+1))
    rw [hsumLen] at h
    exact h
  have htpow : t^(L+1)=2^((L+1)*s) := by
    dsimp [t]
    rw [← Nat.pow_mul]
    congr 1
    simp [Nat.mul_comm]
  have hExpTail : a+s≤(L+1)*s := by
    have hmul : (L+1)*s=L*s+s := by rw [Nat.add_mul]; simp
    omega
  have hMdivPow : M∣t^(L+1) := by
    dsimp [M]
    rw [htpow]
    refine ⟨2^((L+1)*s-(a+s)), ?_⟩
    rw [← Nat.pow_add]
    congr 1
    omega
  have hMdivTail : M∣n*(t^(L+1)*geomSum t (2*r-(L+1))) := by
    have h1 : M∣t^(L+1)*geomSum t (2*r-(L+1)) :=
      Nat.dvd_mul_left_of_dvd hMdivPow _
    exact Nat.dvd_mul_right_of_dvd h1 n
  have hRdecomp : R=Rlow+n*(t^(L+1)*geomSum t (2*r-(L+1))) := by
    dsimp [Rlow,R]
    rw [hTail,Nat.mul_add]
  have hsumZR : z+R=(z+Rlow)+n*(t^(L+1)*geomSum t (2*r-(L+1))) := by
    rw [hRdecomp]
    omega
  have hMlow : M∣z+Rlow := by
    have hsub := Nat.dvd_sub hModular hMdivTail
    have hEqSub : (z+R)-n*(t^(L+1)*geomSum t (2*r-(L+1)))=z+Rlow := by
      omega
    simpa [hEqSub] using hsub
  have hn5 : n+5≤t := by
    dsimp [n,t]
    have hgap := log2_gap_five r hr
    have hpow := pow2_mono (cancellation_threshold r) s hs
    exact Nat.le_trans (by simpa [cancellation_threshold] using hgap) hpow
  have hn2 : n+2≤t := by omega
  have hgapC : n+5≤2^c := by
    have hgap := log2_gap_five r hr
    have hpow := pow2_mono (cancellation_threshold r) c hrem
    exact Nat.le_trans (by simpa [cancellation_threshold] using hgap) hpow
  have hRlowBound : Rlow<(2^c-4)*t^L := by
    dsimp [Rlow]
    have hweighted := geomSum_weighted_lt_general n t L ht2 hn2
    have hcoef : n+1≤2^c-4 := by omega
    exact lt_of_lt_of_le hweighted (Nat.mul_le_mul_right (t^L) hcoef)
  let E := 2*a-(2*r-2)*s-c
  have hEge : s≤E := by
    have hcs : c+s≤2*s := by omega
    have hcoeff : (2*r-2)+2=2*r := by omega
    have hmul : (2*r-2)*s+2*s=2*r*s := by
      rw [← Nat.add_mul]
      rw [hcoeff]
    have h2a : 2*r*s≤2*a := by
      have h := Nat.mul_le_mul_left 2 hupper
      simpa [Nat.mul_assoc] using h
    dsimp [E]
    omega
  have hsmall := small_factor_bound r s hr hs hupper
  have hsmall' : 2*u-3<4*2^E := by
    rw [h2uEq]
    have hpow := Nat.mul_le_mul_left 4 (pow2_mono s E hEge)
    omega
  have hpowIdentity : 2^E*2^(2*r*s)=2^(a+s)*2^(L*s) := by
    have hcoeff : (2*r-2)+2=2*r := by omega
    have hmul : (2*r-2)*s+2*s=2*r*s := by
      rw [← Nat.add_mul]
      rw [hcoeff]
    have hEeq : E+2*r*s=a+s+L*s := by
      dsimp [E]
      rw [hcut]
      omega
    rw [← Nat.pow_add,← Nat.pow_add]
    exact congrArg (fun e=>2^e) hEeq
  have hLpow : t^L=2^(L*s) := by
    dsimp [t]
    rw [← Nat.pow_mul]
    congr 1
    simp [Nat.mul_comm]
  have hUbound : U<M*(4*t^L) := by
    dsimp [U]
    rw [hTpow]
    have hprod : (2*u-3)*2^(2*r*s)<(4*2^E)*2^(2*r*s) :=
      Nat.mul_lt_mul_of_pos_right hsmall' (Nat.pow_pos (by decide : 0<2))
    have hEq : (4*2^E)*2^(2*r*s)=M*(4*t^L) := by
      calc
        (4*2^E)*2^(2*r*s)=4*(2^E*2^(2*r*s)) := by simp [Nat.mul_assoc]
        _=4*(2^(a+s)*2^(L*s)) := by rw [hpowIdentity]
        _=2^(a+s)*(4*2^(L*s)) := by simp [Nat.mul_assoc,Nat.mul_comm,Nat.mul_left_comm]
        _=M*(4*t^L) := by rw [hMpow,hLpow]
    rw [hEq] at hprod
    exact hprod
  have hQbound : Q<M*(4*t^L) := by
    have hQlt : Q<U := by dsimp [Q]; omega
    exact Nat.lt_trans hQlt hUbound
  have hzbound : z<4*t^L := by
    have hmul : D*z<D*(4*t^L) := by rw [hz]; exact hQbound
    exact Nat.lt_of_mul_lt_mul_left hmul
  have h2c : 4≤2^c := by omega
  have hsub : 2^c-4+4=2^c := Nat.sub_add_cancel h2c
  have hsumBound : 4*t^L+(2^c-4)*t^L=2^c*t^L := by
    rw [← Nat.add_mul]
    rw [hsub]
  have hMfact : M=2^c*t^L := by
    dsimp [M]
    rw [← hcut,Nat.pow_add,hLpow]
    simp [Nat.mul_comm]
  have hltM : z+Rlow<M := by
    have hsum : z+Rlow<4*t^L+(2^c-4)*t^L :=
      Nat.add_lt_add hzbound hRlowBound
    rw [hsumBound,hMfact] at hsum
    exact hsum
  have hzpos : 0<z := by
    by_contra h
    have hz0 : z=0 := by omega
    rw [hz0] at hz
    omega
  have hpos : 0<z+Rlow := Nat.add_pos_left hzpos _
  exact (Nat.not_dvd_of_pos_of_lt hpos hltM) hMlow

#print axioms geomSum_weighted_lt_general
#print axioms small_factor_bound
#print axioms midband_no_parent_remainder

end BB6.Agent46.CancellationMidBandResidue
