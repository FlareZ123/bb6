import FiveLayerGap
import ThreeLayerPeel

namespace BB6.Agent43FiveLayer

open BB6.Agent43ThreeLayer

set_option maxRecDepth 4096
set_option maxHeartbeats 5000000

/-- Five shallow transitions, with arbitrary intervening depth-two runs,
cannot satisfy the exact shifted-wall scalar equation once n>=83. -/
private theorem twice_quotient_le (t d R : Nat) (ht : 1≤t)
    (hR : R=2^t*d) : 2*d≤R := by
  have hpow : 2≤2^t := by
    cases t with
    | zero => omega
    | succ k =>
      have hpowPos : 1≤2^k := Nat.one_le_pow k 2 (by decide)
      have hmul : 2≤2^k*2 := by
        simpa using Nat.mul_le_mul_right 2 hpowPos
      simpa [Nat.pow_succ] using hmul
  calc
    2*d≤2^t*d := Nat.mul_le_mul_right d hpow
    _=R := hR.symm

theorem five_layer_abstract_barrier
  (n s u v w x r alpha beta gamma delta epsilon q p a b c f g
   K R1 R2 R3 R4 R5 E : Nat)
  (hn : 83≤n)
  (hqp : q*p=2^n)
  (hqd : ∃ d, q*d=14*n+92)
  (hq : q=8^s) (hExp : p=2^(n-3*s))
  (ha : a=2^alpha) (hb : b=2^beta)
  (hc : c=2^gamma) (hf : f=2^delta) (hg : g=2^epsilon)
  (halpha : 1≤alpha) (hbeta : 1≤beta) (hgamma : 1≤gamma)
  (hdelta : 1≤delta) (hepsilon : 1≤epsilon)
  (hK : 392*(q*((a*8^u)*((b*8^v)*((c*8^w)*(f*8^x)))))≤K)
  (hR1 : 0<R1) (hR1bound : R1≤168*(n+2))
  (hR2 : 0<R2)
  (hR2bound : alpha+3*u≤n-3*s → R2≤168*(n+2))
  (hR3 : 0<R3)
  (hR3bound : alpha+3*u+beta+3*v≤n-3*s → R3≤168*(n+2))
  (hR4 : 0<R4)
  (hR4bound : alpha+3*u+beta+3*v+gamma+3*w≤n-3*s → R4≤168*(n+2))
  (hR5 : 0<R5)
  (hR5bound : alpha+3*u+beta+3*v+gamma+3*w+delta+3*x≤n-3*s →
    R5≤168*(n+2))
  (hEbound : alpha+3*u+beta+3*v+gamma+3*w+delta+3*x+epsilon+3*r≤n-3*s →
    E+1≤224*(n+2))
  (heq : K*p =
    (a*8^u)*((b*8^v)*((c*8^w)*((f*8^x)*((g*8^r)*E+R5)+R4)+R3)+R2)+R1) : False := by
  let X : Nat := n+2
  let A1 : Nat := a*8^u
  let A2 : Nat := b*8^v
  let A3 : Nat := c*8^w
  let A4 : Nat := f*8^x
  let A5 : Nat := g*8^r
  let e : Nat := n-3*s
  let t1 : Nat := alpha+3*u
  let t2 : Nat := beta+3*v
  let t3 : Nat := gamma+3*w
  let t4 : Nat := delta+3*x
  let t5 : Nat := epsilon+3*r
  have hX : 1≤X := by dsimp [X]; omega
  have hx23 : X^2≤X^3 := by
    calc
      X^2 = X^2*1 := by omega
      _ ≤ X^2*X := Nat.mul_le_mul_left _ hX
      _ = X^3 := (Nat.pow_succ X 2).symm
  have hx34 : X^3≤X^4 := by
    calc
      X^3 = X^3*1 := by omega
      _ ≤ X^3*X := Nat.mul_le_mul_left _ hX
      _ = X^4 := (Nat.pow_succ X 3).symm
  have hx45 : X^4≤X^5 := by
    calc
      X^4 = X^4*1 := by omega
      _ ≤ X^4*X := Nat.mul_le_mul_left _ hX
      _ = X^5 := (Nat.pow_succ X 4).symm
  have hx56 : X^5≤X^6 := by
    calc
      X^5 = X^5*1 := by omega
      _ ≤ X^5*X := Nat.mul_le_mul_left _ hX
      _ = X^6 := (Nat.pow_succ X 5).symm
  have hGapX : 19172403734400*X^6<2^n := by
    simpa [X] using sixth_gap_83 n hn
  have hA1 : A1=2^t1 := by
    dsimp [A1,t1]
    rw [ha,show (8:Nat)=2^3 by decide,←Nat.pow_mul,Nat.pow_add]
  have hA2 : A2=2^t2 := by
    dsimp [A2,t2]
    rw [hb,show (8:Nat)=2^3 by decide,←Nat.pow_mul,Nat.pow_add]
  have hA3 : A3=2^t3 := by
    dsimp [A3,t3]
    rw [hc,show (8:Nat)=2^3 by decide,←Nat.pow_mul,Nat.pow_add]
  have hA4 : A4=2^t4 := by
    dsimp [A4,t4]
    rw [hf,show (8:Nat)=2^3 by decide,←Nat.pow_mul,Nat.pow_add]
  have hA5 : A5=2^t5 := by
    dsimp [A5,t5]
    rw [hg,show (8:Nat)=2^3 by decide,←Nat.pow_mul,Nat.pow_add]
  have hqpos : 0<q := by rw [hq]; exact Nat.pow_pos (by decide)
  obtain ⟨d,hd⟩ := hqd
  have hdpos : 0<d := by
    by_cases hz : d=0
    · rw [hz] at hd
      simp at hd
    · omega
  have hd1 : 1≤d := by omega
  have hqle : q≤15*X := by
    have hle : q≤q*d := by
      have hh := Nat.mul_le_mul_left q hd1
      simpa using hh
    dsimp [X]
    omega
  have hR1prod : q*R1≤2520*X^2 := by
    calc
      q*R1≤(15*X)*(168*X) := Nat.mul_le_mul hqle hR1bound
      _ = 2520*X^2 := by
        rw [show (2520:Nat)=15*168 by decide]
        simp only [Nat.pow_succ,Nat.pow_zero]
        ac_rfl
  have hR1smallProd : q*R1<2^n := by
    have hsmall : 2520*X^2≤19172403734400*X^6 := by
      calc
        2520*X^2≤2520*X^3 := Nat.mul_le_mul_left 2520 hx23
        _≤2520*X^4 := Nat.mul_le_mul_left 2520 hx34
        _≤2520*X^5 := Nat.mul_le_mul_left 2520 hx45
        _≤2520*X^6 := Nat.mul_le_mul_left 2520 hx56
        _≤19172403734400*X^6 :=
          Nat.mul_le_mul_right _ (by decide : 2520≤19172403734400)
    exact Nat.lt_of_le_of_lt (Nat.le_trans hR1prod hsmall) hGapX
  have hR1small : R1<2^e := by
    have hh : q*R1<q*p := by rw [hqp]; exact hR1smallProd
    have hp : R1<p := Nat.lt_of_mul_lt_mul_left hh
    simpa only [hExp,e] using hp
  have hEq1 : K*2^e =
      (A2*(A3*(A4*(A5*E+R5)+R4)+R3)+R2)*2^t1+R1 := by
    rw [←hExp,←hA1]
    simpa only [A1,A2,A3,A4,A5,Nat.mul_comm,Nat.mul_assoc,Nat.mul_left_comm] using heq
  obtain ⟨d1,ht1le,hR1eq,hEq2,hd1le,hA1le⟩ :=
    residue_peel e t1 K (A2*(A3*(A4*(A5*E+R5)+R4)+R3)+R2) R1 hR1 hR1small hEq1
  have ht1pos : 1≤t1 := by dsimp [t1]; omega
  have hhalf1 : 2*d1≤R1 := twice_quotient_le t1 d1 R1 ht1pos hR1eq
  have hA1Bound : A1≤168*X := by
    rw [hA1]
    exact Nat.le_trans hA1le hR1bound
  have hR2small : R2≤168*X := hR2bound (by simpa only [t1,e] using ht1le)
  have hRem2Pos : 0<R2+d1 := by omega
  have hRem2Bound : R2+d1≤252*X := by
    have hd1Bound : d1≤84*X := by
      have hdouble : 2*d1≤168*X := Nat.le_trans hhalf1 hR1bound
      omega
    omega
  have hqA1Bound : q*A1≤2520*X^2 := by
    calc
      q*A1≤(15*X)*(168*X) := Nat.mul_le_mul hqle hA1Bound
      _=2520*X^2 := by
        rw [show (2520:Nat)=15*168 by decide]
        simp only [Nat.pow_succ,Nat.pow_zero]
        ac_rfl
  have hqA1RemBound : q*A1*(R2+d1)≤635040*X^3 := by
    calc
      q*A1*(R2+d1)≤(2520*X^2)*(252*X) :=
        Nat.mul_le_mul hqA1Bound hRem2Bound
      _=635040*X^3 := by
        rw [show (635040:Nat)=2520*252 by decide]
        simp only [Nat.pow_succ,Nat.pow_zero]
        ac_rfl
  have hprod1 : (q*A1)*2^(e-t1)=2^n := by
    calc
      (q*A1)*2^(e-t1)=q*(2^t1*2^(e-t1)) := by rw [hA1]; ac_rfl
      _=q*2^e := by
        rw [←Nat.pow_add]
        have heqT : t1+(e-t1)=e := by omega
        rw [heqT]
      _=2^n := by rw [←hExp]; exact hqp
  have hRem2Small : R2+d1<2^(e-t1) := by
    have hbound : 635040*X^3≤19172403734400*X^6 := by
      calc
        635040*X^3≤635040*X^4 := Nat.mul_le_mul_left 635040 hx34
        _≤635040*X^5 := Nat.mul_le_mul_left 635040 hx45
        _≤635040*X^6 := Nat.mul_le_mul_left 635040 hx56
        _≤19172403734400*X^6 :=
          Nat.mul_le_mul_right _ (by decide : 635040≤19172403734400)
    have hb : (q*A1)*(R2+d1)<(q*A1)*2^(e-t1) := by
      rw [hprod1]
      exact Nat.lt_of_le_of_lt (Nat.le_trans hqA1RemBound hbound) hGapX
    exact Nat.lt_of_mul_lt_mul_left hb
  have hEq2' : K*2^(e-t1)=
      (A3*(A4*(A5*E+R5)+R4)+R3)*2^t2+(R2+d1) := by
    rw [←hA2]
    simpa only [Nat.mul_add,Nat.add_assoc,Nat.mul_comm,Nat.mul_assoc,Nat.mul_left_comm] using hEq2
  obtain ⟨d2,ht2le,hR2eq,hEq3,hd2le,hA2le⟩ :=
    residue_peel (e-t1) t2 K (A3*(A4*(A5*E+R5)+R4)+R3) (R2+d1)
      hRem2Pos hRem2Small hEq2'
  have ht2pos : 1≤t2 := by dsimp [t2]; omega
  have hhalf2 : 2*d2≤R2+d1 := twice_quotient_le t2 d2 (R2+d1) ht2pos hR2eq
  have hA2Bound : A2≤252*X := by
    rw [hA2]
    exact Nat.le_trans hA2le hRem2Bound
  have hR3small : R3≤168*X := hR3bound (by omega)
  have hRem3Pos : 0<R3+d2 := by omega
  have hRem3Bound : R3+d2≤294*X := by
    have hd2Bound : d2≤126*X := by
      have hdouble : 2*d2≤252*X := Nat.le_trans hhalf2 hRem2Bound
      omega
    omega
  have hqA1A2Bound : q*A1*A2≤635040*X^3 := by
    calc
      q*A1*A2≤(2520*X^2)*(252*X) := Nat.mul_le_mul hqA1Bound hA2Bound
      _=635040*X^3 := by
        rw [show (635040:Nat)=2520*252 by decide]
        simp only [Nat.pow_succ,Nat.pow_zero]
        ac_rfl
  have hqA1A2RemBound : q*A1*A2*(R3+d2)≤186701760*X^4 := by
    calc
      q*A1*A2*(R3+d2)≤(635040*X^3)*(294*X) :=
        Nat.mul_le_mul hqA1A2Bound hRem3Bound
      _=186701760*X^4 := by
        rw [show (186701760:Nat)=635040*294 by decide]
        simp only [Nat.pow_succ,Nat.pow_zero]
        ac_rfl
  have hprod2 : (q*A1*A2)*2^((e-t1)-t2)=2^n := by
    calc
      (q*A1*A2)*2^((e-t1)-t2)=(q*A1)*(2^t2*2^((e-t1)-t2)) := by
        rw [hA2]
        ac_rfl
      _=(q*A1)*2^(e-t1) := by
        rw [←Nat.pow_add]
        have heqT : t2+((e-t1)-t2)=e-t1 := by omega
        rw [heqT]
      _=2^n := hprod1
  have hRem3Small : R3+d2<2^((e-t1)-t2) := by
    have hbound : 186701760*X^4≤19172403734400*X^6 := by
      calc
        186701760*X^4≤186701760*X^5 := Nat.mul_le_mul_left 186701760 hx45
        _≤186701760*X^6 := Nat.mul_le_mul_left 186701760 hx56
        _≤19172403734400*X^6 :=
          Nat.mul_le_mul_right _ (by decide : 186701760≤19172403734400)
    have hb : (q*A1*A2)*(R3+d2)<(q*A1*A2)*2^((e-t1)-t2) := by
      rw [hprod2]
      exact Nat.lt_of_le_of_lt (Nat.le_trans hqA1A2RemBound hbound) hGapX
    exact Nat.lt_of_mul_lt_mul_left hb
  have hEq3' : K*2^((e-t1)-t2)=
      (A4*(A5*E+R5)+R4)*2^t3+(R3+d2) := by
    rw [←hA3]
    simpa only [Nat.add_assoc,Nat.mul_comm,Nat.mul_assoc,Nat.mul_left_comm] using hEq3
  obtain ⟨d3,ht3le,hR3eq,hEq4,hd3le,hA3le⟩ :=
    residue_peel ((e-t1)-t2) t3 K (A4*(A5*E+R5)+R4) (R3+d2)
      hRem3Pos hRem3Small hEq3'
  have ht3pos : 1≤t3 := by dsimp [t3]; omega
  have hhalf3 : 2*d3≤R3+d2 := twice_quotient_le t3 d3 (R3+d2) ht3pos hR3eq
  have hA3Bound : A3≤294*X := by
    rw [hA3]
    exact Nat.le_trans hA3le hRem3Bound
  have hR4small : R4≤168*X := hR4bound (by omega)
  have hRem4Pos : 0<R4+d3 := by omega
  have hRem4Bound : R4+d3≤315*X := by
    have hd3Bound : d3≤147*X := by
      have hdouble : 2*d3≤294*X := Nat.le_trans hhalf3 hRem3Bound
      omega
    omega
  have hqA1A2A3Bound : q*A1*A2*A3≤186701760*X^4 := by
    calc
      q*A1*A2*A3≤(635040*X^3)*(294*X) :=
        Nat.mul_le_mul hqA1A2Bound hA3Bound
      _=186701760*X^4 := by
        rw [show (186701760:Nat)=635040*294 by decide]
        simp only [Nat.pow_succ,Nat.pow_zero]
        ac_rfl
  have hqA1A2A3RemBound : q*A1*A2*A3*(R4+d3)≤58811054400*X^5 := by
    calc
      q*A1*A2*A3*(R4+d3)≤(186701760*X^4)*(315*X) :=
        Nat.mul_le_mul hqA1A2A3Bound hRem4Bound
      _=58811054400*X^5 := by
        rw [show (58811054400:Nat)=186701760*315 by decide]
        simp only [Nat.pow_succ,Nat.pow_zero]
        ac_rfl
  have hprod3 : (q*A1*A2*A3)*2^(((e-t1)-t2)-t3)=2^n := by
    calc
      (q*A1*A2*A3)*2^(((e-t1)-t2)-t3)=
          (q*A1*A2)*(2^t3*2^(((e-t1)-t2)-t3)) := by
        rw [hA3]
        ac_rfl
      _=(q*A1*A2)*2^((e-t1)-t2) := by
        rw [←Nat.pow_add]
        have heqT : t3+(((e-t1)-t2)-t3)=(e-t1)-t2 := by omega
        rw [heqT]
      _=2^n := hprod2
  have hRem4Small : R4+d3<2^(((e-t1)-t2)-t3) := by
    have hbound : 58811054400*X^5≤19172403734400*X^6 := by
      calc
        58811054400*X^5≤58811054400*X^6 :=
          Nat.mul_le_mul_left 58811054400 hx56
        _≤19172403734400*X^6 :=
          Nat.mul_le_mul_right _ (by decide : 58811054400≤19172403734400)
    have hb : (q*A1*A2*A3)*(R4+d3)<
        (q*A1*A2*A3)*2^(((e-t1)-t2)-t3) := by
      rw [hprod3]
      exact Nat.lt_of_le_of_lt hqA1A2A3RemBound hGapX
    exact Nat.lt_of_mul_lt_mul_left hb
  have hEq4' : K*2^(((e-t1)-t2)-t3)=
      A4*(A5*E+R5)+(R4+d3) := by
    simpa only [Nat.add_assoc,Nat.mul_comm,Nat.mul_assoc,Nat.mul_left_comm] using hEq4
  have hEq4Peel : K*2^(((e-t1)-t2)-t3)=
      (A5*E+R5)*2^t4+(R4+d3) := by
    calc
      K*2^(((e-t1)-t2)-t3)=A4*(A5*E+R5)+(R4+d3) := hEq4'
      _=(A5*E+R5)*2^t4+(R4+d3) := by rw [hA4]; ac_rfl
  obtain ⟨d4,ht4le,hR4eq,hEq5,hd4le,hA4le⟩ :=
    residue_peel (((e-t1)-t2)-t3) t4 K (A5*E+R5) (R4+d3)
      hRem4Pos hRem4Small hEq4Peel
  have ht4pos : 1≤t4 := by dsimp [t4]; omega
  have hhalf4 : 2*d4≤R4+d3 := twice_quotient_le t4 d4 (R4+d3) ht4pos hR4eq
  have hA4Bound : A4≤315*X := by
    rw [hA4]
    exact Nat.le_trans hA4le hRem4Bound
  have hR5small : R5≤168*X := hR5bound (by omega)
  have hRem5Pos : 0<R5+d4 := by omega
  have hRem5Bound : R5+d4≤326*X := by
    have hd4Bound : d4≤158*X := by
      have hdouble : 2*d4≤315*X := Nat.le_trans hhalf4 hRem4Bound
      omega
    omega
  have hqA1A2A3A4Bound : q*A1*A2*A3*A4≤58811054400*X^5 := by
    calc
      q*A1*A2*A3*A4≤(186701760*X^4)*(315*X) :=
        Nat.mul_le_mul hqA1A2A3Bound hA4Bound
      _=58811054400*X^5 := by
        rw [show (58811054400:Nat)=186701760*315 by decide]
        simp only [Nat.pow_succ,Nat.pow_zero]
        ac_rfl
  have hqA1A2A3A4RemBound :
      q*A1*A2*A3*A4*(R5+d4)≤19172403734400*X^6 := by
    calc
      q*A1*A2*A3*A4*(R5+d4)≤
          (58811054400*X^5)*(326*X) :=
        Nat.mul_le_mul hqA1A2A3A4Bound hRem5Bound
      _=19172403734400*X^6 := by
        rw [show (19172403734400:Nat)=58811054400*326 by decide]
        simp only [Nat.pow_succ,Nat.pow_zero]
        ac_rfl
  have hprod4 : (q*A1*A2*A3*A4)*2^((((e-t1)-t2)-t3)-t4)=2^n := by
    calc
      (q*A1*A2*A3*A4)*2^((((e-t1)-t2)-t3)-t4)=
          (q*A1*A2*A3)*(2^t4*2^((((e-t1)-t2)-t3)-t4)) := by
        rw [hA4]
        ac_rfl
      _=(q*A1*A2*A3)*2^(((e-t1)-t2)-t3) := by
        rw [←Nat.pow_add]
        have heqT : t4+((((e-t1)-t2)-t3)-t4)=((e-t1)-t2)-t3 := by omega
        rw [heqT]
      _=2^n := hprod3
  have hRem5Small : R5+d4<2^((((e-t1)-t2)-t3)-t4) := by
    have hb : (q*A1*A2*A3*A4)*(R5+d4)<
        (q*A1*A2*A3*A4)*2^((((e-t1)-t2)-t3)-t4) := by
      rw [hprod4]
      exact Nat.lt_of_le_of_lt hqA1A2A3A4RemBound hGapX
    exact Nat.lt_of_mul_lt_mul_left hb
  have hEq5' : K*2^((((e-t1)-t2)-t3)-t4)=A5*E+(R5+d4) := by
    simpa only [Nat.add_assoc,Nat.mul_comm,Nat.mul_assoc,Nat.mul_left_comm] using hEq5
  have hEq5Peel : K*2^((((e-t1)-t2)-t3)-t4)=E*2^t5+(R5+d4) := by
    calc
      K*2^((((e-t1)-t2)-t3)-t4)=A5*E+(R5+d4) := hEq5'
      _=E*2^t5+(R5+d4) := by rw [hA5]; ac_rfl
  obtain ⟨d5,ht5le,hR5eq,hEq6,hd5le,hA5le⟩ :=
    residue_peel ((((e-t1)-t2)-t3)-t4) t5 K E (R5+d4)
      hRem5Pos hRem5Small hEq5Peel
  have hA5Bound : A5≤326*X := by
    rw [hA5]
    exact Nat.le_trans hA5le hRem5Bound
  have hEplus : E+1≤224*X := by
    have hh := hEbound (by omega)
    simpa [X] using hh
  have hA5Rem : A5≤R5+d4 := by rw [hA5]; exact hA5le
  have hUpper : K*2^((((e-t1)-t2)-t3)-t4)≤(R5+d4)*(E+1) := by
    have hAE : A5*E≤(R5+d4)*E := Nat.mul_le_mul_right E hA5Rem
    have hdist : (R5+d4)*(E+1)=(R5+d4)*E+(R5+d4) := by
      rw [Nat.mul_add]
      simp
    rw [hEq5']
    omega
  have hUpperX : (R5+d4)*(E+1)≤73024*X^2 := by
    calc
      (R5+d4)*(E+1)≤(326*X)*(224*X) :=
        Nat.mul_le_mul hRem5Bound hEplus
      _=73024*X^2 := by
        rw [show (73024:Nat)=326*224 by decide]
        simp only [Nat.pow_succ,Nat.pow_zero]
        ac_rfl
  have hK' : 392*(q*A1*A2*A3*A4)≤K := by
    simpa [A1,A2,A3,A4,Nat.mul_assoc] using hK
  have hLower : 392*2^n≤K*2^((((e-t1)-t2)-t3)-t4) := by
    have hh := Nat.mul_le_mul_right (2^((((e-t1)-t2)-t3)-t4)) hK'
    have hc : 392*2^n=
        (392*(q*A1*A2*A3*A4))*2^((((e-t1)-t2)-t3)-t4) := by
      rw [←hprod4]
      ac_rfl
    rw [hc]
    simpa only [Nat.mul_assoc] using hh
  have hSmallFinal : 73024*X^2<2^n := by
    have hsmall : 73024*X^2≤19172403734400*X^6 := by
      calc
        73024*X^2≤73024*X^3 := Nat.mul_le_mul_left 73024 hx23
        _≤73024*X^4 := Nat.mul_le_mul_left 73024 hx34
        _≤73024*X^5 := Nat.mul_le_mul_left 73024 hx45
        _≤73024*X^6 := Nat.mul_le_mul_left 73024 hx56
        _≤19172403734400*X^6 :=
          Nat.mul_le_mul_right _ (by decide : 73024≤19172403734400)
    exact Nat.lt_of_le_of_lt hsmall hGapX
  omega

#print axioms five_layer_abstract_barrier

end BB6.Agent43FiveLayer
