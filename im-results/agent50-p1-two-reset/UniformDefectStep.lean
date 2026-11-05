import TwoResetSharp
import DefectTransport

set_option maxHeartbeats 2000000

namespace BB6.Agent50TwoReset

/-- One positive inverse reset and following upper suffix preserve a positive
    dyadic defect whenever a prescribed polynomial envelope fits below 2^n.
    Source-shaped transition equalities are explicit hypotheses. -/
theorem uniform_defect_step
    (n m l s W K D F N C V Dp Fend : Nat)
    (hn : 42 ≤ n)
    (hfirst : 2^m ≤W)
    (hsmall : W*(24*(n+2)^2)<2^n)
    (hNpos : 0<N)
    (hNsmall : N≤n+m+1)
    (hK : K+n+3=7*2^n)
    (hV : V+C=2*2^m)
    (hdef : F+N=7*2^(n-m)*C)
    (hFD : F+D+m=K+2)
    (hstep : 2^l*Dp+m=K+D)
    (hl : 2≤l)
    (hpost : 2^s*Fend+Dp+m+l=K+2) :
    ∃ N2 C2 : Nat,
      0<N2 ∧ N2≤n+(m+l+s)+1 ∧ C2≤2^(m+l+s) ∧
      Fend+N2=7*2^(n-(m+l+s))*C2 ∧
      2^(m+l+s) ≤ W*(24*(n+2)^2) := by
  let x := n+2
  let B := 2^m
  let L := 2^l
  let M := 2*(n+m+2)-N
  have hMsum : M+N=2*(n+m+2) := by
    dsimp [M]
    omega
  have hMpos : 0<M := by omega
  have hxpos : 0<x := by dsimp [x]; omega
  have hsmallx : W*(24*x^2)<2^n := by simpa only [x] using hsmall
  have hfirstx : 2^m≤W := hfirst
  have hfactor : 1≤24*x^2 := by
    have hh : 1≤x^2 := Nat.one_le_pow 2 x (by omega)
    omega
  have hBlt : W<2^n := by
    have hh : W≤W*(24*x^2) := by
      have h := Nat.mul_le_mul_left W hfactor
      simpa only [Nat.mul_one] using h
    omega
  have hm : m<n := by
    by_cases hm : m<n
    · exact hm
    have hnm : n≤m := by omega
    have hpow : 2^n≤2^m := Nat.pow_le_pow_right (by decide) hnm
    omega
  have hMbound : M≤4*x := by
    dsimp [x]
    omega
  have hB4 : W*(4*x) <2^n := by
    have hpow2 : x≤x^2 := by
      have hh := Nat.pow_le_pow_right hxpos (by decide : 1≤2)
      simpa using hh
    have hle : 4*x≤24*x^2 := by omega
    have hh := Nat.mul_le_mul_left W hle
    omega
  let Q := 2^(n-m)
  have hP : 2^n=B*Q := by
    calc
      2^n = 2^(m+(n-m)) :=
        congrArg (fun e:Nat=>2^e) (by omega)
      _ = B*Q := Nat.pow_add 2 m (n-m)
  have hMQ : M<Q := by
    have hprod : (2^m)*M≤W*(4*x) :=
      Nat.mul_le_mul hfirst hMbound
    have hlt : (2^m)*M < (2^m)*Q := by rw [←hP]; omega
    exact Nat.lt_of_mul_lt_mul_left hlt
  have hV' : V+C=2*B := hV
  have hFD' : F+D+m=K+2 := hFD
  have hco := BB6.Agent28.defect_reset_input_identity n m K (2^n)
    B Q C F D N M V L Dp hK hP hV' hMsum
    (by simpa only [Q] using hdef) hFD'
    (by simpa only [L] using hstep)
  have hQval : L*Dp+M=(7*V)*Q := by
    simpa only [Nat.mul_assoc,Nat.mul_comm,Nat.mul_left_comm] using hco
  have hpowerdiv := BB6.Agent28.power_remainder_division (n-m) l (7*V) Dp M hMpos hMQ
    (by simpa only [L,Q] using hQval)
  have hLbound : L≤4*x := by omega
  obtain ⟨h,hh⟩ := hpowerdiv.1
  have hMh : M=L*h := hh
  have hL4 : 4≤L := by
    have hh : (2:Nat)^2 ≤2^l := Nat.pow_le_pow_right (by decide) hl
    simpa only [show (2:Nat)^2=4 by decide,L] using hh
  have hlpow : l<L := Nat.lt_pow_self (by decide : 1<(2:Nat))
  have hN2hhalf : 2*h≤n+m+2 := by
    have hh : 4*h≤L*h := Nat.mul_le_mul_right h hL4
    omega
  have hl : l<n-m := by
    have hh : L < Q := by omega
    exact (Nat.pow_lt_pow_iff_right (by decide : 1<(2:Nat))).mp hh
  let Q2 := 2^(n-m-l)
  have hQ : Q=L*Q2 := by
    calc
      Q = 2^(l+(n-m-l)) :=
        congrArg (fun e:Nat=>2^e) (by omega)
      _ = L*Q2 := Nat.pow_add 2 l (n-m-l)
  have hP2 : 2^n=B*L*Q2 := by
    calc
      2^n = B*Q := hP
      _ = B*L*Q2 := by rw [hQ]; ac_rfl
  let N2 := n+m+l+1-h
  have hN2sum : N2+h=n+m+l+1 := by dsimp [N2]; omega
  have hN2pos : 0<N2 := by omega
  have hN2bound : N2≤6*x := by
    have hlin : l≤L := Nat.le_of_lt hlpow
    dsimp [x] at hMbound ⊢
    omega
  let Cp := B*L-V
  have hVle : V≤2*B := by omega
  have hCpbound : V≤B*L := by
    have hh : B*4≤B*L := Nat.mul_le_mul_left B hL4
    omega
  have hCp : Cp+V=B*L := by dsimp [Cp]; omega
  have hout := BB6.Agent28.defect_reset_output_identity
    n m l K (2^n) B L Q2 C (2^s*Fend) Dp N2 M V Cp h
    hK hP2 hCp hMh hN2sum
    (by simpa only [hQ,Nat.mul_assoc,Nat.mul_comm,Nat.mul_left_comm] using hQval)
    hpost (by dsimp [L]; exact Nat.pow_pos (by decide))
  have hsuffix : 2^s*Fend+N2=(7*Cp)*Q2 := by
    simpa only [Nat.mul_assoc,Nat.mul_comm,Nat.mul_left_comm] using hout
  have hN2prod : (B*L)*N2 ≤ W*(24*x^2) := by
    calc
      _ ≤ (W*(4*x))*(6*x) :=
        Nat.mul_le_mul (Nat.mul_le_mul hfirst hLbound) hN2bound
      _ = W*(24*x^2) := by
        simp only [Nat.pow_succ, Nat.pow_zero]
        ac_rfl
  have hN2small : N2<Q2 := by
    have hlt : (B*L)*N2 < (B*L)*Q2 := by rw [←hP2]; omega
    exact Nat.lt_of_mul_lt_mul_left hlt
  have hdiv2 := BB6.Agent28.power_remainder_division (n-m-l) s
    (7*Cp) Fend N2 hN2pos hN2small
    (by simpa only [Q2,Nat.mul_assoc,Nat.mul_comm,Nat.mul_left_comm] using hsuffix)
  have hSbound : 2^s≤6*x := by omega
  have hpowtotal : 2^(m+l+s) ≤ W*(24*x^2) := by
    calc
      2^(m+l+s)=(B*L)*2^s := by
        dsimp [B,L]
        simp only [Nat.pow_add]
      _≤(W*(4*x))*(6*x) :=
        Nat.mul_le_mul (Nat.mul_le_mul hfirst hLbound) hSbound
      _=W*(24*x^2) := by
        simp only [Nat.pow_succ,Nat.pow_zero]
        ac_rfl
  obtain ⟨N3,hN3⟩ := hdiv2.1
  have hN3eq : N2=2^s*N3 := hN3
  have hN3pos : 0<N3 := by
    by_cases hz:N3=0
    · have hh:N2=0 := by simpa only [hz,Nat.mul_zero] using hN3eq
      omega
    · omega
  have hN3bound : N3≤n+(m+l+s)+1 := by
    have hspos : 1≤2^s := Nat.one_le_pow s 2 (by decide)
    have hle : N3≤2^s*N3 := by
      have hh := Nat.mul_le_mul_right N3 hspos
      simpa using hh
    omega
  have hslt : s<n-m-l := by
    have hh : 2^s<Q2 := by omega
    exact (Nat.pow_lt_pow_iff_right (by decide : 1<(2:Nat))).mp hh
  let Q3 := 2^(n-(m+l+s))
  have hQ23 : Q2=2^s*Q3 := by
    calc
      Q2=2^(s+(n-(m+l+s))) :=
        congrArg (fun z:Nat=>2^z) (by omega)
      _=2^s*Q3 := Nat.pow_add 2 s (n-(m+l+s))
  have hdef3 : Fend+N3=7*Q3*Cp := by
    have hspos : 0<2^s := Nat.pow_pos (by decide)
    have hh : 2^s*(Fend+N3)=2^s*(7*Q3*Cp) := by
      calc
        _=2^s*Fend+N2 := by rw [hN3eq]; simp only [Nat.mul_add]
        _=(7*Cp)*Q2 := hsuffix
        _=2^s*(7*Q3*Cp) := by rw [hQ23]; ac_rfl
    exact Nat.mul_left_cancel hspos hh
  have hCpBound : Cp≤2^(m+l+s) := by
    have hCp0 : Cp≤B*L := by omega
    have hspos : 1≤2^s := Nat.one_le_pow s 2 (by decide)
    have hle : B*L ≤ (B*L)*2^s := by
      have hh := Nat.mul_le_mul_left (B*L) hspos
      simpa only [Nat.mul_one] using hh
    have heq : (B*L)*2^s=2^(m+l+s) := by
      dsimp [B,L]; simp only [Nat.pow_add]
    omega
  refine ⟨N3,Cp,hN3pos,hN3bound,hCpBound,?_,?_⟩
  · simpa only [Q3,Nat.mul_assoc,Nat.mul_comm,Nat.mul_left_comm] using hdef3
  · simpa only [x] using hpowtotal

#print axioms BB6.Agent50TwoReset.uniform_defect_step
end BB6.Agent50TwoReset
