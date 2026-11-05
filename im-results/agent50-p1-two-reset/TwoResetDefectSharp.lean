import TwoResetSharp
import DefectTransport

set_option maxHeartbeats 2000000

namespace BB6.Agent50TwoReset

/-- An exact, source-shaped two-reset budget. The hypotheses are explicit;
    a theorem transferring all authentic OddCone histories is separate. -/
theorem exact_two_reset_sharp_defect_budget
    (n m l s K D F N C V Dp Fend : Nat)
    (hn : 42 ≤ n)
    (hfirst : 2^m ≤24*(n+2)^3)
    (hNpos : 0<N)
    (hNsmall : N≤n+m+1)
    (hK : K+n+3=7*2^n)
    (hV : V+C=2*2^m)
    (hdef : F+N=7*2^(n-m)*C)
    (hFD : F+D+m=K+2)
    (hstep : 2^l*Dp+m=K+D)
    (hl : 2≤l)
    (hpost : 2^s*Fend+Dp+m+l=K+2) :
    2^(m+l+s) ≤ 576*(n+2)^5 := by
  let x := n+2
  let B := 2^m
  let L := 2^l
  let M := 2*(n+m+2)-N
  have hMsum : M+N=2*(n+m+2) := by
    dsimp [M]
    omega
  have hMpos : 0<M := by omega
  have hgrowth : 576*x^6<2^n := by
    simpa only [x] using sharp_sextic_growth n hn
  have hxpos : 0<x := by dsimp [x]; omega
  have hx36 : x^3≤x^6 := Nat.pow_le_pow_right hxpos (by decide)
  have hx46 : x^4≤x^6 := Nat.pow_le_pow_right hxpos (by decide)
  have hfirstx : B≤24*x^3 := hfirst
  have hfirstP : 24*x^3 < 2^n := by
    have hhl : 24*x^3 ≤576*x^6 := by
      have hh := Nat.mul_le_mul_left 24 hx36
      omega
    omega
  have hm : m<n := by
    by_cases hm : m<n
    · exact hm
    have hnm : n≤m := by omega
    have hpow : 2^n≤B := Nat.pow_le_pow_right (by decide) hnm
    omega
  have hMbound : M≤4*x := by
    dsimp [x]
    omega
  let Q := 2^(n-m)
  have hP : 2^n=B*Q := by
    calc
      2^n = 2^(m+(n-m)) :=
        congrArg (fun e:Nat=>2^e) (by omega)
      _ = B*Q := Nat.pow_add 2 m (n-m)
  have hMQ : M<Q := by
    have hprod : B*M ≤ 96*x^4 := by
      calc
        _ ≤ (24*x^3)*(4*x) :=
          Nat.mul_le_mul hfirstx hMbound
        _ = 96*x^4 := by
          simp only [Nat.pow_succ,Nat.pow_zero]
          ac_rfl
    have hbig : 96*x^4 < 2^n := by
      have hh : 96*x^4 ≤576*x^6 := by
        have hle := Nat.mul_le_mul_left 96 hx46
        omega
      omega
    have hlt : B*M < B*Q := by rw [←hP]; omega
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
  exact two_reset_sharp_budget n m l s M N2 Dp Fend V Cp
    hn hfirst hMpos (by simpa only [x] using hMbound)
    hN2pos (by simpa only [x] using hN2bound)
    (by simpa only [L,Q] using hQval)
    (by simpa only [Q2] using hsuffix)

#print axioms BB6.Agent50TwoReset.exact_two_reset_sharp_defect_budget
end BB6.Agent50TwoReset
