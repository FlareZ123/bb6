import Lean
import Lean.Elab.Tactic.Omega
set_option maxHeartbeats 2000000
namespace BB6.ThreeResetCore

private theorem five_pow_linear (n : Nat) (hn : 15 ≤ n) : 7011*n+14714 < 5*2^n := by
  have hbase : 7011*15+14714 < 5*2^15 := by decide
  have hrec : ∀ k : Nat, 7011*(15+k)+14714 < 5*2^(15+k) := by
    intro k
    induction k with
    | zero => exact hbase
    | succ k ih =>
      have hp : 0 < (2:Nat)^(15+k) := Nat.pow_pos (by decide)
      have hidx : 15+(k+1)=(15+k)+1 := by omega
      rw [hidx, Nat.pow_succ]
      omega
  have heq : 15+(n-15)=n := by omega
  simpa [heq] using hrec (n-15)

private theorem r0_no_power
    (n P m2 B D C L u : Nat)
    (hmLo : 4≤m2) (hmHi : m2≤5*n+7)
    (hC : C=2*P+146*m2+146*n+816)
    (hLdef : L=D+B/2+3) (hLpow : L=2^u*C) (hu : 1≤u)
    (hMass : B+D+2*n+13=14*P)
    (hRoot0 : B+12+2*n+4=14*P)
    (_hBeven : 2*(B/2)=B)
    (hGap0 : 3*P>1753*n+3678) : False := by
  have hLexact : 2*L+2*n+4=14*P := by
    clear hLpow hu
    omega
  have hClo : 2*P+146*n+1400≤C := by rw [hC]; omega
  have hChi : C≤2*P+876*n+1838 := by rw [hC]; omega
  have hLlow2 : 4*C<2*L := by
    clear hLpow hu
    omega
  have hLlow : 2*C<L := by
    clear hLpow hu
    omega
  have hLhigh : L<4*C := by
    clear hLpow hu
    omega
  by_cases hu1 : u=1
  · rw [hu1] at hLpow
    omega
  · have hu2 : 2≤u := by omega
    have hpowU : 4≤2^u := by
      have hh := Nat.pow_le_pow_right (by decide : 0<(2:Nat)) hu2
      simpa using hh
    have hmul : 4*C≤2^u*C := Nat.mul_le_mul_right C hpowU
    omega

private theorem r1_no_power
    (n P m2 B D C L u : Nat)
    (hn : 14≤n)
    (hmLo : 4≤m2) (hmHi : m2≤5*n+7)
    (hC : C=2*P+146*m2+146*n+816)
    (hLdef : L=D+B/2+3) (hLpow : L=2^u*C) (hu : 1≤u)
    (hMass : B+D+2*n+15=14*P)
    (hRoot1 : 2*(B+12)+2*n+4=14*P)
    (hBeven : 2*(B/2)=B)
    (hGap1 : 13*P>3507*n+7362)
    (hP14 : n=14 -> P=16384)
    (hFive : 15≤n -> 7011*n+14714<5*P) : False := by
  have hLtwice : 2*L+3*n+10=21*P := by
    rw [hLdef]
    have hD : B+D+2*n+15=14*P := hMass
    have hBhalf : 2*(B/2)=B := hBeven
    omega
  have hClo : 2*P+146*n+1400≤C := by rw [hC]; omega
  have hChi : C≤2*P+876*n+1838 := by rw [hC]; omega
  have hLlow2 : 4*C<2*L := by
    clear hLpow hu
    omega
  have hLlow : 2*C<L := by
    clear hLpow hu
    omega
  have hLhigh : L<8*C := by
    clear hLpow hu
    omega
  have hNot4 : L≠4*C := by
    clear hLpow hu
    intro hEq
    have hEq2 : 2*L=8*C := by omega
    have hEq' : 5*P=1168*m2+1171*n+6538 := by
      rw [hC] at hEq2
      omega
    by_cases hn14 : n=14
    · have hP14' := hP14 hn14
      rw [hP14'] at hEq'
      omega
    · have hn15 : 15≤n := by omega
      have hFive' := hFive hn15
      have hbound : 1168*m2+1171*n+6538≤7011*n+14714 := by omega
      omega
  by_cases hu1 : u=1
  · rw [hu1] at hLpow
    omega
  · by_cases hu2 : u=2
    · rw [hu2] at hLpow
      exact hNot4 (by omega)
    · have hu3 : 3≤u := by omega
      have hpowU : 8≤2^u := by
        have hh := Nat.pow_le_pow_right (by decide : 0<(2:Nat)) hu3
        simpa using hh
      have hmul : 8*C≤2^u*C := Nat.mul_le_mul_right C hpowU
      omega

private theorem rge2_no_power
    (n P m2 r B D C L u : Nat)
    (hn : 14≤n)
    (hmLo : 4≤m2) (hmHi : m2≤5*n+7) (hr : r≤m2)
    (hC : C=2*P+146*m2+146*n+816)
    (hLdef : L=D+B/2+3) (hLpow : L=2^u*C)
    (hMass : B+D+2*r+2*n+13=14*P)
    (hBbound : 4*(B+12)+2*n+4≤14*P)
    (hBeven : 2*(B/2)=B)
    (hGap2 : 34*P>28126*n+58964) : False := by
  have hClo : 2*P+146*n+1400≤C := by rw [hC]; omega
  have hChi : C≤2*P+876*n+1838 := by rw [hC]; omega
  have hLform : L+B/2+2*r+2*n+10=14*P := by
    clear hLpow
    rw [hLdef]
    omega
  have hL8lower : 8*L+16*r+14*n+28≥98*P := by
    clear hLpow
    have hBeven' : B=2*(B/2) := by omega
    have hBbound' : 8*(B/2)+2*n+52≤14*P := by omega
    have hLscaled : 8*L+8*(B/2)+16*r+16*n+80=112*P := by omega
    omega
  have hLlow : 4*C<L := by
    clear hLpow
    have hgap : 34*P>28126*n+58964 := hGap2
    omega
  have hLupper : L<14*P := by
    clear hLpow
    omega
  have hLhigh : L<8*C := by
    clear hLpow
    omega
  by_cases hu2 : u≤2
  · have hpowU : 2^u≤4 := by
      have hh := Nat.pow_le_pow_right (by decide : 0<(2:Nat)) hu2
      simpa using hh
    have hmul : 2^u*C≤4*C := Nat.mul_le_mul_right C hpowU
    omega
  · have hu3 : 3≤u := by omega
    have hpowU : 8≤2^u := by
      have hh := Nat.pow_le_pow_right (by decide : 0<(2:Nat)) hu3
      simpa using hh
    have hmul : 8*C≤2^u*C := Nat.mul_le_mul_right C hpowU
    omega

/-- A three-reset shifted-wall prefix is excluded by the final reset's dyadic
    factor. The source wrapper supplies the displayed mass and reset equations. -/
theorem no_three_reset_root_power
    (n P m2 r B D C L u : Nat)
    (hn : 14≤n)
    (hmLo : 4≤m2) (hmHi : m2≤5*n+7) (hr : r≤m2)
    (hC : C=2*P+146*m2+146*n+816)
    (hLdef : L=D+B/2+3) (hLpow : L=2^u*C) (hu : 1≤u)
    (hMass : B+D+2*r+2*n+13=14*P)
    (hRoot : 2^r*(B+12)+2*n+4=14*P)
    (hBeven : 2*(B/2)=B)
    (hGap0 : 3*P>1753*n+3678)
    (hGap1 : 13*P>3507*n+7362)
    (hGap2 : 34*P>28126*n+58964)
    (hP14 : n=14 -> P=16384)
    (hFive : 15≤n -> 7011*n+14714<5*P) : False := by
  by_cases hr0 : r=0
  · subst r
    have hMass0 : B+D+2*n+13=14*P := by simpa using hMass
    have hRoot0 : B+12+2*n+4=14*P := by simpa using hRoot
    exact r0_no_power n P m2 B D C L u hmLo hmHi hC hLdef hLpow hu hMass0 hRoot0 hBeven hGap0
  · have hrpos : 1≤r := by omega
    by_cases hr1 : r=1
    · subst r
      have hMass1 : B+D+2*n+15=14*P := by omega
      have hRoot1 : 2*(B+12)+2*n+4=14*P := by simpa using hRoot
      exact r1_no_power n P m2 B D C L u hn hmLo hmHi hC hLdef hLpow hu hMass1 hRoot1 hBeven hGap1 hP14 hFive
    · have hr2 : 2≤r := by omega
      have hpowr : 4≤2^r := by
        have hh := Nat.pow_le_pow_right (by decide : 0<(2:Nat)) hr2
        simpa using hh
      have hmulB : 4*(B+12)≤2^r*(B+12) := Nat.mul_le_mul_right (B+12) hpowr
      have hBbound : 4*(B+12)+2*n+4≤14*P := by
        calc
          4*(B+12)+2*n+4 ≤ 2^r*(B+12)+2*n+4 := by omega
          _ = 14*P := hRoot
      exact rge2_no_power n P m2 r B D C L u hn hmLo hmHi hr hC hLdef hLpow hMass hBbound hBeven hGap2

private theorem eleven_hundred_mul_le_pow (n : Nat) (hn : 14 ≤ n) :
    1100*n ≤ 2^n := by
  have hbase : 1100*14 ≤ 2^14 := by decide
  have hrec : ∀ k : Nat, 1100*(14+k) ≤ 2^(14+k) := by
    intro k
    induction k with
    | zero => exact hbase
    | succ k ih =>
      have hp : 0 < (2:Nat)^(14+k) := Nat.pow_pos (by decide)
      have hidx : 14+(k+1)=(14+k)+1 := by omega
      rw [hidx, Nat.pow_succ]
      omega
  have heq : 14+(n-14)=n := by omega
  simpa [heq] using hrec (n-14)

/-- Numerical side conditions for the three-reset dyadic gap. -/
theorem three_reset_numeric_bounds (n P : Nat) (hn : 14≤n) (hP : P=2^n) :
    1100*n≤P ∧
    3*P>1753*n+3678 ∧
    13*P>3507*n+7362 ∧
    34*P>28126*n+58964 ∧
    (n=14 -> P=16384) ∧
    (15≤n -> 7011*n+14714<5*P) := by
  have h1100 : 1100*n≤P := by simpa [hP] using eleven_hundred_mul_le_pow n hn
  have hP14 : n=14 -> P=16384 := by
    intro h
    subst n
    have hpow14 : 2^14=16384 := by decide
    simpa [hP] using hpow14
  have hFive : 15≤n -> 7011*n+14714<5*P := by
    intro hn15
    have hlin := five_pow_linear n hn15
    rw [hP]
    exact hlin
  refine ⟨h1100, ?_, ?_, ?_, hP14, hFive⟩
  · omega
  · omega
  · omega

#print axioms BB6.ThreeResetCore.no_three_reset_root_power
#print axioms BB6.ThreeResetCore.three_reset_numeric_bounds

end BB6.ThreeResetCore