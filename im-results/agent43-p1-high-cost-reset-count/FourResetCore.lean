import Lean
import Lean.Elab.Tactic.Omega

set_option maxHeartbeats 5000000

namespace BB6.Agent43FourResetCore

private theorem linear3_pow18 (n : Nat) (hn : 18 ≤ n) :
    9361*n+36446 < 3*2^n := by
  induction n with
  | zero => omega
  | succ n ih =>
    by_cases hk : 18 ≤ n
    · have hpow : 2^18 ≤ 2^n :=
        Nat.pow_le_pow_right (by decide : 0 < (2:Nat)) hk
      have hbase : 9361 ≤ 3*2^18 := by decide
      have hbig : 9361 ≤ 3*2^n := Nat.le_trans hbase (Nat.mul_le_mul_left 3 hpow)
      have hcur := ih hk
      rw [Nat.pow_succ]
      omega
    · have hnEq : n=17 := by omega
      subst n
      decide

private theorem linear13_pow15 (n : Nat) (hn : 15 ≤ n) :
    18723*n+72898 < 13*2^n := by
  induction n with
  | zero => omega
  | succ n ih =>
    by_cases hk : 15 ≤ n
    · have hpow : 2^15 ≤ 2^n :=
        Nat.pow_le_pow_right (by decide : 0 < (2:Nat)) hk
      have hbase : 18723 ≤ 13*2^15 := by decide
      have hbig : 18723 ≤ 13*2^n := Nat.le_trans hbase (Nat.mul_le_mul_left 13 hpow)
      have hcur := ih hk
      rw [Nat.pow_succ]
      omega
    · have hnEq : n=14 := by omega
      subst n
      decide

private theorem linear5_pow18 (n : Nat) (hn : 18 ≤ n) :
    37443*n+145786 < 5*2^n := by
  induction n with
  | zero => omega
  | succ n ih =>
    by_cases hk : 18 ≤ n
    · have hpow : 2^18 ≤ 2^n :=
        Nat.pow_le_pow_right (by decide : 0 < (2:Nat)) hk
      have hbase : 37443 ≤ 5*2^18 := by decide
      have hbig : 37443 ≤ 5*2^n := Nat.le_trans hbase (Nat.mul_le_mul_left 5 hpow)
      have hcur := ih hk
      rw [Nat.pow_succ]
      omega
    · have hnEq : n=17 := by omega
      subst n
      decide

private theorem linear34_pow18 (n : Nat) (hn : 18 ≤ n) :
    149790*n+583132 < 34*2^n := by
  induction n with
  | zero => omega
  | succ n ih =>
    by_cases hk : 18 ≤ n
    · have hpow : 2^18 ≤ 2^n :=
        Nat.pow_le_pow_right (by decide : 0 < (2:Nat)) hk
      have hbase : 149790 ≤ 34*2^18 := by decide
      have hbig : 149790 ≤ 34*2^n := Nat.le_trans hbase (Nat.mul_le_mul_left 34 hpow)
      have hcur := ih hk
      rw [Nat.pow_succ]
      omega
    · have hnEq : n=17 := by omega
      subst n
      decide

private theorem linear10_pow14 (n : Nat) (hn : 14 ≤ n) :
    7026*n+34114 < 10*2^n := by
  induction n with
  | zero => omega
  | succ n ih =>
    by_cases hk : 14 ≤ n
    · have hpow : 2^14 ≤ 2^n :=
        Nat.pow_le_pow_right (by decide : 0 < (2:Nat)) hk
      have hbase : 7026 ≤ 10*2^14 := by decide
      have hbig : 7026 ≤ 10*2^n := Nat.le_trans hbase (Nat.mul_le_mul_left 10 hpow)
      have hcur := ih hk
      rw [Nat.pow_succ]
      omega
    · have hnEq : n=13 := by omega
      subst n
      decide

/-- If the root prefix has one positive reset followed by exactly one
zero-depth edge, its total cost is at most 2*n+3. -/
theorem one_tail_prefix_cost_bound
    (n P B D R u c : Nat)
    (hn : 14≤n) (hP : P=2^n)
    (hMass : B+D+2*R+2*n+13=14*P)
    (hDy : 2^R*(B+12)+2*n+4=14*P)
    (hInv : D+B/2+3=2^u*(c+3))
    (hcOdd : c%2=1) : R+u+2≤2*n+3 := by
  have hRmul : 12*2^R≤14*P := by
    have h12 : 12≤B+12 := by omega
    have hmul := Nat.mul_le_mul_left (2^R) h12
    omega
  have hRmulN : 12*2^R≤14*2^n := by rw [hP] at hRmul; exact hRmul
  have hpowN : 2^(n+1)=2*2^n := by rw [Nat.pow_succ]; omega
  have hRpow : 2^R<2^(n+1) := by
    rw [hpowN]
    have hstrict : 14*2^n<24*2^n := by omega
    omega
  have hR : R≤n := by
    have hexp := (Nat.pow_lt_pow_iff_right (by decide : 1<(2:Nat))).mp hRpow
    omega
  have hBD : B+D≤14*P := by omega
  have hhalf : B/2≤B := Nat.div_le_self B 2
  have hL : D+B/2+3≤14*P := by omega
  have hc : 4≤c+3 := by omega
  have hUmul : 4*2^u≤2^u*(c+3) := by
    calc
      4*2^u = 2^u*4 := by omega
      _ ≤ 2^u*(c+3) := Nat.mul_le_mul_left (2^u) hc
  have hUmulP : 4*2^u≤14*P := by rw [← hInv] at hUmul; omega
  have hPpow : 2^(n+2)=4*2^n := by
    rw [show n+2=n+1+1 by omega, Nat.pow_succ, Nat.pow_succ]
    omega
  have hUstrict : 2^u<2^(n+2) := by
    rw [hPpow] at *
    rw [hP] at hUmulP
    have hstrict : 14*2^n<16*2^n := by omega
    omega
  have hU : u≤n+1 := by
    have hexp := (Nat.pow_lt_pow_iff_right (by decide : 1<(2:Nat))).mp hUstrict
    omega
  omega

/-- Root-connected one-reset histories with a one-step zero-depth suffix are
impossible once the preceding two-reset peel gives the displayed cost bound. -/
theorem no_four_reset_root_one_tail
    (n P b d m j c : Nat)
    (hn : 14 ≤ n) (hP : P=2^n)
    (hm : m≤2*n+3)
    (hMass : b+d+2*m+2*n+13=14*P)
    (hD : d=2*P+1170*m+1170*n+13543)
    (hDy : 2*(b+12)=2*j+8)
    (hRight : d=c+j+6) : False := by
  have hj : j=b+8 := by omega
  have hC : c+3+10*P=2342*m+2342*n+27088 := by omega
  have hnum := linear10_pow14 n hn
  have hbound : 2342*m+2342*n+27088 ≤ 7026*n+34114 := by omega
  omega

/-- The exact root equations left by the four-reset peel cannot support a
zero-depth-free one-reset prefix. -/
theorem no_four_reset_root_zero_tail
    (n P m r B D C L u : Nat)
    (hn : 14 ≤ n) (hP : P=2^n)
    (hB4 : B%4=0)
    (hMass : B+D+2*r+2*n+13=14*P)
    (hDy : 2^r*(B+12)+2*n+4=14*P)
    (hL : L=D+B/2+3)
    (hInv : L=2^u*C)
    (hC : C=2*P+1170*m+1170*n+13542)
    (hmLower : 2≤m) (hmUpper : m≤3*n+4)
    (hu : 1≤u) : False := by
  have hBdiv : 2*(B/2)=B := by omega
  have hClo : 2*P≤C := by omega
  have hLbound : L≤14*P := by rw [hL]; omega
  have huLe : u≤2 := by
    by_cases hle : u≤2
    · exact hle
    · have hthree : 3≤u := by omega
      have hpow : 8≤2^u := Nat.pow_le_pow_right (by decide : 0<(2:Nat)) hthree
      have h1 : 16*P≤8*C := by
        have hh := Nat.mul_le_mul_left 8 hClo
        omega
      have h2 : 8*C≤2^u*C := Nat.mul_le_mul_right C hpow
      have hmul : 16*P≤2^u*C := Nat.le_trans h1 h2
      omega
  have huCases : u=1 ∨ u=2 := by omega
  by_cases hr0 : r=0
  · have hB : B+12+2*n+4=14*P := by simpa [hr0] using hDy
    have hD : D=3 := by omega
    have hL0 : L=7*P-n-2 := by rw [hL,hD]; omega
    rcases huCases with hu1 | hu2
    · have hEq : 3*P=2340*m+2341*n+27086 := by
        rw [hu1] at hInv
        rw [hL0,hC] at hInv
        omega
      by_cases hn14 : n=14
      · subst n
        rw [hP] at hEq
        have hmin : 64540≤2340*m+2341*14+27086 := by omega
        omega
      · by_cases hn15 : n=15
        · subst n
          have hmod : (2340*m+2341*15+27086)%3=2 := by omega
          rw [hP] at hEq
          omega
        · by_cases hn16 : n=16
          · subst n
            rw [hP] at hEq
            have hmax : 2340*m+2341*16+27086≤186222 := by omega
            omega
          · by_cases hn17 : n=17
            · subst n
              rw [hP] at hEq
              have hmax : 2340*m+2341*17+27086≤195583 := by omega
              omega
            · have hn18 : 18≤n := by omega
              have hbig := linear3_pow18 n hn18
              rw [← hP] at hbig
              have hmax : 2340*m+2341*n+27086≤9361*n+36446 := by omega
              omega
    · rw [hu2] at hInv
      rw [hL0,hC] at hInv
      omega
  · by_cases hr1 : r=1
    · have hDy1 : 2*(B+12)+2*n+4=14*P := by simpa [hr1] using hDy
      have hL1 : 2*L+3*n+10=21*P := by rw [hL]; omega
      rcases huCases with hu1 | hu2
      · have hEq : 13*P=4680*m+4683*n+54178 := by
          rw [hu1] at hInv
          simp at hInv
          omega
        by_cases hn14 : n=14
        · subst n
          rw [hP] at hEq
          have hlow : 4680*19 < 93252 := by decide
          have hhigh : 93252 < 4680*20 := by decide
          omega
        · have hn15 : 15≤n := by omega
          have hbig := linear13_pow15 n hn15
          rw [← hP] at hbig
          have hmax : 4680*m+4683*n+54178≤18723*n+72898 := by omega
          omega
      · have hEq : 5*P=9360*m+9363*n+108346 := by
          rw [hu2] at hInv
          simp at hInv
          omega
        by_cases hn14 : n=14
        · subst n
          rw [hP] at hEq
          have hmod : (9360*m+9363*14+108346)%16=4 := by omega
          have hPmod : (5*P)%16=0 := by rw [hP]
          omega
        · by_cases hn15 : n=15
          · subst n
            rw [hP] at hEq
            have hmod : (9360*m+9363*15+108346)%2=1 := by omega
            have hPmod : (5*P)%2=0 := by rw [hP]
            omega
          · by_cases hn16 : n=16
            · subst n
              rw [hP] at hEq
              have hmod : (9360*m+9363*16+108346)%16=10 := by omega
              have hPmod : (5*P)%16=0 := by rw [hP]
              omega
            · by_cases hn17 : n=17
              · subst n
                rw [hP] at hEq
                have hmod : (9360*m+9363*17+108346)%2=1 := by omega
                have hPmod : (5*P)%2=0 := by rw [hP]
                omega
              · have hn18 : 18≤n := by omega
                have hbig := linear5_pow18 n hn18
                rw [← hP] at hbig
                have hmax : 9360*m+9363*n+108346≤37443*n+145786 := by omega
                omega
    · have hr2 : 2≤r := by omega
      have hpow4 : 4≤2^r := Nat.pow_le_pow_right (by decide : 0<(2:Nat)) hr2
      have hmul4 : 4*(B+12)≤2^r*(B+12) := Nat.mul_le_mul_right (B+12) hpow4
      have hBbound : 4*B+2*n+52≤14*P := by omega
      have hLid : 8*L+16*r+14*n+28+4*B+2*n+52=112*P := by rw [hL]; omega
      have hRbound : 12*2^r≤14*P := by
        have h12 : 12≤B+12 := by omega
        have hmul := Nat.mul_le_mul_left (2^r) h12
        omega
      have hRboundN : 12*2^r≤14*2^n := by rw [hP] at hRbound; exact hRbound
      have hpowN : 2^(n+1)=2*2^n := by rw [Nat.pow_succ]; omega
      have hpowStrict : 2^r<2^(n+1) := by
        rw [hpowN]
        have hstrict : 14*2^n<24*2^n := by omega
        omega
      have hrLe : r≤n := by
        have hexp := (Nat.pow_lt_pow_iff_right (by decide : 1<(2:Nat))).mp hpowStrict
        omega
      have hLlower : 98*P≤8*L+16*r+14*n+28 := by omega
      have hLlower' : 98*P≤8*L+30*n+28 := by omega
      have hCupper : C≤2*P+4680*n+18222 := by omega
      by_cases hn14 : n=14
      · subst n
        rw [hP] at hDy hMass hLbound hC
        have hBfactor : B+12=4*(B/4+3) := by omega
        have hrLe3 : r≤3 := by
          by_cases hle : r≤3
          · exact hle
          · have hr4 : 4≤r := by omega
            have hpowFactor : 2^r=16*2^(r-4) := by
              have heq : 4+(r-4)=r := by omega
              calc
                2^r = 2^(4+(r-4)) := by rw [heq]
                _ = 2^4*2^(r-4) := by rw [Nat.pow_add]
                _ = 16*2^(r-4) := by rw [show (2:Nat)^4=16 by decide]
            have hprod : 2^r*(B+12)=64*(2^(r-4)*(B/4+3)) := by
              rw [hpowFactor,hBfactor]
              calc
                (16*2^(r-4))*(4*(B/4+3)) = (16*4)*(2^(r-4)*(B/4+3)) := by ac_rfl
                _ = 64*(2^(r-4)*(B/4+3)) := by omega
            have hEq : 2^r*(B+12)=229344 := by omega
            rw [hprod] at hEq
            omega
        have hrCases : r=2 ∨ r=3 := by omega
        rcases hrCases with hrEq | hrEq
        · have hLval : L=200672 := by
            have hBval : B=57324 := by rw [hrEq] at hDy; omega
            have hDval : D=172007 := by rw [hBval] at hMass; omega
            rw [hL,hBval,hDval]
          rcases huCases with hu1 | hu2
          · rw [hu1] at hInv
            have hCeq : C=100336 := by omega
            rw [hC] at hCeq
            omega
          · rw [hu2] at hInv
            have hClo14 : 65030≤C := by rw [hC]; omega
            have hmul : 260120≤4*C := Nat.mul_le_mul_left 4 hClo14
            omega
        · have hLval : L=215004 := by
            have hBval : B=28656 := by rw [hrEq] at hDy; omega
            have hDval : D=200673 := by rw [hBval] at hMass; omega
            rw [hL,hBval,hDval]
          rcases huCases with hu1 | hu2
          · rw [hu1] at hInv
            have hCeq : C=107502 := by omega
            rw [hC] at hCeq
            omega
          · rw [hu2] at hInv
            have hClo14 : 65030≤C := by rw [hC]; omega
            have hmul : 260120≤4*C := Nat.mul_le_mul_left 4 hClo14
            omega
      · by_cases hn15 : n=15
        · subst n
          have hBfactor : B+12=4*(B/4+3) := by omega
          have hprod : 2^r*(B+12)=4*(2^r*(B/4+3)) := by rw [hBfactor]; ac_rfl
          rw [hP,hprod] at hDy
          omega
        · by_cases hn16 : n=16
          · subst n
            have hBfactor : B+12=4*(B/4+3) := by omega
            have hpowFactor : 2^r=4*2^(r-2) := by
              have heq : 2+(r-2)=r := by omega
              calc
                2^r = 2^(2+(r-2)) := by rw [heq]
                _ = 2^2*2^(r-2) := by rw [Nat.pow_add]
                _ = 4*2^(r-2) := by rw [show (2:Nat)^2=4 by decide]
            have hprod : 2^r*(B+12)=16*(2^(r-2)*(B/4+3)) := by
              rw [hpowFactor,hBfactor]
              calc
                (4*2^(r-2))*(4*(B/4+3)) = (4*4)*(2^(r-2)*(B/4+3)) := by ac_rfl
                _ = 16*(2^(r-2)*(B/4+3)) := by omega
            rw [hP,hprod] at hDy
            omega
          · by_cases hn17 : n=17
            · subst n
              have hBfactor : B+12=4*(B/4+3) := by omega
              have hprod : 2^r*(B+12)=4*(2^r*(B/4+3)) := by rw [hBfactor]; ac_rfl
              rw [hP,hprod] at hDy
              omega
            · have hn18 : 18≤n := by omega
              have hbig : 149790*n+583132<34*P := by
                have haux := linear34_pow18 n hn18
                rw [← hP] at haux
                exact haux
              have hLupper : 8*L≤32*C := by
                have hpowu : 2^u≤4 := by
                  rcases huCases with h | h <;> simp [h]
                have hmul := Nat.mul_le_mul_right C hpowu
                have hL4 : L≤4*C := by rw [hInv]; exact hmul
                calc
                  8*L≤8*(4*C) := Nat.mul_le_mul_left 8 hL4
                  _ =32*C := by omega
              have hCupper32 : 32*C≤64*P+149760*n+583104 := by omega
              omega

end BB6.Agent43FourResetCore
