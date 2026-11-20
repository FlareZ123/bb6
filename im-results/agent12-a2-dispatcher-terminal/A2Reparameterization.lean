import S1Encoder
import Lean.Elab.Tactic.Omega

/-!
# A=2 q4-tail residual as a canonical S1 reset input

Source-only draft. This module proves the two BinDec factorizations and
the resulting full left-facing list equality used in
`im-results/agent12-a2-dispatcher-terminal/README.md`.
It has not been compiled in this invocation.
-/

namespace BB6Coverage.Agent12A2Reparam

open BB6Coverage.Agent8S1Encoder

/-- The maximal counter value is encoded by a full run of d0 blocks. -/
theorem binDec_max (k : Nat) :
    binDec k (2^k - 1) = d0pow k := by
  induction k with
  | zero =>
      simp [binDec, binaryCounterFuel, d0pow]
  | succ k ih =>
      have hk : 2^k - 1 < 2^k := by omega
      have hpos : 0 < 2^k := Nat.pow_pos (by decide)
      have hpow : 2^(k+1) = 2*2^k := by
        rw [Nat.pow_succ]
        omega
      have hnum : 2^(k+1) - 1 = 2*(2^k - 1) + 1 := by
        omega
      calc
        binDec (k+1) (2^(k+1) - 1)
            = d0 ++ binDec k (2^k - 1) := by
                rw [hnum]
                exact binDec_odd k (2^k - 1) hk
        _ = d0pow (k+1) := by
              simp [d0pow, ih]

/-- The width-(L+4) encoding of 2^(L+4)-7 has the A=2 carry prefix. -/
theorem binDec_addFour_subSeven (L : Nat) :
    binDec (L+4) (2^(L+4)-7) =
      d0 ++ d1 ++ d1 ++ d0pow (L+1) := by
  have hp0 : 8 ≤ 2^(L+3) := by
    have h := Nat.pow_le_pow_right (show 0 < 2 by decide)
      (show 3 ≤ L+3 by omega)
    simpa using h
  have hp1 : 4 ≤ 2^(L+2) := by
    have h := Nat.pow_le_pow_right (show 0 < 2 by decide)
      (show 2 ≤ L+2 by omega)
    simpa using h
  have hp2 : 2 ≤ 2^(L+1) := by
    have h := Nat.pow_le_pow_right (show 0 < 2 by decide)
      (show 1 ≤ L+1 by omega)
    simpa using h
  have h0pow : 2^(L+4) = 2*2^(L+3) := by
    rw [show L+4 = (L+3)+1 by omega, Nat.pow_succ]
    omega
  have h1pow : 2^(L+3) = 2*2^(L+2) := by
    rw [show L+3 = (L+2)+1 by omega, Nat.pow_succ]
    omega
  have h2pow : 2^(L+2) = 2*2^(L+1) := by
    rw [show L+2 = (L+1)+1 by omega, Nat.pow_succ]
    omega
  have h0 : 2^(L+4)-7 = 2*(2^(L+3)-4)+1 := by
    omega
  have h1 : 2^(L+3)-4 = 2*(2^(L+2)-2) := by
    omega
  have h2 : 2^(L+2)-2 = 2*(2^(L+1)-1) := by
    omega
  have hb0 : 2^(L+3)-4 < 2^(L+3) := by omega
  have hb1 : 2^(L+2)-2 < 2^(L+2) := by omega
  have hb2 : 2^(L+1)-1 < 2^(L+1) := by omega
  calc
    binDec (L+4) (2^(L+4)-7)
        = d0 ++ binDec (L+3) (2^(L+3)-4) := by
            rw [show L+4 = (L+3)+1 by omega, h0]
            exact binDec_odd (L+3) (2^(L+3)-4) hb0
    _ = d0 ++ d1 ++ binDec (L+2) (2^(L+2)-2) := by
            rw [h1, show L+3 = (L+2)+1 by omega]
            rw [binDec_even (L+2) (2^(L+2)-2) hb1]
            simp [List.append_assoc]
    _ = d0 ++ d1 ++ d1 ++ binDec (L+1) (2^(L+1)-1) := by
            rw [h2, show L+2 = (L+1)+1 by omega]
            rw [binDec_even (L+1) (2^(L+1)-1) hb2]
            simp [List.append_assoc]
    _ = d0 ++ d1 ++ d1 ++ d0pow (L+1) := by
            rw [binDec_max]

/-- Carry-prefix identity for the q4 sweep's all-ones low counter. -/
theorem binDec_lowCarry (K n : Nat) (hK : 0 < K) (hn : 0 < n) :
    binDec (K+n-1) (2^(n-1)-1) =
      d0pow (n-1) ++ d1pow K := by
  have hwidth : K+n-1 = (K-1)+1+(n-1) := by omega
  have hvalue : 2^(n-1)-1 = ((2*0+1)*2^(n-1))-1 := by omega
  calc
    binDec (K+n-1) (2^(n-1)-1)
        = binDec ((K-1)+1+(n-1)) (((2*0+1)*2^(n-1))-1) := by
            rw [hwidth, hvalue]
    _ = d0pow (n-1) ++ d1 ++ binDec (K-1) 0 :=
          binDec_sub_one_carryPrefix (K-1) 0 (n-1) (by
            have hpos : 0 < 2^(K-1) := Nat.pow_pos (by decide)
            omega)
    _ = d0pow (n-1) ++ d1pow K := by
          rw [binDec_zero]
          have hK' : K = (K-1)+1 := by omega
          rw [hK']
          rfl

/-- The exact A=2 S1 context after the two low d0/d1 blocks. -/
theorem a2Context_eq (L : Nat) :
    markerWord 0 ++ d0 ++ binDec (L+4) (2^(L+4)-7) ++ lh =
      markerWord 0 ++ d0pow 2 ++ d1pow 2 ++ d0pow (L+1) ++ lh := by
  rw [binDec_addFour_subSeven]
  simp [d0pow, d1pow, List.append_assoc]

/-- The A=2 residual list before the q4 sweep counter is prepended. -/
def a2Ell (L K : Nat) : List Bool :=
  d1pow K ++ markerWord 0 ++ d0pow 2 ++ d1pow 2
    ++ d0pow (L+1) ++ lh

/-- Full left-facing equality: the q4Tail S0 frame is a canonical
S1 configuration with width L+4 and outer index 2^(L+4)-7. -/
theorem a2FullLeftFacing_eq (L K n : Nat) (hK : 0 < K) (hn : 0 < n) :
    binDec (n-1) (2^(n-1)-1) ++ a2Ell L K =
      binDec (K+n-1) (2^(n-1)-1) ++
        markerWord 0 ++ d0 ++ binDec (L+4) (2^(L+4)-7) ++ lh := by
  calc
    binDec (n-1) (2^(n-1)-1) ++ a2Ell L K
        = d0pow (n-1) ++ d1pow K ++ markerWord 0
            ++ d0pow 2 ++ d1pow 2 ++ d0pow (L+1) ++ lh := by
              simp [a2Ell, binDec_max, List.append_assoc]
    _ = d0pow (n-1) ++ d1pow K ++ markerWord 0
          ++ d0 ++ binDec (L+4) (2^(L+4)-7) ++ lh := by
              rw [← a2Context_eq L]
              simp [List.append_assoc]
    _ = binDec (K+n-1) (2^(n-1)-1) ++
          markerWord 0 ++ d0 ++ binDec (L+4) (2^(L+4)-7) ++ lh := by
              rw [binDec_lowCarry K n hK hn]
              simp [List.append_assoc]

end BB6Coverage.Agent12A2Reparam
