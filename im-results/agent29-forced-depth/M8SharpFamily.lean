/-!
Intermediate Lean draft; not yet locally compiled or accepted by source CI.

This file composes the generic source-level M8 parity exclusion from
M8FilteredResidual.lean with an explicit division-free parametrization of
the dyadic sharp family. The target is m8SharpFamily_unreachable for every
r >= 2. Keep this file in im-results until local Lean 4.36.0-rc2 preflight
and the manual Agent15 source workflow both succeed.
-/

import M8FilteredResidual
import Lean.Elab.Tactic.Omega

namespace BB6.Agent29Depth

/-- The geometric sum 1+4+...+4^(n-1), used to write the dyadic
    sharp family without natural-number division. -/
def m8Geom4 : Nat → Nat
  | 0 => 0
  | n+1 => 4*m8Geom4 n + 1

theorem m8Geom4_three (n : Nat) : 3*m8Geom4 n+1=4^n := by
  induction n with
  | zero => rfl
  | succ n ih =>
      simp only [m8Geom4, Nat.pow_succ]
      omega

theorem m8Geom4_add (a b : Nat) :
    m8Geom4 (a+b)=m8Geom4 a+4^a*m8Geom4 b := by
  induction a with
  | zero => simp [m8Geom4]
  | succ a ih =>
      simp only [Nat.succ_add, m8Geom4, Nat.pow_succ]
      rw [ih, Nat.mul_add]
      ac_rfl

theorem m8Geom4_ge (n : Nat) : n≤m8Geom4 n := by
  induction n with
  | zero => simp [m8Geom4]
  | succ n ih =>
      simp only [m8Geom4]
      omega

theorem m8Geom4_mod_four (n : Nat) (hn : 1≤n) :
    m8Geom4 n%4=1 := by
  cases n with
  | zero => omega
  | succ n =>
      simp only [m8Geom4]
      omega

theorem m8PowTwoDouble (n : Nat) : 2^(2*n)=4^n := by
  induction n with
  | zero => decide
  | succ n ih =>
      have he : 2*(n+1)=2*n+2 := by omega
      rw [he, Nat.pow_add]
      simp only [show (2:Nat)^2=4 by decide]
      rw [ih, Nat.pow_succ]

/-- Dyadic sharp-family parameters: m=(4^r-1)/3, L=m+1, and
    N=L-r. -/
def m8SharpM (r : Nat) : Nat := m8Geom4 r
def m8SharpL (r : Nat) : Nat := m8SharpM r+1
def m8SharpN (r : Nat) : Nat := m8SharpL r-r
def m8SharpW (r : Nat) : Nat := m8Geom4 (m8SharpN r)
def m8SharpT (r : Nat) : Nat := 2*r-1
def m8SharpD (r : Nat) : Nat := m8SharpT r+2*m8SharpL r
def m8SharpV (r : Nat) : Nat := 2*m8SharpW r
def m8SharpJ (r : Nat) : Nat :=
  3*m8SharpV r*2^(m8SharpT r)-2
def m8SharpK (r : Nat) : Nat :=
  3*m8SharpV r*2^(m8SharpD r)-2

theorem m8SharpN_pos (r : Nat) (hr : 2≤r) :
    1≤m8SharpN r := by
  have h := m8Geom4_ge r
  dsimp [m8SharpN, m8SharpL, m8SharpM]
  omega

theorem m8SharpL_decomp (r : Nat) :
    r+m8SharpN r=m8SharpL r := by
  have h := m8Geom4_ge r
  dsimp [m8SharpN, m8SharpL, m8SharpM]
  omega

theorem m8SharpM_mod_four (r : Nat) (hr : 1≤r) :
    m8SharpM r%4=1 := by
  have h := m8Geom4_mod_four r hr
  simpa [m8SharpM] using h

theorem m8SharpW_mod_four (r : Nat) (hr : 2≤r) :
    m8SharpW r%4=1 := by
  exact m8Geom4_mod_four (m8SharpN r) (m8SharpN_pos r hr)

theorem m8SharpV_mod_eight (r : Nat) (hr : 2≤r) :
    m8SharpV r%8=2 := by
  have hw := m8SharpW_mod_four r hr
  dsimp [m8SharpV]
  omega

theorem m8SharpMass (r : Nat) (hr : 2≤r) :
    m8SharpV r*2^(m8SharpT r)=
      m8Geom4 (m8SharpL r)-m8SharpM r := by
  have hN := m8SharpN_pos r hr
  have hL := m8SharpL_decomp r
  have hadd := m8Geom4_add r (m8SharpN r)
  rw [hL] at hadd
  have hdiff :
      m8Geom4 (m8SharpL r)-m8SharpM r =
        4^r*m8SharpW r := by
    dsimp [m8SharpM, m8SharpW]
    omega
  have ht : m8SharpT r+1=2*r := by
    dsimp [m8SharpT]
    omega
  have hpow : 2^(m8SharpT r)*2=4^r := by
    calc
      2^(m8SharpT r)*2 = 2^(m8SharpT r+1) := by
        symm
        exact Nat.pow_succ 2 (m8SharpT r)
      _ = 2^(2*r) := by rw [ht]
      _ = 4^r := m8PowTwoDouble r
  calc
    m8SharpV r*2^(m8SharpT r)
        = (2*m8SharpW r)*2^(m8SharpT r) := rfl
    _ = m8SharpW r*(2^(m8SharpT r)*2) := by ac_rfl
    _ = m8SharpW r*4^r := by rw [hpow]
    _ = 4^r*m8SharpW r := by ac_rfl
    _ = m8Geom4 (m8SharpL r)-m8SharpM r := hdiff.symm

theorem m8SharpMain (r : Nat) (hr : 2≤r) :
    3*m8SharpV r*2^(m8SharpT r)+4^r =
      4^(m8SharpL r) := by
  have hm := m8Geom4_three r
  have hq := m8Geom4_three (m8SharpL r)
  have hmass := m8SharpMass r hr
  have hmass3 :
      3*m8SharpV r*2^(m8SharpT r) =
        3*(m8Geom4 (m8SharpL r)-m8SharpM r) := by
    calc
      3*m8SharpV r*2^(m8SharpT r)
          = 3*(m8SharpV r*2^(m8SharpT r)) := by ac_rfl
      _ = 3*(m8Geom4 (m8SharpL r)-m8SharpM r) := by rw [hmass]
  dsimp [m8SharpM] at hm
  omega

theorem m8SharpStop (r : Nat) (hr : 2≤r) :
    m8SharpK r+m8SharpJ r+3*m8SharpM r+5 =
      2^(2*m8SharpM r+2)*(m8SharpJ r+3) := by
  have hm : 3*m8SharpM r+1=4^r := by
    simpa [m8SharpM] using m8Geom4_three r
  have hmain := m8SharpMain r hr
  have hsum :
      3*m8SharpV r*2^(m8SharpT r)+3*m8SharpM r+1 =
        4^(m8SharpL r) := by omega
  have hpow : 2^(2*m8SharpM r+2)=4^(m8SharpL r) := by
    have he : 2*m8SharpM r+2=2*m8SharpL r := by
      dsimp [m8SharpL]
      omega
    rw [he, m8PowTwoDouble]
  have hfactor :
      3*m8SharpV r*2^(m8SharpD r) =
        4^(m8SharpL r)*(3*m8SharpV r*2^(m8SharpT r)) := by
    dsimp [m8SharpD]
    rw [Nat.pow_add, m8PowTwoDouble]
    ac_rfl
  have hvpos : 2≤m8SharpV r := by
    have h := m8SharpV_mod_eight r hr
    omega
  have htpos : 1≤2^(m8SharpT r) := by
    have h := Nat.pow_pos (by decide : 0 < (2:Nat)) (m8SharpT r)
    omega
  have hdpos : 1≤2^(m8SharpD r) := by
    have h := Nat.pow_pos (by decide : 0 < (2:Nat)) (m8SharpD r)
    omega
  have hj : m8SharpJ r+3 =
      3*m8SharpV r*2^(m8SharpT r)+1 := by
    have hp : 2≤3*m8SharpV r*2^(m8SharpT r) := by
      have hmul := Nat.mul_le_mul hvpos htpos
      omega
    dsimp [m8SharpJ]
    omega
  have hk : m8SharpK r+2 =
      3*m8SharpV r*2^(m8SharpD r) := by
    have hp : 2≤3*m8SharpV r*2^(m8SharpD r) := by
      have hmul := Nat.mul_le_mul hvpos hdpos
      omega
    dsimp [m8SharpK]
    omega
  calc
    m8SharpK r+m8SharpJ r+3*m8SharpM r+5 =
        (m8SharpK r+2)+(m8SharpJ r+3)+3*m8SharpM r := by omega
    _ = 4^(m8SharpL r)*(3*m8SharpV r*2^(m8SharpT r))+
        3*m8SharpV r*2^(m8SharpT r)+3*m8SharpM r+1 := by
          rw [hk, hj, hfactor]
    _ = 4^(m8SharpL r)*(3*m8SharpV r*2^(m8SharpT r)+1) := by
          rw [Nat.mul_add]
          omega
    _ = 2^(2*m8SharpM r+2)*(m8SharpJ r+3) := by
          rw [hpow, hj]

/-- The all-depth oddDepth counter agrees with the explicit family depth:
    k+2=3*v*2^d and v=2 (mod 4) force exactly d affine steps. -/
theorem m8OddDepth_scaled (v d : Nat) (hv : v%4=2) :
    BB6.Agent15.oddDepth (3*v*2^d-2)=d := by
  induction d with
  | zero =>
      have hnot : ¬(4≤3*v-2 ∧ (3*v-2)%4=2) := by omega
      simp [BB6.Agent15.oddDepth, hnot]
  | succ d ih =>
      have hv2 : 2≤v := by omega
      have hpowPos : 1≤2^d := by
        have hp := Nat.pow_pos (by decide : 0 < (2:Nat)) d
        omega
      have hpow2 : 2≤2^(d+1) := by
        rw [Nat.pow_succ]
        omega
      have hmul : 4≤v*2^(d+1) := Nat.mul_le_mul hv2 hpow2
      have hmul3 : 12≤3*v*2^(d+1) := by
        have h := Nat.mul_le_mul_left 3 hmul
        simpa [Nat.mul_assoc] using h
      have hkpos : 4≤3*v*2^(d+1)-2 := by omega
      have hvEven : v%2=0 := by omega
      have hfactor : 3*v*2^(d+1)=2*(3*v*2^d) := by
        rw [Nat.pow_succ]
        ac_rfl
      have hmul0 : 2≤v*2^d := Nat.mul_le_mul hv2 hpowPos
      have hmul0' : 6≤3*v*2^d := by
        have h := Nat.mul_le_mul_left 3 hmul0
        simpa [Nat.mul_assoc] using h
      have hzEven : (3*v*2^d)%2=0 := by
        simp [Nat.mul_mod, hvEven]
      have hkmod : (3*v*2^(d+1)-2)%4=2 := by
        rw [hfactor]
        omega
      have hstep :
          ((3*v*2^(d+1)-2)-2)/2=3*v*2^d-2 := by
        rw [hfactor]
        omega
      rw [BB6.Agent15.oddDepth, dif_pos ⟨hkpos,hkmod⟩, hstep, ih]
      omega

/-- An explicit infinite family of authentic second-family stopping inputs
    is excluded by the original-source M8 quotient theorem. -/
theorem m8SharpFamily_unreachable (r : Nat) (hr : 2≤r) :
    ¬ BB6.Agent15.CReach
      (2*m8SharpJ r+3) (m8SharpK r) := by
  let j := m8SharpJ r
  let m := m8SharpM r
  let k := m8SharpK r
  let v := m8SharpV r
  let d := m8SharpD r
  have hm4 : m%4=1 := by
    simpa [m] using m8SharpM_mod_four r (by omega)
  have hm : m%2=1 := by omega
  have hv8 : v%8=2 := by
    simpa [v] using m8SharpV_mod_eight r hr
  have hv4 : v%4=2 := by omega
  have ht : 2≤m8SharpT r := by
    dsimp [m8SharpT]
    omega
  have hpowdiv : 4∣2^(m8SharpT r) := by
    obtain ⟨q,hq⟩ : ∃q, m8SharpT r=2+q :=
      ⟨m8SharpT r-2,by omega⟩
    refine ⟨2^q,?_⟩
    rw [hq, Nat.pow_add]
    simp
  have hproddiv : 4∣3*m8SharpV r*2^(m8SharpT r) := by
    rcases hpowdiv with ⟨q,hq⟩
    refine ⟨3*m8SharpV r*q,?_⟩
    rw [hq]
    ac_rfl
  have hj4 : j%4=2 := by
    rcases hproddiv with ⟨q,hq⟩
    dsimp [j,m8SharpJ]
    omega
  have hj : j%2=0 := by omega
  have hs : (j+m)%4=3 := by omega
  have hstop := m8SharpStop r hr
  have hdepth : BB6.Agent15.oddDepth k=d := by
    simpa [k,d,v,m8SharpK,m8SharpD,m8SharpV] using
      m8OddDepth_scaled (m8SharpV r) (m8SharpD r) hv4
  have hdeep := BB6.Agent15.second_halt_deep_sector j m k hstop hj hm hs
  let p := BB6.Agent15.affineNormalize (2*j+3) k
  have hscale :
      2^(BB6.Agent15.oddDepth k)*(p.2+2)=k+2 := by
    simpa [p] using hdeep.2.2.2.2
  have hscale' : 2^d*(p.2+2)=k+2 := by
    rw [hdepth] at hscale
    exact hscale
  have hvpos : 2≤m8SharpV r := by
    have h := m8SharpV_mod_eight r hr
    omega
  have hdpos : 1≤2^(m8SharpD r) := by
    have h := Nat.pow_pos (by decide : 0 < (2:Nat)) (m8SharpD r)
    omega
  have hmulD : 2≤m8SharpV r*2^(m8SharpD r) :=
    Nat.mul_le_mul hvpos hdpos
  have hmulD3 : 2≤3*m8SharpV r*2^(m8SharpD r) := by
    have h := Nat.mul_le_mul_left 3 hmulD
    have heq : 3*(m8SharpV r*2^(m8SharpD r)) =
        3*m8SharpV r*2^(m8SharpD r) := by ac_rfl
    rw [heq] at h
    omega
  have hscaleFamily : 2^d*(3*v)=k+2 := by
    dsimp [k,d,v,m8SharpK,m8SharpD,m8SharpV]
    rw [Nat.sub_add_cancel hmulD3]
    ac_rfl
  have hY : p.2+2=3*v := by
    apply Nat.mul_left_cancel (Nat.pow_pos (by decide : 0 < (2:Nat)) d)
    calc
      2^d*(p.2+2)=k+2 := hscale'
      _ =2^d*(3*v) := hscaleFamily.symm
  have hdiv : (p.2+2)/3=v := by
    rw [hY]
    omega
  have hdodd : d%2=1 := by
    dsimp [d,m8SharpD,m8SharpT,m8SharpL]
    omega
  have hsecond :
      2*BB6.Agent15.oddDepth k%4=(m+1)%4 := by
    rw [hdepth]
    omega
  intro hroot
  have hnot := BB6.Agent29Depth.second_deep_root_m8_parity_exclusion
    j m k hstop hj hm hs hroot
  apply hnot
  constructor
  · simpa [p,hdiv] using hv8
  · exact hsecond

#print axioms m8SharpFamily_unreachable
end BB6.Agent29Depth
