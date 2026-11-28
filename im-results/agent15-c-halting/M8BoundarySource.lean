import M8DeepThin
import Lean.Elab.Tactic.Omega

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace BB6.Agent15Research

/-- Q_m = 1+4+...+4^m, written recursively to avoid Nat division. -/
def m8BoundaryQ : Nat → Nat
  | 0 => 1
  | n+1 => 4*m8BoundaryQ n+1

theorem m8BoundaryQ_three (m : Nat) :
    3*m8BoundaryQ m+1=4^(m+1) := by
  induction m with
  | zero => decide
  | succ m ih =>
      change 3*(4*m8BoundaryQ m+1)+1=4^((m+1)+1)
      calc
        3*(4*m8BoundaryQ m+1)+1 = 4*(3*m8BoundaryQ m+1) := by omega
        _ = 4*4^(m+1) := by rw [ih]
        _ = 4^(m+1)*4 := by ac_rfl
        _ = 4^((m+1)+1) := (Nat.pow_succ 4 (m+1)).symm

theorem m8BoundaryPowDouble (n : Nat) :
    2^(2*n)=4^n := by
  induction n with
  | zero => decide
  | succ n ih =>
      calc
        2^(2*(n+1)) = 2^(2*n+2) := by congr 1 <;> omega
        _ = 2^(2*n)*2^2 := by rw [Nat.pow_add]
        _ = 4^n*4 := by rw [ih]
        _ = 4^(n+1) := (Nat.pow_succ 4 n).symm

theorem m8BoundaryBQ (m : Nat) :
    2^(2*m+2)=3*m8BoundaryQ m+1 := by
  have hp := m8BoundaryPowDouble (m+1)
  have h3 := m8BoundaryQ_three m
  rw [show 2*m+2=2*(m+1) by omega, hp, h3]

theorem m8BoundaryQ_lower (m : Nat) (hm : 1≤m) :
    m+2≤m8BoundaryQ m := by
  induction m with
  | zero => omega
  | succ m ih =>
      by_cases h0 : m=0
      · subst m
        decide
      · have hi := ih (Nat.one_le_iff_ne_zero.mpr h0)
        simp only [m8BoundaryQ]
        omega

theorem m8BoundaryQ_mod8 (m : Nat) (hm : 1≤m) :
    m8BoundaryQ m%8=5 := by
  cases m with
  | zero => omega
  | succ n =>
      cases n with
      | zero => decide
      | succ n =>
          simp only [m8BoundaryQ]
          omega

/-- The compact boundary quotient D_m = Q_m-m. -/
def m8BoundaryD (m : Nat) : Nat := m8BoundaryQ m-m

/-- High stopping index at the first deep boundary d=2m+2. -/
def m8BoundaryJThin (m : Nat) : Nat := 3*m8BoundaryD m-2

/-- Exact corresponding second stopping right counter. -/
def m8BoundaryKThin (m : Nat) : Nat :=
    3*m8BoundaryD m*2^(2*m+2)-2

theorem m8BoundaryD_eq (m : Nat) (hm : 1≤m) :
    m+m8BoundaryD m=m8BoundaryQ m := by
  have h := m8BoundaryQ_lower m hm
  dsimp [m8BoundaryD]
  omega

/-- For m=3 mod 8 the normalized quotient coordinate is exactly 2 mod 8. -/
theorem m8BoundaryD_mod8 (m : Nat) (hm8 : m%8=3) :
    m8BoundaryD m%8=2 := by
  have hq := m8BoundaryQ_mod8 m (by omega)
  have hl := m8BoundaryQ_lower m (by omega)
  dsimp [m8BoundaryD]
  omega

theorem m8BoundaryJThin_plus (m : Nat) (hm8 : m%8=3) :
    m8BoundaryJThin m+3=3*m8BoundaryD m+1 := by
  have hl := m8BoundaryQ_lower m (by omega)
  have hd : 2≤m8BoundaryD m := by
    dsimp [m8BoundaryD]
    omega
  dsimp [m8BoundaryJThin]
  omega

theorem m8BoundaryKThin_plus (m : Nat) (hm8 : m%8=3) :
    m8BoundaryKThin m+2=3*m8BoundaryD m*2^(2*m+2) := by
  have hdmod := m8BoundaryD_mod8 m hm8
  have hp : 1≤2^(2*m+2) := Nat.pow_pos (by decide)
  have hd : 2≤m8BoundaryD m := by omega
  have hprod : 2≤m8BoundaryD m*2^(2*m+2) :=
    Nat.mul_le_mul hd hp
  have h6 : 6≤3*m8BoundaryD m*2^(2*m+2) := by
    have h := Nat.mul_le_mul_left 3 hprod
    simpa [Nat.mul_assoc] using h
  dsimp [m8BoundaryKThin]
  omega

/-- Exact second-stopping Diophantine identity for the new closed-form family. -/
theorem m8Boundary_stop (m : Nat) (hm8 : m%8=3) :
    m8BoundaryKThin m+m8BoundaryJThin m+3*m+5 =
      2^(2*m+2)*(m8BoundaryJThin m+3) := by
  let d := m8BoundaryD m
  let b := 2^(2*m+2)
  have hd : m+d=m8BoundaryQ m := by
    simpa [d] using m8BoundaryD_eq m (by omega)
  have hb : b=3*m8BoundaryQ m+1 := by
    simpa [b] using m8BoundaryBQ m
  have hj : m8BoundaryJThin m+3=3*d+1 := by
    simpa [d] using m8BoundaryJThin_plus m hm8
  have hk : m8BoundaryKThin m+2=3*d*b := by
    simpa [d,b] using m8BoundaryKThin_plus m hm8
  have hcore : 3*d*b+3*d+3*m+1=b*(3*d+1) := by
    calc
      3*d*b+3*d+3*m+1 = 3*d*b+3*(m+d)+1 := by omega
      _ = 3*d*b+(3*m8BoundaryQ m+1) := by rw [hd]; ac_rfl
      _ = 3*d*b+b := by rw [hb]
      _ = b*(3*d+1) := by
        simp only [Nat.mul_add,Nat.mul_one]
        ac_rfl
  calc
    m8BoundaryKThin m+m8BoundaryJThin m+3*m+5 =
        (m8BoundaryKThin m+2)+(m8BoundaryJThin m+3)+3*m := by omega
    _ = 3*d*b+(3*d+1)+3*m := by rw [hk,hj]
    _ = 3*d*b+3*d+3*m+1 := by omega
    _ = b*(3*d+1) := hcore
    _ = b*(m8BoundaryJThin m+3) := by rw [hj]
    _ = 2^(2*m+2)*(m8BoundaryJThin m+3) := by rfl

/-- New source-linked infinite Machine-C exclusion at the exact deep boundary.
    Every m=3 mod 8 yields a genuine second stopping parameter which cannot
    occur on the authentic blank-origin section orbit. -/
theorem m8Boundary_unreachable_thin (m : Nat) (hm8 : m%8=3) :
    ¬ BB6.Agent15.CReach
      (2*m8BoundaryJThin m+3) (m8BoundaryKThin m) := by
  have hm : m%2=1 := by omega
  have hdmod := m8BoundaryD_mod8 m hm8
  have hj2 : m8BoundaryJThin m%2=0 := by
    have hj := m8BoundaryJThin_plus m hm8
    omega
  have hs : (m8BoundaryJThin m+m)%4=3 := by
    have hj := m8BoundaryJThin_plus m hm8
    have hd4 : m8BoundaryD m%4=2 := by omega
    omega
  have hscale :
      m8BoundaryKThin m+2 =
        3*m8BoundaryD m*2^(2*m+2) :=
    m8BoundaryKThin_plus m hm8
  have hpar : 2*(2*m+2)%4=(m+1)%4 := by omega
  exact deep_no_root_of_data_thin
    (m8BoundaryJThin m) m (m8BoundaryKThin m)
    (2*m+2) (m8BoundaryD m)
    hm hj2 hs (m8Boundary_stop m hm8) hscale hdmod hpar

/-- The source exclusion occurs at arbitrarily large stopping-family
    parameters; choosing m=8L+3 gives an explicit witness above any bound. -/
theorem m8Boundary_unbounded_parameter (L : Nat) :
    ∃ m, L≤m ∧ m%8=3 ∧
      ¬ BB6.Agent15.CReach
        (2*m8BoundaryJThin m+3) (m8BoundaryKThin m) := by
  refine ⟨8*L+3, by omega, by omega, ?_⟩
  exact m8Boundary_unreachable_thin (8*L+3) (by omega)

#print axioms m8Boundary_stop
#print axioms m8Boundary_unreachable_thin
#print axioms m8Boundary_unbounded_parameter

end BB6.Agent15Research
