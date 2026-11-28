import M8GenericHigh
import Lean.Elab.Tactic.Omega
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace BB6.Agent15Research
open BB6.Agent29Depth

/-- For positive m, the M8 geometric quotient dominates the small linear
    correction needed by the boundary-depth construction. -/
theorem m8BoundaryQ_lower (m : Nat) (hm : 1≤m) :
    m+2≤allOddQ m := by
  induction m with
  | zero => omega
  | succ m ih =>
      by_cases hm0 : m=0
      · subst m
        decide
      · have hm1 : 1≤m := Nat.one_le_iff_ne_zero.mpr hm0
        have hi := ih hm1
        dsimp [allOddQ] at hi
        change m+1+2 ≤ m8Geom4 (m+1+1)
        change m+1+2 ≤ 4*m8Geom4 (m+1)+1
        omega

/-- From the second geometric term onward Q=1+4+... is 5 modulo 8. -/
theorem m8BoundaryQ_mod8 (m : Nat) (hm : 1≤m) :
    allOddQ m%8=5 := by
  obtain ⟨n,rfl⟩ : ∃n,m=n+1 := ⟨m-1,by omega⟩
  change m8Geom4 (n+1+1)%8=5
  change (4*(4*m8Geom4 n+1)+1)%8=5
  omega

/-- Boundary-depth M8 quotient parameter. -/
def m8BoundaryT (m : Nat) : Nat := (allOddQ m-m-2)/8

/-- Boundary-depth high stopping index. -/
def m8BoundaryJ (m : Nat) : Nat := 3*(allOddQ m-m)-2

/-- The quotient coordinate is exactly Q-m when m=3 mod 8. -/
theorem m8BoundaryV (m : Nat) (hm8 : m%8=3) :
    2+8*m8BoundaryT m=allOddQ m-m := by
  have hm : 1≤m := by omega
  have hlow := m8BoundaryQ_lower m hm
  have hq8 := m8BoundaryQ_mod8 m hm
  have hz : (allOddQ m-m-2)%8=0 := by omega
  have hd : 8∣allOddQ m-m-2 := Nat.dvd_of_mod_eq_zero hz
  have heq := Nat.div_mul_cancel hd
  dsimp [m8BoundaryT]
  rw [Nat.mul_comm] at heq
  omega

theorem m8BoundaryJ_plus (m : Nat) (hm8 : m%8=3) :
    m8BoundaryJ m+3=3*(allOddQ m-m)+1 := by
  have hlow := m8BoundaryQ_lower m (by omega)
  dsimp [m8BoundaryJ]
  omega

/-- Closed Diophantine solution at the first depth d=2m+2 beyond the
    previously explicit shallow all-odd construction. -/
theorem m8Boundary_diophantine (m : Nat) (hm8 : m%8=3) :
    allOddQ m*(m8BoundaryJ m+3)=
      m+2^(2*m+2)*(2+8*m8BoundaryT m) := by
  let Q := allOddQ m
  let D := Q-m
  have hlow : m+2≤Q := m8BoundaryQ_lower m (by omega)
  have hv : 2+8*m8BoundaryT m=D := by
    simpa [Q,D] using m8BoundaryV m hm8
  have hj : m8BoundaryJ m+3=3*D+1 := by
    simpa [Q,D] using m8BoundaryJ_plus m hm8
  have hB := allOdd_BQ m
  have hpow : 2^(2*m+2)=3*Q+1 := by
    simpa [allOddB,Q] using hB
  have hsplit : m+D=Q := by
    dsimp [D,Q]
    omega
  rw [hj,hpow,hv]
  calc
    Q*(3*D+1)=3*Q*D+Q := by
      simp only [Nat.mul_add,Nat.mul_one]
      ac_rfl
    _=3*Q*D+(m+D) := by rw [hsplit]
    _=m+(3*Q+1)*D := by
      simp only [Nat.add_mul,Nat.one_mul]
      ac_rfl

/-- New explicit infinite boundary-depth family: every m=3 mod 8 gives an
    exact high stopping target excluded from the authentic blank-origin
    Machine-C orbit by the M8 quotient theorem. -/
theorem m8Boundary_unreachable (m : Nat) (hm8 : m%8=3) :
    ¬ BB6.Agent15.CReach
      (2*m8BoundaryJ m+3)
      (3*2^(2*m+2)*(2+8*m8BoundaryT m)-2) := by
  have hm : m%2=1 := by omega
  have hpar : 2*(2*m+2)%4=(m+1)%4 := by omega
  exact high_m8_diophantine_exclusion
    m (2*m+2) (m8BoundaryT m) (m8BoundaryJ m)
    hm (by omega) hpar (m8Boundary_diophantine m hm8)

#print axioms m8Boundary_diophantine
#print axioms m8Boundary_unreachable
end BB6.Agent15Research
