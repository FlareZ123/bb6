import M8BoundarySource
import Lean.Elab.Tactic.Omega

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace BB6.Agent15Research

/-- Boundary coefficient. For m=3 mod 8 it runs 1,9,17,...; for
    m=7 mod 8 it runs 5,13,21,... . -/
def m8BoundaryCoeff (m s : Nat) : Nat :=
  (if m%8=3 then 1 else 5)+8*s

/-- Normalized M8 quotient coordinate for the complete boundary lattice. -/
def m8BoundaryVLattice (m s : Nat) : Nat :=
  m8BoundaryCoeff m s*m8BoundaryQ m-m

/-- High stopping index at exact affine depth d=2m+2. -/
def m8BoundaryJLattice (m s : Nat) : Nat :=
  m8BoundaryCoeff m s*2^(2*m+2)-(3*m+3)

/-- Corresponding exact second-stopping right counter. -/
def m8BoundaryKLattice (m s : Nat) : Nat :=
  3*m8BoundaryVLattice m s*2^(2*m+2)-2

theorem m8BoundaryCoeff_mod8 (m s : Nat) (hm4 : m%4=3) :
    m8BoundaryCoeff m s%8 =
      (if m%8=3 then 1 else 5) := by
  by_cases h3 : m%8=3
  · simp [m8BoundaryCoeff,h3]
  · have h7 : m%8=7 := by omega
    simp [m8BoundaryCoeff,h3]

theorem m8BoundaryCoeff_pos (m s : Nat) :
    1≤m8BoundaryCoeff m s := by
  unfold m8BoundaryCoeff
  split <;> omega

theorem m8BoundaryVLattice_sum (m s : Nat) (hm4 : m%4=3) :
    m+m8BoundaryVLattice m s =
      m8BoundaryCoeff m s*m8BoundaryQ m := by
  have hm : 1≤m := by omega
  have hQ := m8BoundaryQ_lower m hm
  have hq := m8BoundaryCoeff_pos m s
  have hprod : m≤m8BoundaryCoeff m s*m8BoundaryQ m := by
    have hmul := Nat.mul_le_mul hq hQ
    omega
  dsimp [m8BoundaryVLattice]
  omega

/-- Every boundary lattice quotient coordinate lands in the source-forbidden
    M8 class v=2 mod 8. -/
theorem m8BoundaryVLattice_mod8 (m s : Nat) (hm4 : m%4=3) :
    m8BoundaryVLattice m s%8=2 := by
  have hm : 1≤m := by omega
  have hQ8 := m8BoundaryQ_mod8 m hm
  have hq8 := m8BoundaryCoeff_mod8 m s hm4
  have hsum := m8BoundaryVLattice_sum m s hm4
  have hh := congrArg (fun z : Nat => z%8) hsum
  rw [Nat.add_mod,Nat.mul_mod,hQ8,hq8] at hh
  by_cases h3 : m%8=3
  · rw [if_pos h3] at hh
    omega
  · have h7 : m%8=7 := by omega
    rw [if_neg h3] at hh
    omega

theorem m8BoundaryB_mod8 (m : Nat) (hm4 : m%4=3) :
    2^(2*m+2)%8=0 := by
  have hm : 1≤m := by omega
  have hQ8 := m8BoundaryQ_mod8 m hm
  have hB := m8BoundaryBQ m
  have hh := congrArg (fun z : Nat => z%8) hB
  rw [Nat.add_mod,Nat.mul_mod,hQ8] at hh
  omega

theorem m8BoundaryJLattice_sum (m s : Nat) (hm4 : m%4=3) :
    m8BoundaryJLattice m s+3*m+3 =
      m8BoundaryCoeff m s*2^(2*m+2) := by
  have hm : 1≤m := by omega
  have hQ := m8BoundaryQ_lower m hm
  have hB := m8BoundaryBQ m
  have hq := m8BoundaryCoeff_pos m s
  have hBlow : 3*m+3≤2^(2*m+2) := by
    rw [hB]
    omega
  have hprod : 3*m+3≤m8BoundaryCoeff m s*2^(2*m+2) := by
    have hh := Nat.mul_le_mul hq hBlow
    omega
  dsimp [m8BoundaryJLattice]
  omega

theorem m8BoundaryJLattice_plus3 (m s : Nat) (hm4 : m%4=3) :
    m8BoundaryJLattice m s+3 =
      3*m8BoundaryVLattice m s+m8BoundaryCoeff m s := by
  let q := m8BoundaryCoeff m s
  let Q := m8BoundaryQ m
  let v := m8BoundaryVLattice m s
  let j := m8BoundaryJLattice m s
  have hv : m+v=q*Q := by
    simpa [q,Q,v] using m8BoundaryVLattice_sum m s hm4
  have hB : 2^(2*m+2)=3*Q+1 := by
    simpa [Q] using m8BoundaryBQ m
  have hqB :
      q*2^(2*m+2)=3*(q*Q)+q := by
    rw [hB]
    simp [Nat.mul_add,Nat.mul_assoc,Nat.mul_comm,Nat.mul_left_comm]
  have hj : j+3*m+3=q*2^(2*m+2) := by
    simpa [q,j] using m8BoundaryJLattice_sum m s hm4
  omega

theorem m8BoundaryKLattice_plus2 (m s : Nat) (hm4 : m%4=3) :
    m8BoundaryKLattice m s+2 =
      3*m8BoundaryVLattice m s*2^(2*m+2) := by
  have hv8 := m8BoundaryVLattice_mod8 m s hm4
  have hv : 2≤m8BoundaryVLattice m s := by omega
  have hp : 1≤2^(2*m+2) := Nat.pow_pos (by decide)
  have hprod : 2≤m8BoundaryVLattice m s*2^(2*m+2) :=
    Nat.mul_le_mul hv hp
  have h6 : 6≤3*m8BoundaryVLattice m s*2^(2*m+2) := by
    have hh := Nat.mul_le_mul_left 3 hprod
    simpa [Nat.mul_assoc] using hh
  dsimp [m8BoundaryKLattice]
  omega

/-- Exact second-stopping identity across the entire two-parameter boundary
    lattice, not only the first q-ray. -/
theorem m8BoundaryLattice_stop (m s : Nat) (hm4 : m%4=3) :
    m8BoundaryKLattice m s+m8BoundaryJLattice m s+3*m+5 =
      2^(2*m+2)*(m8BoundaryJLattice m s+3) := by
  let v := m8BoundaryVLattice m s
  let q := m8BoundaryCoeff m s
  let j := m8BoundaryJLattice m s
  let k := m8BoundaryKLattice m s
  let B := 2^(2*m+2)
  have hk : k+2=3*v*B := by
    simpa [k,v,B] using m8BoundaryKLattice_plus2 m s hm4
  have hj : j+3=3*v+q := by
    simpa [j,v,q] using m8BoundaryJLattice_plus3 m s hm4
  have hjsum : j+3*m+3=q*B := by
    simpa [j,q,B] using m8BoundaryJLattice_sum m s hm4
  have htail : 3*v+q+3*m=q*B := by omega
  calc
    k+j+3*m+5 = (k+2)+(j+3)+3*m := by omega
    _ = 3*v*B+(3*v+q)+3*m := by rw [hk,hj]
    _ = 3*v*B+q*B := by omega
    _ = B*(3*v+q) := by
      simp [Nat.add_mul,Nat.mul_add,Nat.mul_assoc,Nat.mul_comm,Nat.mul_left_comm]
    _ = B*(j+3) := by rw [hj]
    _ = 2^(2*m+2)*(j+3) := by rfl

theorem m8BoundaryJLattice_parity (m s : Nat) (hm4 : m%4=3) :
    m8BoundaryJLattice m s%2=0 ∧
    (m8BoundaryJLattice m s+m)%4=3 := by
  have hB8 := m8BoundaryB_mod8 m hm4
  have hsum := m8BoundaryJLattice_sum m s hm4
  have h2 := congrArg (fun z : Nat => z%2) hsum
  have h4 := congrArg (fun z : Nat => z%4) hsum
  have hB2 : 2^(2*m+2)%2=0 := by omega
  have hB4 : 2^(2*m+2)%4=0 := by omega
  rw [Nat.add_mod,Nat.add_mod,Nat.mul_mod,hB2] at h2
  rw [Nat.add_mod,Nat.add_mod,Nat.mul_mod,hB4] at h4
  omega

/-- Full boundary lattice source exclusion. At exact depth d=2m+2, every
    m=3 mod 4 and every admissible q-ray is blank-unreachable. -/
theorem m8BoundaryLattice_unreachable (m s : Nat) (hm4 : m%4=3) :
    ¬ BB6.Agent15.CReach
      (2*m8BoundaryJLattice m s+3) (m8BoundaryKLattice m s) := by
  have hm : m%2=1 := by omega
  have hj := m8BoundaryJLattice_parity m s hm4
  have hv8 := m8BoundaryVLattice_mod8 m s hm4
  have hpar : 2*(2*m+2)%4=(m+1)%4 := by omega
  have hscale := m8BoundaryKLattice_plus2 m s hm4
  exact deep_no_root_of_data_thin
    (m8BoundaryJLattice m s) m (m8BoundaryKLattice m s)
    (2*m+2) (m8BoundaryVLattice m s)
    hm hj.1 hj.2 (m8BoundaryLattice_stop m s hm4)
    hscale hv8 hpar


/-- Completeness of the boundary parameterization. At depth d=2m+2,
    every Diophantine M8 solution in the forbidden v=2 mod 8 sector is
    exactly one of the displayed q-rays. -/
theorem m8BoundaryLattice_complete
    (m j v : Nat)
    (hm4 : m%4=3)
    (hv8 : v%8=2)
    (heq : m8BoundaryQ m*(j+3)=m+2^(2*m+2)*v) :
    ∃ s,
      v=m8BoundaryVLattice m s ∧
      j=m8BoundaryJLattice m s := by
  let Q := m8BoundaryQ m
  let B := 2^(2*m+2)
  have hm : 1≤m := by omega
  have hQlow := m8BoundaryQ_lower m hm
  have hQpos : 0<Q := by omega
  have hQ8 := m8BoundaryQ_mod8 m hm
  have hB : B=3*Q+1 := by
    simpa [B,Q] using m8BoundaryBQ m
  have hdecomp : m+B*v=Q*(3*v)+(m+v) := by
    rw [hB]
    simp [Nat.add_mul,Nat.mul_add,Nat.mul_assoc,Nat.mul_comm,Nat.mul_left_comm]
    omega
  have hmain : Q*(j+3)=Q*(3*v)+(m+v) := by
    simpa [Q,B] using (heq.trans hdecomp)
  have hmul : Q*(3*v)≤Q*(j+3) := by
    rw [hmain]
    omega
  have hle : 3*v≤j+3 :=
    Nat.le_of_mul_le_mul_left hmul hQpos
  let q := j+3-3*v
  have hjq : j+3=3*v+q := by
    dsimp [q]
    omega
  have hqQ : Q*q=m+v := by
    rw [hjq,Nat.mul_add] at hmain
    omega
  have hqpos : 1≤q := by
    cases q with
    | zero =>
        simp at hqQ
        omega
    | succ q =>
        omega
  have hqmod : q%8=(if m%8=3 then 1 else 5) := by
    have hh := congrArg (fun z : Nat => z%8) hqQ
    rw [Nat.mul_mod,hQ8,Nat.add_mod] at hh
    by_cases h3 : m%8=3
    · rw [if_pos h3]
      omega
    · have h7 : m%8=7 := by omega
      rw [if_neg h3]
      omega
  let s := q/8
  have hqform : q=m8BoundaryCoeff m s := by
    have hdiv := Nat.mod_add_div q 8
    dsimp [s,m8BoundaryCoeff]
    rw [hqmod]
    omega
  have hv : v=m8BoundaryVLattice m s := by
    dsimp [m8BoundaryVLattice]
    rw [← hqform]
    rw [← hqQ]
    omega
  have hqB : q*B=j+3*m+3 := by
    calc
      q*B = q*(3*Q+1) := by rw [hB]
      _ = 3*(Q*q)+q := by
        simp [Nat.mul_add,Nat.mul_assoc,Nat.mul_comm,Nat.mul_left_comm]
      _ = 3*(m+v)+q := by rw [hqQ]
      _ = j+3*m+3 := by omega
  have hj : j=m8BoundaryJLattice m s := by
    dsimp [m8BoundaryJLattice]
    rw [← hqform]
    change j=q*B-(3*m+3)
    omega
  exact ⟨s,hv,hj⟩

/-- The one-ray family in M8BoundarySource is the q=1, s=0 slice. -/
theorem m8Boundary_first_slice (m : Nat) (hm8 : m%8=3) :
    m8BoundaryCoeff m 0=1 ∧
    m8BoundaryVLattice m 0=m8BoundaryD m ∧
    m8BoundaryJLattice m 0=m8BoundaryJThin m ∧
    m8BoundaryKLattice m 0=m8BoundaryKThin m := by
  have hm4 : m%4=3 := by omega
  have hq : m8BoundaryCoeff m 0=1 := by
    simp [m8BoundaryCoeff,hm8]
  have hvsum := m8BoundaryVLattice_sum m 0 hm4
  have hD := m8BoundaryD_eq m (by omega)
  have hv : m8BoundaryVLattice m 0=m8BoundaryD m := by
    rw [hq] at hvsum
    simp only [Nat.one_mul] at hvsum
    omega
  have hjsum := m8BoundaryJLattice_sum m 0 hm4
  have hjold := m8BoundaryJThin_plus m hm8
  have hj : m8BoundaryJLattice m 0=m8BoundaryJThin m := by
    rw [hq] at hjsum
    simp only [Nat.one_mul] at hjsum
    have hB := m8BoundaryBQ m
    have hD3 : 3*m8BoundaryD m+3*m+1=2^(2*m+2) := by
      have hdeq := m8BoundaryD_eq m (by omega)
      rw [hB]
      omega
    omega
  have hkplus := m8BoundaryKLattice_plus2 m 0 hm4
  have hkold := m8BoundaryKThin_plus m hm8
  have hk : m8BoundaryKLattice m 0=m8BoundaryKThin m := by
    rw [hv] at hkplus
    omega
  exact ⟨hq,hv,hj,hk⟩

#print axioms m8BoundaryLattice_stop
#print axioms m8BoundaryLattice_unreachable
#print axioms m8BoundaryLattice_complete
#print axioms m8Boundary_first_slice

end BB6.Agent15Research
