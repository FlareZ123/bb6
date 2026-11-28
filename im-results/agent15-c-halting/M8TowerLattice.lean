import M8BoundaryLattice
import Lean.Elab.Tactic.Omega

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace BB6.Agent15Research

/-- Geometric sum for repeated exact-boundary lifts. -/
def m8TowerLatticeSum (m : Nat) : Nat → Nat
  | 0 => 0
  | r+1 => 2^(2*m+2)*m8TowerLatticeSum m r+1

/-- Exact dyadic scale at tower depth r(2m+2). -/
def m8TowerLatticeX (m r : Nat) : Nat :=
  (2^(2*m+2))^r

/-- The forbidden quotient coordinate is independent of tower height. -/
def m8TowerLatticeV (m s : Nat) : Nat :=
  m8BoundaryVLattice m s

/-- Complete q-lattice stopping index at tower height r. -/
def m8TowerLatticeJ (m r s : Nat) : Nat :=
  3*m8TowerLatticeSum m r*m8TowerLatticeV m s+
    m8BoundaryCoeff m s-3

/-- Exact corresponding second stopping right counter. -/
def m8TowerLatticeK (m r s : Nat) : Nat :=
  3*m8TowerLatticeV m s*m8TowerLatticeX m r-2

theorem m8TowerLattice_geom (m r : Nat) :
    3*m8BoundaryQ m*m8TowerLatticeSum m r+1=
      m8TowerLatticeX m r := by
  induction r with
  | zero => rfl
  | succ r ih =>
      let B := 2^(2*m+2)
      let Q := m8BoundaryQ m
      let S := m8TowerLatticeSum m r
      have hB : B=3*Q+1 := by
        simpa [B,Q] using m8BoundaryBQ m
      change 3*Q*(B*S+1)+1=B^(r+1)
      calc
        3*Q*(B*S+1)+1 =
            B*(3*Q*S+1) := by
          rw [hB]
          simp only [Nat.mul_add,Nat.add_mul,Nat.one_mul]
          ac_rfl
        _ = B*m8TowerLatticeX m r := by rw [ih]
        _ = m8TowerLatticeX m r*B := by ac_rfl
        _ = B^r*B := by rfl
        _ = B^(r+1) := (Nat.pow_succ B r).symm

theorem m8TowerLatticeX_power (m r : Nat) :
    m8TowerLatticeX m r=2^((2*m+2)*r) := by
  dsimp [m8TowerLatticeX]
  exact (Nat.pow_mul 2 (2*m+2) r).symm

theorem m8TowerLatticeSum_pos (m r : Nat) (hr : 1≤r) :
    1≤m8TowerLatticeSum m r := by
  cases r with
  | zero => omega
  | succ r =>
      simp only [m8TowerLatticeSum]
      omega

theorem m8TowerLatticeB_mod4 (m : Nat) :
    2^(2*m+2)%4=0 := by
  rw [show 2*m+2=2+2*m by omega,Nat.pow_add]
  simp

theorem m8TowerLatticeSum_mod4 (m r : Nat) (hr : 1≤r) :
    m8TowerLatticeSum m r%4=1 := by
  cases r with
  | zero => omega
  | succ r =>
      have hB := m8TowerLatticeB_mod4 m
      change (2^(2*m+2)*m8TowerLatticeSum m r+1)%4=1
      rw [Nat.add_mod,Nat.mul_mod,hB]
      omega

theorem m8TowerLatticeCoeff_mod4 (m s : Nat) (hm4 : m%4=3) :
    m8BoundaryCoeff m s%4=1 := by
  have h8 := m8BoundaryCoeff_mod8 m s hm4
  by_cases h3 : m%8=3
  · rw [if_pos h3] at h8
    omega
  · rw [if_neg h3] at h8
    omega

theorem m8TowerLatticeJ_plus3
    (m r s : Nat) (hm4 : m%4=3) (hr : 1≤r) :
    m8TowerLatticeJ m r s+3 =
      3*m8TowerLatticeSum m r*m8TowerLatticeV m s+
        m8BoundaryCoeff m s := by
  have hs := m8TowerLatticeSum_pos m r hr
  have hv8 : m8TowerLatticeV m s%8=2 := by
    simpa [m8TowerLatticeV] using m8BoundaryVLattice_mod8 m s hm4
  have hv : 2≤m8TowerLatticeV m s := by omega
  have hq := m8BoundaryCoeff_pos m s
  have hsv : 2≤m8TowerLatticeSum m r*m8TowerLatticeV m s :=
    Nat.mul_le_mul hs hv
  have h6 : 6≤3*m8TowerLatticeSum m r*m8TowerLatticeV m s := by
    have h := Nat.mul_le_mul_left 3 hsv
    simpa [Nat.mul_assoc] using h
  dsimp [m8TowerLatticeJ]
  omega

theorem m8TowerLatticeK_plus2
    (m r s : Nat) (hm4 : m%4=3) :
    m8TowerLatticeK m r s+2 =
      3*m8TowerLatticeV m s*m8TowerLatticeX m r := by
  have hv8 : m8TowerLatticeV m s%8=2 := by
    simpa [m8TowerLatticeV] using m8BoundaryVLattice_mod8 m s hm4
  have hv : 2≤m8TowerLatticeV m s := by omega
  have hx : 1≤m8TowerLatticeX m r := by
    dsimp [m8TowerLatticeX]
    exact Nat.pow_pos (Nat.pow_pos (by decide))
  have hvx : 2≤m8TowerLatticeV m s*m8TowerLatticeX m r :=
    Nat.mul_le_mul hv hx
  have h6 : 6≤3*m8TowerLatticeV m s*m8TowerLatticeX m r := by
    have h := Nat.mul_le_mul_left 3 hvx
    simpa [Nat.mul_assoc] using h
  dsimp [m8TowerLatticeK]
  omega

/-- Exact M8 quotient equation at every positive tower height. -/
theorem m8TowerLattice_mass
    (m r s : Nat) (hm4 : m%4=3) (hr : 1≤r) :
    m8BoundaryQ m*(m8TowerLatticeJ m r s+3)=
      m+m8TowerLatticeX m r*m8TowerLatticeV m s := by
  let Q := m8BoundaryQ m
  let S := m8TowerLatticeSum m r
  let X := m8TowerLatticeX m r
  let V := m8TowerLatticeV m s
  let q := m8BoundaryCoeff m s
  have hgeom : 3*Q*S+1=X := by
    simpa [Q,S,X] using m8TowerLattice_geom m r
  have hvsum : m+V=q*Q := by
    simpa [V,q] using m8BoundaryVLattice_sum m s hm4
  have hqQ : Q*q=m+V := by
    calc
      Q*q=q*Q := Nat.mul_comm _ _
      _=m+V := hvsum.symm
  have hj : m8TowerLatticeJ m r s+3=3*S*V+q := by
    simpa [S,V,q] using m8TowerLatticeJ_plus3 m r s hm4 hr
  calc
    Q*(m8TowerLatticeJ m r s+3)
        = Q*(3*S*V+q) := by rw [hj]
    _ = 3*Q*S*V+Q*q := by
      simp only [Nat.mul_add]
      ac_rfl
    _ = 3*Q*S*V+(m+V) := by rw [hqQ]
    _ = m+(3*Q*S+1)*V := by
      simp only [Nat.add_mul,Nat.one_mul]
      ac_rfl
    _ = m+X*V := by rw [hgeom]
    _ = m+m8TowerLatticeX m r*m8TowerLatticeV m s := by rfl

/-- Exact second-stopping equation at every positive tower height. -/
theorem m8TowerLattice_stop
    (m r s : Nat) (hm4 : m%4=3) (hr : 1≤r) :
    m8TowerLatticeK m r s+m8TowerLatticeJ m r s+3*m+5 =
      2^(2*m+2)*(m8TowerLatticeJ m r s+3) := by
  let Q := m8BoundaryQ m
  let X := m8TowerLatticeX m r
  let V := m8TowerLatticeV m s
  let J := m8TowerLatticeJ m r s
  let K := m8TowerLatticeK m r s
  let B := 2^(2*m+2)
  have hB : B=3*Q+1 := by
    simpa [B,Q] using m8BoundaryBQ m
  have hmass : Q*(J+3)=m+X*V := by
    simpa [Q,J,X,V] using m8TowerLattice_mass m r s hm4 hr
  have hk : K+2=3*V*X := by
    simpa [K,V,X] using m8TowerLatticeK_plus2 m r s hm4
  symm
  calc
    B*(J+3)=(3*Q+1)*(J+3) := by rw [hB]
    _=3*(Q*(J+3))+(J+3) := by
      simp only [Nat.add_mul,Nat.one_mul]
      ac_rfl
    _=3*(m+X*V)+(J+3) := by rw [hmass]
    _=3*V*X+J+3*m+3 := by
      simp only [Nat.mul_add]
      ac_rfl
    _=(K+2)+J+3*m+3 := by rw [hk]
    _=K+J+3*m+5 := by omega

theorem m8TowerLatticeJ_parity
    (m r s : Nat) (hm4 : m%4=3) (hr : 1≤r) :
    m8TowerLatticeJ m r s%2=0 ∧
      (m8TowerLatticeJ m r s+m)%4=3 := by
  let S := m8TowerLatticeSum m r
  let V := m8TowerLatticeV m s
  let q := m8BoundaryCoeff m s
  let J := m8TowerLatticeJ m r s
  have hs4 : S%4=1 := by
    simpa [S] using m8TowerLatticeSum_mod4 m r hr
  have hv8 : V%8=2 := by
    simpa [V,m8TowerLatticeV] using m8BoundaryVLattice_mod8 m s hm4
  have hv4 : V%4=2 := by omega
  have hq4 : q%4=1 := by
    simpa [q] using m8TowerLatticeCoeff_mod4 m s hm4
  have hterm : (3*S*V)%4=2 := by
    rw [Nat.mul_mod (3*S) V 4,Nat.mul_mod 3 S 4,hs4,hv4]
    omega
  have hj : J+3=3*S*V+q := by
    simpa [J,S,V,q] using m8TowerLatticeJ_plus3 m r s hm4 hr
  have hjmod : (J+3)%4=3 := by
    rw [hj,Nat.add_mod,hterm,hq4]
    omega
  have hJ4 : J%4=0 := by
    rw [Nat.add_mod] at hjmod
    omega
  constructor
  · omega
  · dsimp [J] at hJ4 ⊢
    omega

theorem m8TowerLattice_depth_parity (m r : Nat) (hm4 : m%4=3) :
    2*((2*m+2)*r)%4=(m+1)%4 := by
  have hm1 : (m+1)%4=0 := by omega
  have hbase : (2*(2*m+2))%4=0 := by omega
  have hleft : (2*((2*m+2)*r))%4=0 := by
    rw [show 2*((2*m+2)*r)=(2*(2*m+2))*r by ac_rfl,
      Nat.mul_mod,hbase]
    simp
  omega

/-- Source-linked complete q-lattice exclusion at every positive tower
    depth r(2m+2), for the m=3 mod 4 M8 sector. -/
theorem m8TowerLattice_unreachable
    (m r s : Nat) (hm4 : m%4=3) (hr : 1≤r) :
    ¬ BB6.Agent15.CReach
      (2*m8TowerLatticeJ m r s+3) (m8TowerLatticeK m r s) := by
  have hm : m%2=1 := by omega
  have hj := m8TowerLatticeJ_parity m r s hm4 hr
  have hv8 : m8TowerLatticeV m s%8=2 := by
    simpa [m8TowerLatticeV] using m8BoundaryVLattice_mod8 m s hm4
  have hscale :
      m8TowerLatticeK m r s+2 =
        3*m8TowerLatticeV m s*2^((2*m+2)*r) := by
    rw [m8TowerLatticeK_plus2 m r s hm4,
      m8TowerLatticeX_power m r]
  exact deep_no_root_of_data_thin
    (m8TowerLatticeJ m r s) m (m8TowerLatticeK m r s)
    ((2*m+2)*r) (m8TowerLatticeV m s)
    hm hj.1 hj.2 (m8TowerLattice_stop m r s hm4 hr)
    hscale hv8 (m8TowerLattice_depth_parity m r hm4)

#print axioms m8TowerLattice_mass
#print axioms m8TowerLattice_stop
#print axioms m8TowerLattice_unreachable

end BB6.Agent15Research
