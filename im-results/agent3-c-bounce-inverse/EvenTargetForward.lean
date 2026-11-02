import FastSectionDef
import Lean.Elab.Tactic.Omega

namespace BB6.Agent46

/-- The middle counter reached after n even-bounce recursive transitions. -/
def invLiftK (k : Nat) : Nat → Nat
  | 0 => k
  | n+1 => invLiftK (2*k+4) n

/-- The unique initial height obtained by reversing n recursive even bounces. -/
def invLiftC (k : Nat) : Nat → Nat → Nat
  | 0, y => y+1
  | n+1, y => 2*k+5+invLiftC (2*k+4) n y

theorem invLiftC_lower (k n y : Nat) : y+1 ≤ invLiftC k n y := by
  induction n generalizing k with
  | zero => simp [invLiftC]
  | succ n ih =>
    simp only [invLiftC]
    have hh := ih (2*k+4)
    omega

/-- Reversing an arbitrary number of even-bounce steps preserves the output. -/
theorem bounce_inv_lift (k n y : Nat) (hk : k%2=0) (hy : 5≤y) :
    (bounce k (invLiftC k n y)).2 =
      (bounce (invLiftK k n) (y+1)).2 := by
  induction n generalizing k with
  | zero => simp [invLiftC, invLiftK]
  | succ n ih =>
    have hC : 6≤invLiftC (2*k+4) n y := by
      have h := invLiftC_lower (2*k+4) n y
      omega
    have hlow : ¬(2*k+5+invLiftC (2*k+4) n y<4) := by omega
    have hodd : k%2≠1 := by omega
    have h4 : 2*k+5+invLiftC (2*k+4) n y ≠ 4 := by omega
    have h5 : 2*k+5+invLiftC (2*k+4) n y ≠ 5 := by omega
    have hhigh : ¬(2*k+5+invLiftC (2*k+4) n y≤2*k+8) := by omega
    simp only [invLiftC,invLiftK]
    rw [bounce]
    simp only [if_neg hlow,if_neg hodd,if_neg h4,if_neg h5, if_neg hhigh]
    have hsub : 2*k+5+invLiftC (2*k+4) n y-(2*k+5)=
        invLiftC (2*k+4) n y := by omega
    rw [hsub]
    exact ih (2*k+4) (by omega)

theorem bounce_inv_direct (k y : Nat) (hk : k%2=0) (hy : 5≤y)
    (hu : y+1≤2*k+8) :
    (bounce k (y+1)).2=some (2*k+8-(y+1), y) := by
  have hlow : ¬(y+1<4) := by omega
  have hodd : k%2≠1 := by omega
  have h4 : y+1≠4 := by omega
  have h5 : y+1≠5 := by omega
  simp [bounce,hlow,hodd,h4,h5,hu]

theorem invLiftK_closed (k n : Nat) :
    invLiftK k n +4 = 2^n*(k+4) := by
  induction n generalizing k with
  | zero => simp [invLiftK]
  | succ n ih =>
    simp only [invLiftK, Nat.pow_succ]
    calc
      invLiftK (2*k+4) n +4 = 2^n*(2*k+4+4) := ih (2*k+4)
      _ = 2^n*(2*(k+4)) := by congr 1
      _ = 2^n*2*(k+4) := by ac_rfl

theorem invLiftC_closed (k n y : Nat) :
    invLiftC k n y + 2*(k+4)+3*n = (y+1)+2^(n+1)*(k+4) := by
  induction n generalizing k with
  | zero => simp [invLiftC]
  | succ n ih =>
    simp only [invLiftC]
    have hh := ih (2*k+4)
    have hp : 2^(n+1)*(2*k+4+4) = 2^(n+1+1)*(k+4) := by
      rw [Nat.pow_succ, Nat.pow_succ]
      calc
        2^n*2*(2*k+4+4) = 2^n*2*(2*(k+4)) := by congr 1
        _ = 2^n*2*2*(k+4) := by ac_rfl
    rw [hp] at hh
    omega

theorem four_pow_ge_inverse (r : Nat) : r+1 ≤ 4^r := by
  induction r with
  | zero => decide
  | succ r ih =>
    rw [Nat.pow_succ]
    omega

theorem two_pow_double_inverse (r : Nat) : 2^(2*r)=4^r := by
  calc
    2^(2*r) = (2^2)^r := Nat.pow_mul 2 2 r
    _ = 4^r := by simp

/-- Every syntactically predicted high predecessor is a REAL source edge,
    for arbitrary recursion depth 2r and arbitrarily large u. -/
theorem general_even_inverse_edge (r u : Nat) (hu : 1≤u) :
    secNext (22*u-3,32*(4^r*u)-(11*u+3+3*r)) =
      some (24*(4^r*u), 20*(4^r*u)-1) := by
  let P : Nat := 4^r*u
  let a : Nat := 22*u-3
  let k : Nat := 32*P-(11*u+3+3*r)
  let K : Nat := a-1
  let n : Nat := 2*r
  let y : Nat := 20*P-1
  have hpow : r+1≤4^r := four_pow_ge_inverse r
  have hP1 : 1≤P := by
    have hh := Nat.le_mul_of_pos_right (4^r) hu
    dsimp [P]
    omega
  have hPu : u≤P := by
    have hh := Nat.mul_le_mul_right u (by omega : 1≤4^r)
    dsimp [P]
    simpa using hh
  have hPr : r≤P := by
    have hh := Nat.le_mul_of_pos_right (4^r) hu
    dsimp [P]
    omega
  have ha : a+3=22*u := by dsimp [a]; omega
  have hK : K+4=22*u := by dsimp [K]; omega
  have hk : k+(11*u+3+3*r)=32*P := by
    dsimp [k]
    omega
  have hkh : 2*k>a := by omega
  have hne0 : a≠0 := by omega
  have hne1 : a≠1 := by omega
  have hk0 : k≠0 := by omega
  have hreg : ¬2*k≤a := by omega
  have hodd : K%2=0 := by dsimp [K]; omega
  have hy : 5≤y := by dsimp [y]; omega
  have hn : 2^n=4^r := by simpa [n] using two_pow_double_inverse r
  have hkc : invLiftK K n+4=22*P := by
    calc
      invLiftK K n+4 = 2^n*(K+4) := invLiftK_closed K n
      _ = (4^r)*(22*u) := by rw [hn,hK]
      _ = 22*((4^r)*u) := by ac_rfl
      _ = 22*P := rfl
  have hbase : (y+1)+2^(n+1)*(K+4)=64*P := by
    rw [Nat.pow_succ,hK,hn]
    have heq : 4^r*2*(22*u)=44*P := by
      dsimp [P]
      calc
        4^r*2*(22*u) = (2*22)*(4^r*u) := by ac_rfl
        _ = 44*(4^r*u) := by rfl
    rw [heq]
    dsimp [y]
    omega
  have hC : invLiftC K n y+44*u+6*r=64*P := by
    have hh := invLiftC_closed K n y
    rw [hbase] at hh
    have hterm : 2*(K+4)+3*n=44*u+6*r := by omega
    omega
  have hinput : 2*k-a+3=invLiftC K n y := by omega
  have htail : (bounce (invLiftK K n) (y+1)).2 =
      some (24*P,20*P-1) := by
    have hterm : y+1≤2*(invLiftK K n)+8 := by omega
    have hev : (invLiftK K n)%2=0 := by omega
    have h := bounce_inv_direct (invLiftK K n) y hev hy hterm
    have hx : 2*(invLiftK K n)+8-(y+1)=24*P := by omega
    simpa [hx,y] using h
  have h : (bounce K (2*k-a+3)).2 = some (24*P,20*P-1) := by
    rw [hinput]
    rw [bounce_inv_lift K n y hodd hy]
    exact htail
  change secNext (a,k) = some (24*P,20*P-1)
  simp only [secNext, exactSection, if_neg hne0,if_neg hne1,
    if_neg hk0,if_neg hreg]
  exact h

#print axioms bounce_inv_lift
#print axioms invLiftC_closed
#print axioms general_even_inverse_edge
end BB6.Agent46
