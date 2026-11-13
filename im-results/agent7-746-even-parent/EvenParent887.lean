import FeederExceptional887

set_option maxHeartbeats 0

namespace CascadeEvenParent887

open CascadeResetInverse

/-- The common dyadic scale for the exceptional lift. -/
def p (n : Nat) : Nat := 2^(n-2)

/-- The fifth same-scale even predecessor of the fatal target's even
    predecessor, written in the scale-normalized coordinate. -/
def y5 (n : Nat) : Nat := 16*p n - 127*n - 193

/-- Quotient parameter for the t=1 odd inverse at y5. -/
def d0 (n : Nat) : Nat := (2*y5 n+5)/9

def q0 (n : Nat) : Nat := 2*d0 n

/-- The actual source predecessor of y5 in the t=1 odd arm. -/
def z0 (n : Nat) : Nat := 2*q0 n - 8*p n - n - 3

/-- The even predecessor of z0. -/
def z1 (n : Nat) : Nat := 2*z0 n - 8*p n - (n-2)

private theorem pow_period6_9 (m : Nat) :
    2^(m+6)%9=2^m%9 := by
  rw [Nat.pow_add, Nat.mul_mod]
  have h : (2:Nat)^6%9=1 := by decide
  rw [h]
  simp

private theorem pow_period6_9_many (m t : Nat) :
    2^(m+6*t)%9=2^m%9 := by
  induction t with
  | zero => simp
  | succ t ih =>
      have hs : m+6*(t+1)=(m+6*t)+6 := by omega
      rw [hs]
      exact (pow_period6_9 (m+6*t)).trans ih

private theorem growth (n : Nat) (hn : n%13122=887) :
    10000*n+10000≤p n := by
  have hn4 : 4≤n := by omega
  simpa [p] using CascadeFeederSix.growth n hn4

private theorem small_residues (n : Nat) (hn : n%13122=887) :
    n%6=5 ∧ n%9=5 ∧ 2^n%9=5 ∧ p n%9=8 := by
  have hn6 : n%6=5 := by omega
  have hn9 : n%9=5 := by omega
  have hrepr : n=5+6*(n/6) := by
    have h := Nat.mod_add_div n 6
    omega
  have hrepr2 : n-2=3+6*(n/6) := by omega
  have hpow1 := pow_period6_9_many 5 (n/6)
  have hpow2 := pow_period6_9_many 3 (n/6)
  constructor
  · exact hn6
  constructor
  · exact hn9
  constructor
  · rw [hrepr]
    simpa using hpow1
  · dsimp [p]
    rw [hrepr2]
    simpa using hpow2

/-- The exact t=1 odd parent of y5. The odd-band quantity is q0=2*d0;
    the source predecessor is z0=2*q0-8*2^(n-2)-n-3, not d0. -/
theorem corrected_t1_parent (n : Nat) (hn : n%13122=887) :
    ResetParent (z0 n) (y5 n) := by
  obtain ⟨hn6,hn9,h2n9,hpn9⟩ := small_residues n hn
  have hbig := growth n hn
  have hypos : 127*n+193≤16*p n := by omega
  have hy : y5 n=16*p n-127*n-193 := rfl
  have hyMod : y5 n%9=2 := by
    dsimp [y5]
    omega
  have hnumMod : (2*y5 n+5)%9=0 := by omega
  have hd : 9*d0 n=2*y5 n+5 := by
    have h := Nat.mod_add_div (2*y5 n+5) 9
    rw [hnumMod] at h
    dsimp [d0]
    omega
  have hdodd : d0 n%2=1 := by
    have hodd : (2*y5 n+5)%2=1 := by omega
    omega
  have hqformula : 9*q0 n=64*p n-508*n-762 := by
    have h1 : 9*q0 n=4*y5 n+10 := by
      dsimp [q0]
      omega
    rw [hy] at h1
    omega
  have hqband : 6*p n+1≤q0 n ∧ q0 n≤8*p n-1 := by
    constructor <;> omega
  have hz0pos : 8*p n+n+3≤2*q0 n := by omega
  have hparent : ResetParent (z0 n) (y5 n) := by
    apply Or.inr
    refine ⟨n-2,1,d0 n,hdodd,?_,?_,?_⟩
    · simpa [p,q0] using hqband
    · norm_num
      exact hd
    · dsimp [z0,q0,p]
      omega
  exact hparent

/-- Exact affine identity for the corrected predecessor. -/
theorem z0_formula (n : Nat) (hn : n%13122=887) :
    9*z0 n=56*p n-1025*n-1551 := by
  have hq := by
    obtain ⟨_,_,_,_⟩ := small_residues n hn
    have hbig := growth n hn
    have hypos : 127*n+193≤16*p n := by omega
    have hy : y5 n=16*p n-127*n-193 := rfl
    have hyMod : y5 n%9=2 := by
      dsimp [y5]
      omega
    have hnumMod : (2*y5 n+5)%9=0 := by omega
    have hd : 9*d0 n=2*y5 n+5 := by
      have h := Nat.mod_add_div (2*y5 n+5) 9
      rw [hnumMod] at h
      dsimp [d0]
      omega
    have h1 : 9*q0 n=4*y5 n+10 := by
      dsimp [q0]
      omega
    rw [hy] at h1
    exact h1
  have hz0pos : 8*p n+n+3≤2*q0 n := by
    have hbig := growth n hn
    obtain ⟨_,_,_,_⟩ := small_residues n hn
    have hypos : 127*n+193≤16*p n := by omega
    have hy : y5 n=16*p n-127*n-193 := rfl
    have hyMod : y5 n%9=2 := by dsimp [y5]; omega
    have hnumMod : (2*y5 n+5)%9=0 := by omega
    have hd : 9*d0 n=2*y5 n+5 := by
      have h := Nat.mod_add_div (2*y5 n+5) 9
      rw [hnumMod] at h
      dsimp [d0]
      omega
    have hqformula : 9*q0 n=64*p n-508*n-762 := by
      have h1 : 9*q0 n=4*y5 n+10 := by dsimp [q0]; omega
      rw [hy] at h1
      exact h1
    have hqband : 6*p n+1≤q0 n ∧ q0 n≤8*p n-1 := by
      constructor <;> omega
    omega
  dsimp [z0]
  omega

/-- The corrected parent z0 is itself in the even band at scale n-2. -/
theorem z0_even_band (n : Nat) (hn : n%13122=887) :
    6*p n-1≤z0 n ∧ z0 n≤8*p n-3 := by
  have hbig := growth n hn
  have hformula := z0_formula n hn
  constructor <;> omega

/-- z1 is the genuine even parent of z0. -/
theorem z1_even_parent (n : Nat) (hn : n%13122=887) :
    ResetParent (z1 n) (z0 n) := by
  have hband := z0_even_band n hn
  have hbig := growth n hn
  have hzpos : 8*p n+(n-2)≤2*z0 n := by omega
  apply Or.inl
  refine ⟨n-2,?_,?_⟩
  · simpa [p] using hband
  · dsimp [z1,p]
    omega

/-- Affine identity for the gap-state after the even parent of z0. -/
theorem z1_formula (n : Nat) (hn : n%13122=887) :
    9*z1 n=40*p n-2059*n-3084 := by
  have hbig := growth n hn
  have hz0 := z0_formula n hn
  have hzpos : 8*p n+(n-2)≤2*z0 n := by
    have hband := z0_even_band n hn
    omega
  dsimp [z1]
  omega

/-- The next even predecessor lies in the middle-low gap, not an even band. -/
theorem z1_middle_low_gap (n : Nat) (hn : n%13122=887) :
    4*p n-3<z1 n ∧ z1 n<6*p n-1 := by
  have hbig := growth n hn
  have hz1 := z1_formula n hn
  constructor <;> omega

#print axioms corrected_t1_parent
#print axioms z0_formula
#print axioms z0_even_band
#print axioms z1_even_parent
#print axioms z1_formula
#print axioms z1_middle_low_gap

end CascadeEvenParent887
