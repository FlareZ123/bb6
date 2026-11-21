import Lean
open Lean
set_option maxHeartbeats 1000000

namespace BB6.Agent9FirstShallowCoordinateGate

/-!
Exact arithmetic consequences of the three surviving first-shallow cases
from RestartWallLowTrace.lean. The hypotheses are the source-wall mass
invariant, the mod-7 source-coordinate relation, and the inverseAt power
and mass equations. The child-mod-four guard is represented by k % 2 = 0.
-/

theorem two_mul_le_pow_two : ∀ n : Nat, 2 ≤ n → 2*n ≤ 2^n
  | 0, h => by omega
  | 1, h => by omega
  | n+2, h => by
      by_cases h0 : n=0
      · subst n; decide
      by_cases h1 : n=1
      · subst n; decide
      have hn2 : 2≤n := by omega
      have ih := two_mul_le_pow_two n hn2
      have hpow : 2 ≤ 2^n := Nat.le_pow (a:=2) (b:=n) (by omega)
      have hmul : 2^(n+2)=2^n*4 := by simp [Nat.pow_succ, Nat.mul_assoc]
      omega

theorem target_power_bound (n : Nat) (hn : 83≤n) : 2*n≤2^n := by
  exact two_mul_le_pow_two n (by omega)

/-! ### First-shallow parent coordinates -/

theorem is20_parent_coordinates
    (P u b d T : Nat)
    (hcoord : b+18=6*d)
    (hmass : b+d+2*T+1=14*P)
    (hT : T=14*u+5)
    (hb : 8≤b) :
    b+24*u+12=12*P ∧ d+4*u=2*P+1 ∧ 2*u+2≤P := by
  omega

theorem is48_even_parent_coordinates
    (P u b d T : Nat)
    (hcoord : b+14=6*d)
    (hmass : b+d+2*T+1=14*P)
    (hT : T=14*u+10)
    (hb : 8≤b) :
    b+24*u+20=12*P ∧ d+4*u+1=2*P ∧ 2*u+3≤P := by
  omega

theorem is48_odd_parent_coordinates
    (P u b d T : Nat)
    (hcoord : b+14=6*d)
    (hmass : b+d+2*T+1=14*P)
    (hT : T=14*u+3)
    (hb : 8≤b) :
    b+24*u+8=12*P ∧ d+4*u=2*P+1 ∧ 2*u+2≤P := by
  omega

/-! ### First-shallow child coordinates -/

theorem child_source_coordinate
    (k c : Nat) (hk : 2≤k) :
    (c+4)+(2*k-4)/2+3=c+k+5 := by
  omega

/-- Is=20, T=14u+5: the first shallow edge has depth zero. -/
theorem is20_child_coordinates
    (P u b d k c : Nat)
    (hP : P%2=0)
    (hb : b+24*u+12=12*P)
    (hd : d+4*u=2*P+1)
    (hpow : c+3=d+b/2+3)
    (hInvMass : 2*k+c+2=b+d) :
    2*k+12*u+8=6*P ∧
    c+16*u+5=8*P ∧
    c+k+5+22*u+4=11*P ∧
    k%2=0 := by
  omega

/-- Is=48, even T=14u+10: the first shallow edge has depth zero. -/
theorem is48_even_child_coordinates
    (P u b d k c : Nat)
    (hP : P%2=0)
    (hb : b+24*u+20=12*P)
    (hd : d+4*u+1=2*P)
    (hpow : c+3=d+b/2+3)
    (hInvMass : 2*k+c+2=b+d) :
    2*k+12*u+12=6*P ∧
    c+16*u+11=8*P ∧
    c+k+5+22*u+12=11*P ∧
    k%2=0 := by
  omega

/-- Is=48, odd T=14u+3: the first shallow edge has depth one. -/
theorem is48_odd_child_coordinates
    (P u b d k c : Nat)
    (hP : P%2=0)
    (hb : b+24*u+8=12*P)
    (hd : d+4*u=2*P+1)
    (hpow : 2*(c+3)=d+b/2+3)
    (hInvMass : 2*k+c+4=b+d) :
    2*k+20*u+8=10*P ∧
    c+8*u+3=4*P ∧
    c+k+5+18*u+2=9*P ∧
    k%2=0 := by
  omega

/-! ### Wall equations for a terminal first-shallow child -/

theorem is20_terminal_wall_equation
    (P u b B : Nat)
    (hb : b+12*u+12=6*P)
    (hB : B=14*u+6)
    (hwall : b+4*B=12*P+4) : 22*u+4=3*P := by
  omega

theorem is48_even_terminal_wall_equation
    (P u b B : Nat)
    (hb : b+12*u+16=6*P)
    (hB : B=14*u+11)
    (hwall : b+4*B=12*P+4) : 22*u+12=3*P := by
  omega

theorem is48_odd_terminal_wall_equation
    (P u b B : Nat)
    (hb : b+20*u+12=10*P)
    (hB : B=14*u+5)
    (hwall : b+4*B=12*P+4) : 18*u+2=P := by
  omega

/-! ### A terminal first-shallow child is impossible -/

/-- The high-depth restart defect equation excludes an immediate wall child
in the Is=20 branch. -/
theorem is20_terminal_impossible
    (P n M D u : Nat)
    (hPbig : 2*n≤P)
    (hOffset : M+n+3=14*u)
    (hWall : 22*u+4=3*P)
    (hDefect : 49*D+14*M=18*P+6)
    (hD : 4≤D) : False := by
  omega

/-- The high-depth restart defect equation excludes an immediate wall child
in the even-offset Is=48 branch. -/
theorem is48_even_terminal_impossible
    (P n M D u : Nat)
    (hPbig : 2*n≤P)
    (hOffset : M+n=14*u+3)
    (hWall : 22*u+12=3*P)
    (hDefect : 49*D+14*M=2*P+6)
    (hD : 4≤D) : False := by
  omega

/-- The high-depth restart defect equation excludes an immediate wall child
in the odd-offset Is=48 branch. -/
theorem is48_odd_terminal_impossible
    (P n M D u : Nat)
    (hPbig : 2*n≤P)
    (hOffset : M+n+4=14*u)
    (hWall : 18*u+2=P)
    (hDefect : 49*D+14*M=2*P+6)
    (hD : 4≤D) : False := by
  omega

theorem is20_terminal_impossible_pow
    (n M D u : Nat)
    (hn : 83≤n)
    (hOffset : M+n+3=14*u)
    (hWall : 22*u+4=3*(2^n))
    (hDefect : 49*D+14*M=18*(2^n)+6)
    (hD : 4≤D) : False := by
  have hPbig : 2*n≤2^n := target_power_bound n hn
  exact is20_terminal_impossible (2^n) n M D u hPbig hOffset hWall hDefect hD

theorem is48_even_terminal_impossible_pow
    (n M D u : Nat)
    (hn : 83≤n)
    (hOffset : M+n=14*u+3)
    (hWall : 22*u+12=3*(2^n))
    (hDefect : 49*D+14*M=2*(2^n)+6)
    (hD : 4≤D) : False := by
  have hPbig : 2*n≤2^n := target_power_bound n hn
  exact is48_even_terminal_impossible (2^n) n M D u hPbig hOffset hWall hDefect hD

theorem is48_odd_terminal_impossible_pow
    (n M D u : Nat)
    (hn : 83≤n)
    (hOffset : M+n+4=14*u)
    (hWall : 18*u+2=2^n)
    (hDefect : 49*D+14*M=2*(2^n)+6)
    (hD : 4≤D) : False := by
  have hPbig : 2*n≤2^n := target_power_bound n hn
  exact is48_odd_terminal_impossible (2^n) n M D u hPbig hOffset hWall hDefect hD

/-! ### Full next-edge residue gates

For a next edge of depth t, 2^t (c+3) = X is the inverse power
condition, c is odd, 2*k+c+2*t+2=S is the inverse mass condition, and
k even is the next-child mod-four guard. These are necessary conditions
for a source suffix to continue.
-/

-- Is=20, T=14u+5.
theorem is20_depth0
    (P u X S k c : Nat)
    (hP : P%16=0)
    (hX : X+22*u+4=11*P)
    (hS : S+28*u+13=14*P)
    (hpow : c+3=X)
    (hmass : 2*k+c+2=S)
    (hk : k%2=0) : u%2=0 := by omega

theorem is20_depth1
    (P u X S k c : Nat)
    (hP : P%16=0)
    (hX : X+22*u+4=11*P)
    (hS : S+28*u+13=14*P)
    (hpow : 2*(c+3)=X)
    (hodd : c%2=1)
    (hmass : 2*k+c+4=S)
    (hk : k%2=0) : u%4=0 := by omega

theorem is20_depth2
    (P u X S k c : Nat)
    (hP : P%16=0)
    (hX : X+22*u+4=11*P)
    (hS : S+28*u+13=14*P)
    (hpow : 4*(c+3)=X)
    (hodd : c%2=1)
    (hmass : 2*k+c+6=S)
    (hk : k%2=0) : u%8=2 := by omega

-- Is=48, even T=14u+10.
theorem is48_even_depth0
    (P u X S k c : Nat)
    (hP : P%16=0)
    (hX : X+22*u+12=11*P)
    (hS : S+28*u+23=14*P)
    (hpow : c+3=X)
    (hmass : 2*k+c+2=S)
    (hk : k%2=0) : u%2=1 := by omega

theorem is48_even_depth1
    (P u X S k c : Nat)
    (hP : P%16=0)
    (hX : X+22*u+12=11*P)
    (hS : S+28*u+23=14*P)
    (hpow : 2*(c+3)=X)
    (hodd : c%2=1)
    (hmass : 2*k+c+4=S)
    (hk : k%2=0) : u%4=2 := by omega

theorem is48_even_depth2
    (P u X S k c : Nat)
    (hP : P%16=0)
    (hX : X+22*u+12=11*P)
    (hS : S+28*u+23=14*P)
    (hpow : 4*(c+3)=X)
    (hodd : c%2=1)
    (hmass : 2*k+c+6=S)
    (hk : k%2=0) : u%8=2 := by omega

-- Is=48, odd T=14u+3.
theorem is48_odd_depth0
    (P u X S k c : Nat)
    (hP : P%16=0)
    (hX : X+18*u+2=9*P)
    (hS : S+28*u+11=14*P)
    (hpow : c+3=X)
    (hmass : 2*k+c+2=S)
    (hk : k%2=0) : u%2=0 := by omega

theorem is48_odd_depth1
    (P u X S k c : Nat)
    (hP : P%16=0)
    (hX : X+18*u+2=9*P)
    (hS : S+28*u+11=14*P)
    (hpow : 2*(c+3)=X)
    (hodd : c%2=1)
    (hmass : 2*k+c+4=S)
    (hk : k%2=0) : u%4=3 := by omega

theorem is48_odd_depth2
    (P u X S k c : Nat)
    (hP : P%16=0)
    (hX : X+18*u+2=9*P)
    (hS : S+28*u+11=14*P)
    (hpow : 4*(c+3)=X)
    (hodd : c%2=1)
    (hmass : 2*k+c+6=S)
    (hk : k%2=0) : u%8=3 := by omega

#print axioms target_power_bound
#print axioms is20_parent_coordinates
#print axioms is48_even_parent_coordinates
#print axioms is48_odd_parent_coordinates
#print axioms child_source_coordinate
#print axioms is20_child_coordinates
#print axioms is48_even_child_coordinates
#print axioms is48_odd_child_coordinates
#print axioms is20_terminal_wall_equation
#print axioms is48_even_terminal_wall_equation
#print axioms is48_odd_terminal_wall_equation
#print axioms is20_terminal_impossible
#print axioms is48_even_terminal_impossible
#print axioms is48_odd_terminal_impossible
#print axioms is20_terminal_impossible_pow
#print axioms is48_even_terminal_impossible_pow
#print axioms is48_odd_terminal_impossible_pow
#print axioms is20_depth0
#print axioms is20_depth1
#print axioms is20_depth2
#print axioms is48_even_depth0
#print axioms is48_even_depth1
#print axioms is48_even_depth2
#print axioms is48_odd_depth0
#print axioms is48_odd_depth1
#print axioms is48_odd_depth2

end BB6.Agent9FirstShallowCoordinateGate
