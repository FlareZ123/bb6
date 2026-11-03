import ZeroOddRange
import BounceEvenExact
import Lean.Elab.Tactic.Omega

namespace BB6.Agent3
open BB6.Agent46

/-- The exceptional a=1 source yields an infinite dyadic odd-output
    family: every parameter r produces a TRUE original-source section edge. -/
theorem odd_one_source (r : Nat) :
    secNext (1,32*4^r-(8+3*r))=some (0,32*4^r-1) := by
  let P : Nat := 4^r
  let k : Nat := 32*P-(8+3*r)
  let y : Nat := 32*P-1
  have hp : r+1≤P := parent_four_ge r
  have hk : k+(8+3*r)=32*P := by dsimp [k]; omega
  have hk4 : 4≤k := by omega
  have hn : 2^(2*r+1)=2*P := by
    rw [show 2*r+1=(2*r)+1 by omega,Nat.pow_succ,parent_two_pow_double]
    omega
  have hy : 5≤y := by dsimp [y]; omega
  have hsum : 0+y+1=2^(2*r+1)*16 := by
    rw [hn]
    dsimp [y]
    omega
  have hcost : (2*k-3)+16+3*(2*r+1)=0+2*y+2 := by
    dsimp [y]
    omega
  have hb : (bounce 4 (2*k-3)).2=some (0,y) :=
    (bounce_even_output_exact 4 (2*k-3) 0 y (by decide) hy).mpr
      ⟨2*r+1,hsum,hcost⟩
  change secNext (1,k)=some (0,y)
  simp only [secNext,exactSection,if_neg (by omega:1≠0),
    if_pos rfl,if_neg (by omega:k≠0),if_neg (by omega:k≠1),
    if_neg (by omega:k≠2),if_neg (by omega:k≠3)]
  exact hb

/-- An all-depth and two-parameter high odd-first source branch for every
    odd target y=4*4^r*(u+2)-1. Every source is a genuine section return. -/
theorem odd_high_source (r u : Nat) (hu : 1≤u) :
    secNext (2*u+1, (4*4^r*(u+2)-1)-(u+4+3*r))
      =some (0,4*4^r*(u+2)-1) := by
  let P : Nat := 4^r*(u+2)
  let y : Nat := 4*P-1
  let a : Nat := 2*u+1
  let k : Nat := y-(u+4+3*r)
  let K : Nat := a-1
  have hpow : r+1≤4^r := parent_four_ge r
  have hP1 : u+2≤P := by
    have hh := Nat.mul_le_mul_right (u+2) (by omega : 1≤4^r)
    dsimp [P]
    simpa using hh
  have hP2 : 3*(r+1)≤P := by
    have hh := Nat.mul_le_mul_left 3 hpow
    have ht : 3*4^r≤4^r*(u+2) :=
      Nat.mul_le_mul_left (4^r) (by omega : 3≤u+2)
    dsimp [P]
    omega
  have hA : a=2*u+1 := rfl
  have hK : K=2*u := by dsimp [K,a]; omega
  have hY : y+1=4*P := by dsimp [y]; omega
  have hk : k+(u+4+3*r)=y := by dsimp [k]; omega
  have ha2 : 2≤a := by omega
  have hk1 : 1≤k := by omega
  have hreg : a<2*k := by omega
  have hodd : K%2=0 := by omega
  have hy : 5≤y := by omega
  have hsum : 0+y+1=2^(2*r)*(2*K+8) := by
    rw [parent_two_pow_double]
    have heq : 2*K+8=4*(u+2) := by omega
    rw [heq]
    dsimp [P]
    calc
      0+y+1 = 4*(4^r*(u+2)) := by omega
      _=4^r*(4*(u+2)) := by ac_rfl
  have hcost : (2*k-a+3)+(2*K+8)+3*(2*r)=0+2*y+2 := by
    omega
  have hb : (bounce K (2*k-a+3)).2=some (0,y) :=
    (bounce_even_output_exact K (2*k-a+3) 0 y hodd hy).mpr
      ⟨2*r,hsum,hcost⟩
  change secNext (a,k)=some (0,y)
  simp only [secNext,exactSection,if_neg (by omega:a≠0),
    if_neg (by omega:a≠1),if_neg (by omega:k≠0),
    if_neg (by omega:¬2*k≤a)]
  exact hb

#print axioms odd_one_source
#print axioms odd_high_source
end BB6.Agent3
