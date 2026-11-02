import BounceOddExact
import FastSectionDef
import Lean.Elab.Tactic.Omega

namespace BB6.Agent3
open BB6.Agent46

/-- Growth bound used to show that every parent is a valid natural
    high-branch source state, even at unbounded bounce recursion depth. -/
theorem parent_four_ge (r : Nat) : r+1 ≤ 4^r := by
  induction r with
  | zero => decide
  | succ r ih =>
    rw [Nat.pow_succ]
    omega

theorem parent_two_pow_double (r : Nat) : 2^(2*r)=4^r := by
  calc
    2^(2*r) = (2^2)^r := Nat.pow_mul 2 2 r
    _ = 4^r := by simp

/-- For each r,s the displayed genuine source takes exactly one section
    return to the common target (0,16*4^(r+s)). The original recursive
    bounce runs to odd-terminal depth 2r+1 without any cutoff. -/
theorem unbounded_source_parent (r s : Nat) :
    secNext (4*4^s-2,16*4^(r+s)-(2*4^s+3*r+4))
      = some (0,16*4^(r+s)) := by
  let P : Nat := 4^(r+s)
  let Q : Nat := 4^s
  let a : Nat := 4*Q-2
  let k : Nat := 16*P-(2*Q+3*r+4)
  let K : Nat := a-1
  let y : Nat := 16*P
  have hQ : 1≤Q := by dsimp [Q]; exact Nat.one_le_pow s 4 (by decide)
  have hR : r+1≤4^r := parent_four_ge r
  have hP : P=4^r*Q := by dsimp [P,Q]; exact Nat.pow_add 4 r s
  have hQR : Q≤P := by
    rw [hP]
    have h := Nat.mul_le_mul_right Q (by omega : 1≤4^r)
    simpa using h
  have hRP : r≤P := by
    rw [hP]
    have h := Nat.le_mul_of_pos_right (4^r) (by omega : 0<Q)
    omega
  have ha : a+2=4*Q := by dsimp [a]; omega
  have hk : k+(2*Q+3*r+4)=16*P := by dsimp [k]; omega
  have hkPos : 1≤k := by omega
  have haPos : 2≤a := by omega
  have hreg : a<2*k := by omega
  have hOdd : K%2=1 := by dsimp [K]; omega
  have hy : 4≤y := by dsimp [y]; omega
  have hnum : 2^(2*r+1)=2*4^r := by
    rw [show 2*r+1=(2*r)+1 by omega, Nat.pow_succ,parent_two_pow_double]
    omega
  have hs : 0+y=2^(2*r+1)*(2*K+6) := by
    have haeq : 2*K+6=8*Q := by omega
    rw [haeq,hnum]
    dsimp [y]
    rw [hP]
    calc
      0 + 16*(4^r*Q) = (2*8)*(4^r*Q) := by omega
      _ = (2*4^r)*(8*Q) := by ac_rfl
  have hc : (2*k-a+3)+(2*K+6)+3*(2*r+1)=0+2*y := by
    omega
  have hb : (bounce K (2*k-a+3)).2=some (0,y) := by
    exact (bounce_odd_output_exact K (2*k-a+3) 0 y hOdd hy).mpr
      ⟨2*r+1,hs,hc⟩
  change secNext (a,k)=some (0,y)
  simp only [secNext,exactSection,if_neg (by omega : a≠0),
    if_neg (by omega : a≠1),if_neg (by omega : k≠0),
    if_neg (by omega : ¬2*k≤a)]
  exact hb

/-- For each fixed target (0,16*4^t), every s≤t specifies a
    genuine source section edge. -/
theorem family_parent (t s : Nat) (h : s≤t) :
    secNext (4*4^s-2,16*4^t-(2*4^s+3*(t-s)+4))
      = some (0,16*4^t) := by
  have hh := unbounded_source_parent (t-s) s
  have he : t-s+s=t := by omega
  simpa only [he] using hh

/-- Source first coordinates for distinct s are strictly increasing. -/
theorem parent_first_strict (s u : Nat) (h : s<u) :
    4*4^s-2 < 4*4^u-2 := by
  have hp := Nat.pow_lt_pow_right (by decide : 1<4) h
  have hs := Nat.one_le_pow s 4 (by decide)
  have hu := Nat.one_le_pow u 4 (by decide)
  omega

/-- Every target (0,16*4^t) has at least t+1 distinct immediate sources.
    This establishes an unbounded-in-degree obstruction for naive finite
    predecessor enumeration of the unbounded original section map. -/
theorem parent_neq (t s u : Nat) (_hs : s≤t) (_hu : u≤t) (h : s≠u) :
    (4*4^s-2,16*4^t-(2*4^s+3*(t-s)+4)) ≠
    (4*4^u-2,16*4^t-(2*4^u+3*(t-u)+4)) := by
  intro he
  have hf : 4*4^s-2=4*4^u-2 := congrArg Prod.fst he
  by_cases hlt : s<u
  · have hh := parent_first_strict s u hlt
    omega
  · have hgt : u<s := by omega
    have hh := parent_first_strict u s hgt
    omega

#print axioms unbounded_source_parent
#print axioms family_parent
#print axioms parent_neq
end BB6.Agent3
