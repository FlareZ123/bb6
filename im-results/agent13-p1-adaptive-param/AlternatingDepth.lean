import BlockPotential
namespace BB6.Agent13Alternation
open BB6.Agent13Block

/-- Exact consecutive pairs of P1 scalar inverse depths (0,1). -/
inductive Run01 (L : Nat) : Nat → Nat → Nat → Prop where
| zero (m z : Nat) : Run01 L 0 m z
| more {N m z z1 v z2 : Nat} : Run01 L N (m+3) z2 →
    2*z1+1=L+m+z → z1=2*v →
    2*z2+1=L+m+2+v → Run01 L (N+1) m z

/-- Exact consecutive pairs of P1 scalar inverse depths (1,0). -/
inductive Run10 (L : Nat) : Nat → Nat → Nat → Prop where
| zero (m z : Nat) : Run10 L 0 m z
| more {N m z v z1 z2 : Nat} : Run10 L N (m+3) z2 →
    z=2*v → 2*z1+1=L+m+1+v →
    2*z2+1=L+m+2+z1 → Run10 L (N+1) m z

theorem pair01_block (L N m z : Nat) (hr:Run01 L N m z) :
    RunBlock 8 5 3 3 L N m z := by
  induction hr with
  | zero m z => exact .zero m z
  | @more N m z z1 v z2 ih h0 hd h1 ihb =>
      have he : 8*z2=z+5*(L+m)+3 := by omega
      exact RunBlock.more ihb he

theorem pair10_block (L N m z : Nat) (hr:Run10 L N m z) :
    RunBlock 8 6 3 4 L N m z := by
  induction hr with
  | zero m z => exact .zero m z
  | @more N m z v z1 z2 ih hdiv h1 h0 ihb =>
      have he : 8*z2=z+6*(L+m)+4 := by omega
      exact RunBlock.more ihb he

/-- Every inverse-depth 01 alternation has a bounded number of periods. -/
theorem no_infinite_01 (L m z : Nat)
    (hall : ∀ N : Nat, Run01 L N m z) : False := by
  apply no_infinite_block 8 5 3 3 L m z (by decide) (by decide)
  intro N
  exact pair01_block L N m z (hall N)

/-- Every inverse-depth 10 alternation has a bounded number of periods. -/
theorem no_infinite_10 (L m z : Nat)
    (hall : ∀ N : Nat, Run10 L N m z) : False := by
  apply no_infinite_block 8 6 3 4 L m z (by decide) (by decide)
  intro N
  exact pair10_block L N m z (hall N)

#print axioms no_infinite_01
#print axioms no_infinite_10
end BB6.Agent13Alternation
