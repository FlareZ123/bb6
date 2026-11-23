import CLine
import PrimitiveRankUnique
import Lean.Elab.Tactic.Omega

namespace BB6.PrimitiveRankRigidity
open BB6CLine

/-- Original-source sweep, preserving a+2k+c exactly. -/
theorem source_sweep : nextC (1,0,4)=some (0,1,3) := by decide

/-- Original-source reset family of arbitrary right-counter size. -/
theorem source_zero (k : Nat) :
    nextC (0,k,0)=some (1,0,2*k+2) := by rfl

/-- Original-source even zero-left bounce family. -/
theorem source_even_bounce (j : Nat) :
    nextC (0,2*j,4)=some (4*j+2,2,1) := by
  have he : (2*j)%2=0 := by omega
  have hdiv : (2*j)/2=j := by omega
  simp [nextC,he,hdiv]

private theorem source_rank (a k c x y z : Nat)
    (h : nextC (a,k,c)=some (x,y,z)) :
    a+2*k+c≤x+2*y+z := by
  have hh := BB6CLine.rank_mono h
  simpa only [rankC] using hh

/-- Complete original-source linear-monotonicity classification. -/
theorem machine_c_primitive_linear_unique (u v w : Nat) :
    (∀ a k c x y z, nextC (a,k,c)=some (x,y,z) →
       weight3 u v w a k c≤weight3 u v w x y z)
     ↔ w=u ∧ v=2*u :=
  unique_linear_primitive nextC source_rank source_sweep source_zero source_even_bounce u v w

/-- No globally strictly increasing nonnegative linear primitive rank. -/
theorem machine_c_primitive_no_strict_linear (u v w : Nat) :
    ¬ (∀ a k c x y z, nextC (a,k,c)=some (x,y,z) →
       weight3 u v w a k c<weight3 u v w x y z) :=
  no_strict_linear_primitive nextC source_rank source_sweep source_zero source_even_bounce u v w

#print axioms source_sweep
#print axioms source_even_bounce
#print axioms machine_c_primitive_linear_unique
#print axioms machine_c_primitive_no_strict_linear
end BB6.PrimitiveRankRigidity
