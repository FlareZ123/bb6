import BB429JuncHeadExcursion
import Lean.Elab.Tactic.Omega

namespace BB429High2Tail

open BB429OddExcursion BB429SourceE1Return BB429SourceE1Delta
open BB429JuncHeadExcursion

/-- The leftward A/F boundary family at the end of the high-2 excursion. -/
def midAaux (v k : Nat) : Zipper :=
  z 0 (ones (2*v+1) ++ [false] ++ ones 6) true
    (tens k ++ [false,true])

/-- Two A/F pairs consume two left ones and prepend one 01 pair on the right. -/
theorem midAaux_step2 (v k : Nat) :
    runWithDelta 2 (midAaux (v+1) k) =
      some (midAaux v (k+1), -2) := by
  rfl

/-- The six-step prefix from the w=1 mid-A configuration to midAaux. -/
theorem midApos_to_midAaux (v : Nat) :
    runWithDelta 6 (midApos 1 (v+1) 1) =
      some (midAaux v 3, -6) := by
  rfl

/-- Repeated two-step reduction removes all v left pairs and transfers them
    into the right alternating block. -/
theorem midAaux_reduce_v (v k : Nat) :
    runWithDelta (2*v) (midAaux v k) =
      some (midAaux 0 (k+v), -((2*v : Nat) : Int)) := by
  induction v with
  | zero =>
      simp [runWithDelta]
  | succ v ih =>
      rw [show 2*(v+1) = 2 + 2*v by omega, runWithDelta_add,
        midAaux_step2]
      simp only [Option.bind_some]
      rw [ih]
      simp [Nat.add_assoc, Int.natCast_add, Int.natCast_mul]

/-- Once the single v=0 base family is proved, the complete midApos-to-Junc
    suffix follows uniformly. This isolates the remaining proof obligation. -/
theorem midApos_to_junc0_of_base (v : Nat) (hv : 1≤v)
    (hbase : ∀ k : Nat,
      runWithDelta (4*k+36) (midAaux 0 k) =
        some (junc 0 0 (2*k+6), -4)) :
    runWithDelta (6*v+48) (midApos 1 v 1) =
      some (junc 0 0 (2*v+10), -((2*v+8 : Nat) : Int)) := by
  have hsub : (v-1)+1 = v := Nat.sub_add_cancel hv
  have hfirst :
      runWithDelta 6 (midApos 1 v 1) =
        some (midAaux (v-1) 3, -6) := by
    simpa [hsub] using midApos_to_midAaux (v-1)
  have hreduce :
      runWithDelta (2*(v-1)) (midAaux (v-1) 3) =
        some (midAaux 0 (v+2), -((2*(v-1) : Nat) : Int)) := by
    have h := midAaux_reduce_v (v-1) 3
    simpa [show 3+(v-1)=v+2 by omega] using h
  have hlast := hbase (v+2)
  have htotal :
      runWithDelta (6 + (2*(v-1) + (4*(v+2)+36))) (midApos 1 v 1) =
        some (junc 0 0 (2*(v+2)+6),
          (-6 : Int) + (-((2*(v-1) : Nat) : Int)) + (-4)) := by
    rw [runWithDelta_add, hfirst]
    simp only [Option.bind_some]
    rw [runWithDelta_add, hreduce]
    simp only [Option.bind_some]
    rw [hlast]
    simp
  have htime : 6 + (2*(v-1) + (4*(v+2)+36)) = 6*v+48 := by omega
  rw [← htime]
  simpa [Int.natCast_add, Int.natCast_mul] using htotal

#print axioms midAaux_step2
#print axioms midApos_to_midAaux
#print axioms midAaux_reduce_v
#print axioms midApos_to_junc0_of_base

end BB429High2Tail
