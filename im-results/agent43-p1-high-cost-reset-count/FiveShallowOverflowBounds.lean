import FourShallowFiniteBounds
import FiveShallowFiniteBounds

namespace BB6.Agent43FiveShallowOverflow

open BB6.Agent43TwoShallowFinite
open BB6.Agent43ThreeShallowFinite
open BB6.Agent43FourShallowFinite
open BB6.Agent43FiveShallowFinite

/-- If the final depth-two run after five shallow transitions has length at
least three, the fifth successive source numerator is divisible by its
shallow factor times 512. All four earlier quotient checks are retained. -/
def fifthOverflow (n s u v w x t1 t2 t3 t4 t5 : Nat) : Bool := Id.run do
  let P := 2^n
  let D := 14*n+92
  let q := 8^s
  if P%q != 0 || D%q != 0 then return false
  let p := P/q
  let d := D/q
  let (alpha,C1,L1,O1) := triple t1
  let (beta,C2,L2,O2) := triple t2
  let (gamma,C3,L3,O3) := triple t3
  let (delta,C4,L4,O4) := triple t4
  let (epsilon,C5,L5,O5) := triple t5
  let T1 := n+6+3*s
  let N1 : Int := 98*(p:Int)-(d:Int)-(C1:Int)*(P:Int)+(L1:Int)*(T1:Int)-(O1:Int)
  if N1 % ((2:Int)^alpha) != 0 then return false
  let J1 := N1 / ((2:Int)^alpha)
  if J1 % ((8:Int)^u) != 0 then return false
  let T2 := T1+alpha+3*u
  let N2 : Int := J1/((8:Int)^u)-(C2:Int)*(P:Int)+(L2:Int)*(T2:Int)-(O2:Int)
  if N2 % ((2:Int)^beta) != 0 then return false
  let J2 := N2 / ((2:Int)^beta)
  if J2 % ((8:Int)^v) != 0 then return false
  let T3 := T2+beta+3*v
  let N3 : Int := J2/((8:Int)^v)-(C3:Int)*(P:Int)+(L3:Int)*(T3:Int)-(O3:Int)
  if N3 % ((2:Int)^gamma) != 0 then return false
  let J3 := N3 / ((2:Int)^gamma)
  if J3 % ((8:Int)^w) != 0 then return false
  let T4 := T3+gamma+3*w
  let N4 : Int := J3/((8:Int)^w)-(C4:Int)*(P:Int)+(L4:Int)*(T4:Int)-(O4:Int)
  if N4 % ((2:Int)^delta) != 0 then return false
  let J4 := N4 / ((2:Int)^delta)
  if J4 % ((8:Int)^x) != 0 then return false
  let T5 := T4+delta+3*x
  let N5 : Int := J4/((8:Int)^x)-(C5:Int)*(P:Int)+(L5:Int)*(T5:Int)-(O5:Int)
  return N5 % ((2:Int)^epsilon*512) == 0

set_option maxRecDepth 4096
set_option maxHeartbeats 80000000

/-- The first four overflow predicates are false on every root-compatible
(n,s) pair in 14<=n<=82 and every bounded preceding run/profile tuple. -/
theorem five_first_overflow_false :
    ∀ i : Fin rootPairs.length, ∀ t1 : Fin 2,
      BB6.Agent43TwoShallowFinite.firstOverflow
        (rootPairs.get i).1 (rootPairs.get i).2 t1.val = false := by decide

theorem five_second_overflow_false :
    ∀ i : Fin rootPairs.length, ∀ u : Fin 3,
      ∀ t1 : Fin 2, ∀ t2 : Fin 2,
      BB6.Agent43TwoShallowFinite.secondOverflow
        (rootPairs.get i).1 (rootPairs.get i).2 u.val t1.val t2.val = false := by decide

theorem five_third_overflow_false :
    ∀ i : Fin rootPairs.length, ∀ u : Fin 3, ∀ v : Fin 3,
      ∀ t1 : Fin 2, ∀ t2 : Fin 2, ∀ t3 : Fin 2,
      BB6.Agent43ThreeShallowFinite.thirdOverflow
        (rootPairs.get i).1 (rootPairs.get i).2 u.val v.val
        t1.val t2.val t3.val = false := by decide

theorem five_fourth_overflow_false :
    ∀ i : Fin rootPairs.length, ∀ u : Fin 3, ∀ v : Fin 3, ∀ w : Fin 3,
      ∀ t1 : Fin 2, ∀ t2 : Fin 2, ∀ t3 : Fin 2, ∀ t4 : Fin 2,
      BB6.Agent43FourShallowFinite.fourthOverflow
        (rootPairs.get i).1 (rootPairs.get i).2 u.val v.val w.val
        t1.val t2.val t3.val t4.val = false := by decide

/-- Exact fifth-overflow certificate: after four preceding depth-two runs
of length at most two, the fifth run cannot have length at least three. -/
theorem five_fifth_overflow_false :
    ∀ i : Fin rootPairs.length,
      ∀ u : Fin 3, ∀ v : Fin 3, ∀ w : Fin 3, ∀ x : Fin 3,
      ∀ t1 : Fin 2, ∀ t2 : Fin 2, ∀ t3 : Fin 2, ∀ t4 : Fin 2, ∀ t5 : Fin 2,
      fifthOverflow (rootPairs.get i).1 (rootPairs.get i).2
        u.val v.val w.val x.val t1.val t2.val t3.val t4.val t5.val = false := by decide

#print axioms fifthOverflow
#print axioms five_first_overflow_false
#print axioms five_second_overflow_false
#print axioms five_third_overflow_false
#print axioms five_fourth_overflow_false
#print axioms five_fifth_overflow_false

end BB6.Agent43FiveShallowOverflow
