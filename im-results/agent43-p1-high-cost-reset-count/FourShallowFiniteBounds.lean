import ThreeShallowFiniteBounds

namespace BB6.Agent43FourShallowFinite

open BB6.Agent43TwoShallowFinite
open BB6.Agent43ThreeShallowFinite

/-- If the final depth-two run has length at least three, the fourth
successive source numerator must be divisible by its shallow factor times
512. -/
def fourthOverflow (n s u v w t1 t2 t3 t4 : Nat) : Bool := Id.run do
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
  let T1 := n+6+3*s
  let N1 : Int := 98*(p:Int)-(d:Int)-(C1:Int)*(P:Int)+(L1:Int)*(T1:Int)-(O1:Int)
  if N1 % ((2:Int)^alpha) != 0 then return false
  let I1 := N1 / ((2:Int)^alpha)
  if I1 % ((8:Int)^u) != 0 then return false
  let N2 : Int := I1/((8:Int)^u)-(C2:Int)*(P:Int)+
    (L2:Int)*(T1+alpha+3*u:Int)-(O2:Int)
  if N2 % ((2:Int)^beta) != 0 then return false
  let I2 := N2 / ((2:Int)^beta)
  if I2 % ((8:Int)^v) != 0 then return false
  let N3 : Int := I2/((8:Int)^v)-(C3:Int)*(P:Int)+
    (L3:Int)*(T1+alpha+3*u+beta+3*v:Int)-(O3:Int)
  if N3 % ((2:Int)^gamma) != 0 then return false
  let I3 := N3 / ((2:Int)^gamma)
  if I3 % ((8:Int)^w) != 0 then return false
  let N4 : Int := I3/((8:Int)^w)-(C4:Int)*(P:Int)+
    (L4:Int)*(T1+alpha+3*u+beta+3*v+gamma+3*w:Int)-(O4:Int)
  return N4 % ((2:Int)^delta*512) == 0

/-- Exact scalar terminal equality after four shallow transitions and five
arbitrary depth-two runs. -/
def fourBad (n s u v w r t1 t2 t3 t4 : Nat) : Bool := Id.run do
  let q := 8^s
  let P := 2^n
  let D := 14*n+92
  if P%q != 0 || D%q != 0 then return false
  let p := P/q
  let d := D/q
  let (alpha,C1,L1,O1) := triple t1
  let (beta,C2,L2,O2) := triple t2
  let (gamma,C3,L3,O3) := triple t3
  let (delta,C4,L4,O4) := triple t4
  let A1 := 2^alpha*8^u
  let A2 := 2^beta*8^v
  let A3 := 2^gamma*8^w
  let A4 := 2^delta*8^r
  let T1 := n+6+3*s
  let T2 := T1+alpha+3*u
  let T3 := T2+beta+3*v
  let T4 := T3+gamma+3*w
  let T5 := T4+delta+3*r
  let R1 := L1*T1-O1-d
  let R2 := L2*T2-O2
  let R3 := L3*T3-O3
  let R4 := L4*T4-O4
  let E := 112*T5-384
  let K := C1*q+C2*q*A1+C3*q*A1*A2+C4*q*A1*A2*A3-98
  return K*p == A1*(A2*(A3*(A4*E+R4)+R3)+R2)+R1

set_option maxRecDepth 4096
set_option maxHeartbeats 80000000

theorem four_first_overflow_false_76 :
    ∀ n : Fin 62, ∀ s : Fin 4, ∀ t : Fin 2,
      BB6.Agent43TwoShallowFinite.firstOverflow (n.val+14) s.val t.val = false := by decide

theorem four_second_overflow_false_76 :
    ∀ n : Fin 62, ∀ s : Fin 4, ∀ u : Fin 3,
      ∀ t1 : Fin 2, ∀ t2 : Fin 2,
      BB6.Agent43TwoShallowFinite.secondOverflow
        (n.val+14) s.val u.val t1.val t2.val = false := by decide

theorem four_third_overflow_false_76 :
    ∀ n : Fin 62, ∀ s : Fin 4, ∀ u : Fin 3, ∀ v : Fin 3,
      ∀ t1 : Fin 2, ∀ t2 : Fin 2, ∀ t3 : Fin 2,
      BB6.Agent43ThreeShallowFinite.thirdOverflow
        (n.val+14) s.val u.val v.val t1.val t2.val t3.val = false := by decide

theorem four_fourth_overflow_false_76 :
    ∀ n : Fin 62, ∀ s : Fin 4, ∀ u : Fin 3, ∀ v : Fin 3, ∀ w : Fin 3,
      ∀ t1 : Fin 2, ∀ t2 : Fin 2, ∀ t3 : Fin 2, ∀ t4 : Fin 2,
      fourthOverflow (n.val+14) s.val u.val v.val w.val
        t1.val t2.val t3.val t4.val = false := by decide

theorem no_four_small_bad_76 :
    ∀ n : Fin 62, ∀ s : Fin 4, ∀ u : Fin 3, ∀ v : Fin 3,
      ∀ w : Fin 3, ∀ r : Fin 3,
      ∀ t1 : Fin 2, ∀ t2 : Fin 2, ∀ t3 : Fin 2, ∀ t4 : Fin 2,
      fourBad (n.val+14) s.val u.val v.val w.val r.val
        t1.val t2.val t3.val t4.val = false := by decide

#print axioms four_first_overflow_false_76
#print axioms four_second_overflow_false_76
#print axioms four_third_overflow_false_76
#print axioms four_fourth_overflow_false_76
#print axioms no_four_small_bad_76

end BB6.Agent43FourShallowFinite
