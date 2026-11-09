import TwoShallowFiniteBounds
namespace BB6.Agent43ThreeShallowFinite
open BB6.Agent43TwoShallowFinite

/-- Exact third shallow numerator, checking all quotient preconditions. -/
def thirdOverflow (n s u v t1 t2 t3 : Nat) : Bool := Id.run do
 let P := 2^n
 let D := 14*n+92
 let q := 8^s
 if P%q != 0 || D%q != 0 then return false
 let p := P/q
 let d := D/q
 let (alpha,C1,L1,O1) := triple t1
 let (beta,C2,L2,O2) := triple t2
 let (gamma,C3,L3,O3) := triple t3
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
 return N3 % ((2:Int)^gamma*512) == 0

/-- Exact numerical wall equation for three shallows and three bounded runs. -/
def threeBad (n s u v r t1 t2 t3 : Nat) : Bool := Id.run do
 let P := 2^n
 let D := 14*n+92
 let q := 8^s
 if P%q != 0 || D%q != 0 then return false
 let p := P/q
 let d := D/q
 let (alpha,C1,L1,O1) := triple t1
 let (beta,C2,L2,O2) := triple t2
 let (gamma,C3,L3,O3) := triple t3
 let A1 := 2^alpha*8^u
 let A2 := 2^beta*8^v
 let A3 := 2^gamma*8^r
 let T1 := n+6+3*s
 let T2 := T1+alpha+3*u
 let T3 := T2+beta+3*v
 let T4 := T3+gamma+3*r
 let R1 := L1*T1-O1-d
 let R2 := L2*T2-O2
 let R3 := L3*T3-O3
 let E := 112*T4-384
 let K := C1*q+C2*q*A1+C3*q*A1*A2-98
 return K*p == A1*(A2*(A3*E+R3)+R2)+R1

set_option maxRecDepth 4096
set_option maxHeartbeats 8000000

theorem first_overflow_false_58 :
 ∀ n : Fin 44, ∀ s : Fin 4, ∀ t : Fin 2,
 firstOverflow (n.val+14) s.val t.val = false := by decide

theorem second_overflow_false_58 :
 ∀ n : Fin 44, ∀ s : Fin 4, ∀ u : Fin 3,
 ∀ t1 : Fin 2, ∀ t2 : Fin 2,
 secondOverflow (n.val+14) s.val u.val t1.val t2.val = false := by decide

theorem third_overflow_false_58 :
 ∀ n : Fin 44, ∀ s : Fin 4, ∀ u : Fin 3, ∀ v : Fin 3,
 ∀ t1 : Fin 2, ∀ t2 : Fin 2, ∀ t3 : Fin 2,
 thirdOverflow (n.val+14) s.val u.val v.val t1.val t2.val t3.val = false := by decide

theorem no_three_small_bad_58 :
 ∀ n : Fin 44, ∀ s : Fin 4, ∀ u : Fin 3, ∀ v : Fin 3, ∀ r : Fin 3,
 ∀ t1 : Fin 2, ∀ t2 : Fin 2, ∀ t3 : Fin 2,
 threeBad (n.val+14) s.val u.val v.val r.val t1.val t2.val t3.val = false := by decide

#print axioms first_overflow_false_58
#print axioms second_overflow_false_58
#print axioms third_overflow_false_58
#print axioms no_three_small_bad_58
end BB6.Agent43ThreeShallowFinite
