import Lean
import Lean.Elab.Tactic.Omega

namespace BB6.Agent43TwoShallowFinite

def triple (t : Nat) : Nat × Nat × Nat × Nat :=
  if t = 0 then (1, 588, 84, 232) else (2, 392, 56, 136)

/-- Necessary scalar terminal equality of any exact wall word containing two
shallow (depth zero/one) transitions, parameterized by all three two-runs. -/
def smallBad (n s u r t1 t2 : Nat) : Bool := Id.run do
  let q := 8^s
  let P := 2^n
  let D := 14*n+92
  if P%q != 0 || D%q != 0 then return false
  let p := P/q
  let d := D/q
  let (alpha,C1,L1,O1) := triple t1
  let (beta,C2,L2,O2) := triple t2
  let z := 2^alpha*8^u
  let v := 2^beta*8^r
  let T1 := n+6+3*s
  let T2 := T1+alpha+3*u
  let T3 := T2+beta+3*r
  let R1 := L1*T1-O1-d
  let R2 := L2*T2-O2
  let E := 112*T3-384
  let K := C1*q+C2*q*z-98
  return K*p == z*(v*E+R2)+R1

set_option maxRecDepth 4096
set_option maxHeartbeats 5000000

/-- Verifies finite residue nondivisibility in all possible root-prefix
indices n=14..47 and s=0..3; the first shallow run cannot have 3
or more subsequent depth-two steps. -/
def firstOverflow (n s t : Nat) : Bool := Id.run do
  let P := 2^n
  let D := 14*n+92
  let q := 8^s
  if P%q !=0 || D%q !=0 then return false
  let p := P/q
  let d := D/q
  let (alpha,C,L,O) := triple t
  let Ba := n+6+3*s
  let N : Int := 98*(p:Int)-(d:Int)-(C:Int)*(P:Int)+(L:Int)*(Ba:Int)-(O:Int)
  return N % ((2:Int)^alpha*512) == 0

/-- Finite check for a middle depth-two run of length u<=2:
the second shallow transition cannot be followed by >=3 two-steps. -/
def secondOverflow (n s u t1 t2 : Nat) : Bool := Id.run do
  let P := 2^n
  let D := 14*n+92
  let q := 8^s
  if P%q !=0 || D%q !=0 then return false
  let p := P/q
  let d := D/q
  let (alpha,C1,L1,O1) := triple t1
  let (beta,C2,L2,O2) := triple t2
  let Ba := n+6+3*s
  let N1 : Int := 98*(p:Int)-(d:Int)-(C1:Int)*(P:Int)+(L1:Int)*(Ba:Int)-(O1:Int)
  if N1 % ((2:Int)^alpha) != 0 then return false
  let I1 := N1 / ((2:Int)^alpha)
  if I1 % ((8:Int)^u) != 0 then return false
  let Imid := I1 / ((8:Int)^u)
  let Bc := Ba+alpha+3*u
  let N2 : Int := Imid-(C2:Int)*(P:Int)+(L2:Int)*(Bc:Int)-(O2:Int)
  return N2 % ((2:Int)^beta*512) == 0

set_option maxRecDepth 4096
set_option maxHeartbeats 5000000

theorem first_overflow_false :
    ∀ n : Fin 34, ∀ s : Fin 4, ∀ t : Fin 2,
    firstOverflow (n.val+14) s.val t.val = false := by decide

theorem second_overflow_false :
    ∀ n : Fin 34, ∀ s : Fin 4, ∀ u : Fin 3,
    ∀ t1 : Fin 2, ∀ t2 : Fin 2,
    secondOverflow (n.val+14) s.val u.val t1.val t2.val = false := by decide

#print axioms first_overflow_false
#print axioms second_overflow_false

theorem no_small_bad_test :
    ∀ n : Fin 34, ∀ s : Fin 4, ∀ u : Fin 3,
      ∀ r : Fin 3, ∀ t1 : Fin 2, ∀ t2 : Fin 2,
        smallBad (n.val+14) s.val u.val r.val t1.val t2.val = false := by decide

#print axioms BB6.Agent43TwoShallowFinite.no_small_bad_test
end BB6.Agent43TwoShallowFinite