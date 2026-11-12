import FiveShallowIntegerAlgebra

namespace BB6.Agent43FiveShallowFinite

open BB6.Agent43TwoShallowFinite

/-- Exact natural-number terminal equation for five shallow transitions and
six depth-two runs. The root divisor is checked before any divisions. -/
def fiveBad (n s u v w x r t1 t2 t3 t4 t5 : Nat) : Bool := Id.run do
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
  let (epsilon,C5,L5,O5) := triple t5
  let A1 := 2^alpha*8^u
  let A2 := 2^beta*8^v
  let A3 := 2^gamma*8^w
  let A4 := 2^delta*8^x
  let A5 := 2^epsilon*8^r
  let T1 := n+6+3*s
  let T2 := T1+alpha+3*u
  let T3 := T2+beta+3*v
  let T4 := T3+gamma+3*w
  let T5 := T4+delta+3*x
  let T6 := T5+epsilon+3*r
  let R1 := L1*T1-O1-d
  let R2 := L2*T2-O2
  let R3 := L3*T3-O3
  let R4 := L4*T4-O4
  let R5 := L5*T5-O5
  let E := 112*T6-384
  let K := C1*q+C2*q*A1+C3*q*A1*A2+C4*q*A1*A2*A3+
    C5*q*A1*A2*A3*A4-98
  return K*p == A1*(A2*(A3*(A4*(A5*E+R5)+R4)+R3)+R2)+R1

/-- All root-compatible (n,s) pairs for 14<=n<=82 and s<=3. -/
def rootPairs : List (Nat × Nat) := [
  (14,0),
  (14,1),
  (15,0),
  (16,0),
  (17,0),
  (18,0),
  (18,1),
  (19,0),
  (20,0),
  (21,0),
  (22,0),
  (22,1),
  (23,0),
  (24,0),
  (25,0),
  (26,0),
  (26,1),
  (27,0),
  (28,0),
  (29,0),
  (30,0),
  (30,1),
  (30,2),
  (30,3),
  (31,0),
  (32,0),
  (33,0),
  (34,0),
  (34,1),
  (35,0),
  (36,0),
  (37,0),
  (38,0),
  (38,1),
  (39,0),
  (40,0),
  (41,0),
  (42,0),
  (42,1),
  (43,0),
  (44,0),
  (45,0),
  (46,0),
  (46,1),
  (47,0),
  (48,0),
  (49,0),
  (50,0),
  (50,1),
  (51,0),
  (52,0),
  (53,0),
  (54,0),
  (54,1),
  (55,0),
  (56,0),
  (57,0),
  (58,0),
  (58,1),
  (59,0),
  (60,0),
  (61,0),
  (62,0),
  (62,1),
  (62,2),
  (63,0),
  (64,0),
  (65,0),
  (66,0),
  (66,1),
  (67,0),
  (68,0),
  (69,0),
  (70,0),
  (70,1),
  (71,0),
  (72,0),
  (73,0),
  (74,0),
  (74,1),
  (75,0),
  (76,0),
  (77,0),
  (78,0),
  (78,1),
  (79,0),
  (80,0),
  (81,0),
  (82,0),
  (82,1)
]

theorem rootPairs_length : rootPairs.length=90 := by decide

/-- The root divisor condition forces membership in the finite root-pair
certificate. -/
theorem rootPairs_complete :
    ∀ n : Fin 69, ∀ s : Fin 4,
      (14*(n.val+14)+92) % 8^s.val = 0 →
      (n.val+14,s.val) ∈ rootPairs := by decide

set_option maxRecDepth 4096
set_option maxHeartbeats 80000000

/-- The exact five-layer natural equation has no solutions on the complete
bounded core: all five profiles and all five run lengths in {0,1,2}. -/
theorem no_five_bad_rootPairs :
    ∀ i : Fin rootPairs.length,
      ∀ t1 : Fin 2, ∀ t2 : Fin 2, ∀ t3 : Fin 2,
      ∀ t4 : Fin 2, ∀ t5 : Fin 2,
      ∀ u : Fin 3, ∀ v : Fin 3, ∀ w : Fin 3,
      ∀ x : Fin 3, ∀ r : Fin 3,
        fiveBad (rootPairs.get i).1 (rootPairs.get i).2
          u.val v.val w.val x.val r.val
          t1.val t2.val t3.val t4.val t5.val = false := by decide

end BB6.Agent43FiveShallowFinite
