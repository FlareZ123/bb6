import Lean.Elab.Tactic.Omega

/-!
# E/B/P2 packet index cocycle

This module formalizes the exact affine identities recorded in
`IndexCocycle.md`. It proves arithmetic consequences of the already source-
certified macro shapes; it does not prove any additional source transition or
that every resulting orbit terminates.
-/

namespace BB6.Agent2IndexCocycle

/-- E packet followed by E: `k' = (8*k+5)/3`. -/
theorem e_to_e (k k' : Nat) (h : 3*k' = 8*k+5) :
    3*(k'+1) = 8*(k+1) := by omega

/-- E packet followed by B: `k' = (8*k+7)/3`. -/
theorem e_to_b (k k' : Nat) (h : 3*k' = 8*k+7) :
    3*(5*k'+7) = 8*(5*k+7) := by omega

/-- B packet followed by E: `k' = (8*k+6)/3`. -/
theorem b_to_e (k k' : Nat) (h : 3*k' = 8*k+6) :
    3*(5*k'+6) = 8*(5*k+6) := by omega

/-- B packet followed by B: `k' = (8*k+8)/3`. -/
theorem b_to_b (k k' : Nat) (h : 3*k' = 8*k+8) :
    3*(5*k'+8) = 8*(5*k+8) := by omega

/-- Fixed-tail E,p=2 reset followed by an E-shaped output. -/
theorem p2_to_e (k k' : Nat) (h : 3*k' = 8*k+1) :
    3*(5*k'+1) = 8*(5*k+1) := by omega

/-- An ordinary E packet call consumes one unit of `q+p` resource. -/
theorem e_resource (q p : Nat) (hp : 3 ≤ p) :
    (q+2) + (p-3) + 1 = q+p := by omega

/-- An ordinary B packet call consumes one unit of `q+p` resource. -/
theorem b_resource (q p : Nat) (hq : 1 ≤ q) :
    (q-1) + p + 1 = q+p := by omega

/-- A fixed-tail P2 reset changes `q+p` from `q+2` to `2*q+6`. -/
theorem p2_resource_delta (q : Nat) :
    2*q+6 = (q+2) + (q+4) := by omega

#print axioms e_to_e
#print axioms e_to_b
#print axioms b_to_e
#print axioms b_to_b
#print axioms p2_to_e
#print axioms e_resource
#print axioms b_resource
#print axioms p2_resource_delta

end BB6.Agent2IndexCocycle
