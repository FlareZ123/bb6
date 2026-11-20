import Std

/-!
Exact arithmetic alignment for a depth-three P2/E/B/B/A reset cylinder.

This file proves only the natural-number identities used to align the
resulting L(a,2,2) section with the already-known 86-step DRegular seed
L(24956,2,2). It does not import or assert any Turing-machine source run.
-/

set_option maxRecDepth 8192
set_option maxHeartbeats 100000000

namespace BB6.Agent37D3SecondReturnAlignment

def seedS : Nat := 202789636786509251933665269483979866281743
def seedK : Nat := 147833645217365244659641981453821322519390957
def modulus : Nat := 3^87
def baseExitK : Nat := 35761011052497844733597143642740448447362
def baseExitA : Nat := 107283033157493534200791430928221345342090
def P0 : Nat := 1315608

def familyS (v : Nat) : Nat := seedS + modulus*v
def familyK (v : Nat) : Nat := 729*familyS v + 310
def familyKExplicit (v : Nat) : Nat := seedK + 3^93*v
def familyH (v : Nat) : Nat := 54*familyS v + 23
def familyT (v : Nat) : Nat := 4096*familyS v + 1744
def familyKA (v : Nat) : Nat := 64*familyT v + 45
def familyEndpoint (v : Nat) : Nat := 8*familyKA v + 28
def packetShift (v : Nat) : Nat := 3*(P0 + 2^21*v)
def shiftedExitK (v : Nat) : Nat := baseExitK + 8^86*(P0 + 2^21*v)

theorem modulus_exact : modulus = 323257909929174534292273980721360271853387 := by decide

theorem familyK_explicit (v : Nat) :
    familyK v = familyKExplicit v := by
  simp [familyK, familyKExplicit, familyS, seedS, seedK, modulus]
  omega

theorem reset_3adic_alignment (v : Nat) :
    2*familyK v+1 = 3^3*familyH v := by
  simp [familyK, familyH, familyS]
  omega

theorem E_chain_BB_index (v : Nat) :
    1+4*8^3*familyH v = 27*familyT v+17 := by
  simp [familyH, familyT, familyS]
  omega

theorem A_marker_endpoint (v : Nat) :
    familyEndpoint v =
      24956 + modulus*(P0 + 2^21*v) := by
  simp [familyEndpoint, familyKA, familyT, familyS,
    modulus, P0, seedS]
  omega

theorem input_shift_for_86_steps (v : Nat) :
    familyEndpoint v =
      24956 + 3^86*packetShift v := by
  rw [A_marker_endpoint]
  simp [packetShift, modulus]
  omega

theorem base_exit_shape :
    baseExitA = 3*baseExitK+4 := by decide

theorem transported_exit_shape (v : Nat) :
    baseExitA + 8^86*packetShift v =
      3*shiftedExitK v+4 := by
  rw [base_exit_shape]
  simp [packetShift, shiftedExitK]
  omega

theorem q5_exit_parameter (v : Nat) :
    shiftedExitK v = baseExitK + 8^86*(P0 + 2^21*v) := by
  rfl

#print axioms familyK_explicit
#print axioms reset_3adic_alignment
#print axioms E_chain_BB_index
#print axioms A_marker_endpoint
#print axioms input_shift_for_86_steps
#print axioms transported_exit_shape
#print axioms q5_exit_parameter

end BB6.Agent37D3SecondReturnAlignment
