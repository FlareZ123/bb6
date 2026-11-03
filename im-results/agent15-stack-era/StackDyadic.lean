/-
Binary-word encoding of the standalone DeepMind-derived digit-stack equations.
The integer code is a finite odd binary word with no adjacent zero digits,
or zero for the empty stack. Verification remains model-local; StackGate.lean
itself transcribes rather than imports the original Cryptids module.
-/
import StackGate
import Lean.Elab.Tactic.Omega

namespace Agent15Stack

def encode : List Nat → Nat
  | [] => 0
  | a :: L => 2^(a+1)*(2*encode L+1)-1

theorem encode_cons_succ (a : Nat) (L : List Nat) :
    encode (a::L)+1 = 2^(a+1)*(2*encode L+1) := by
  simp only [encode]
  have hp : 0 < 2^(a+1)*(2*encode L+1) :=
    Nat.mul_pos (Nat.two_pow_pos _) (by omega)
  omega

theorem encode_bump (L : List Nat) :
    encode (bump L) = 2*encode L+1 := by
  cases L with
  | nil => decide
  | cons a L =>
    change encode ((a+1)::L) = 2*(encode (a::L))+1
    have h1 : encode ((a+1)::L)+1 = 2*(encode (a::L)+1) := by
      rw [encode_cons_succ (a+1) L, encode_cons_succ a L]
      have ha : a+1+1 = (a+1)+1 := rfl
      rw [Nat.pow_succ]
      ac_rfl
    omega

theorem encode_bumpN (n : Nat) (L : List Nat) :
    encode (bumpN n L)+1 = 2^n*(encode L+1) := by
  induction n generalizing L with
  | zero => simp [bumpN]
  | succ n ih =>
    calc
      encode (bumpN (n+1) L)+1 = 2^n*(encode (bump L)+1) := by
        simpa [bumpN] using ih (bump L)
      _ = 2^n*(2*(encode L+1)) := by
        rw [encode_bump, show 2*encode L+1+1 = 2*(encode L+1) by omega]
      _ = 2^(n+1)*(encode L+1) := by
        rw [Nat.pow_succ]
        ac_rfl

theorem encode_zero (L : List Nat) :
    encode (0::L) = 4*encode L+1 := by
  have h := encode_cons_succ 0 L
  have h' : encode (0::L)+1 = 2*(2*encode L+1) := by simpa using h
  omega

theorem encode_one (L : List Nat) :
    encode (1::L) = 8*encode L+3 := by
  have h := encode_cons_succ 1 L
  have h' : encode (1::L)+1 = 4*(2*encode L+1) := by simpa using h
  omega

theorem encode_D_one (L R : List Nat) :
    encode (bump L)*4 = encode (1::L)+1 ∧
    encode (0::R) = 4*encode R+1 := by
  constructor
  · rw [encode_bump, encode_one]
    omega
  · exact encode_zero R

theorem encode_D_zero_one (L R : List Nat) :
    encode (bumpN 4 L) = 4*encode (0::L)+11 ∧
    4*encode (bump R) = encode (1::R)+1 := by
  constructor
  · have h := encode_bumpN 4 L
    have h' : encode (bumpN 4 L)+1 = 16*(encode L+1) := by simpa using h
    rw [encode_zero]
    omega
  · rw [encode_bump, encode_one]
    omega

theorem encode_FR_zero (R : List Nat) :
    2*encode (bump R)=encode (0::R)+1 := by
  rw [encode_bump, encode_zero]
  omega

#eval encode [0,0]
#eval encode [0,1]
#eval encode [1]
#eval encode [2]

#print axioms encode_bumpN
#print axioms encode_D_zero_one

end Agent15Stack
