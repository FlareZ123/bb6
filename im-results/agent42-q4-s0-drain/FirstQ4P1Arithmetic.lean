import Agent8S1Encoder
import Lean.Elab.Tactic.Omega

/-!
# Isolated arithmetic core for the first-q4-to-P1 reparameterization

This module imports only the source-exact S1 encoder.  It isolates the
arithmetic and BinDec identity from Agent 48's larger P1 dependency
closure, so the core lemma can be locally preflighted independently.
-/

namespace BB6Coverage.Agent42FirstQ4P1Arithmetic

open BB6Coverage.Agent8S1Encoder

def firstQ4P1M (L A : Nat) : Nat :=
  2^A * (2^(L+2)-1)

def firstQ4P1Width (L A : Nat) : Nat :=
  A+L+1

def firstQ4P1Value (L A : Nat) : Nat :=
  2^(A-1) * (2^(L+2)-1) - 1

/-- The product expression for M is the exact exponent-minus-block
expression used in Agent 24's firstQ4Left2. -/
theorem firstQ4P1M_eq_rootM (L A : Nat) :
    firstQ4P1M L A = 2^(L+A+2)-2^A := by
  unfold firstQ4P1M
  rw [Nat.mul_sub_left_distrib]
  simp only [Nat.mul_one]
  have hpow : 2^A * 2^(L+2) = 2^(L+A+2) := by
    rw [← Nat.pow_add]
    congr 1
    omega
  rw [hpow]

/-- The reparameterized value fits the one-smaller BinDec width. -/
theorem firstQ4P1Value_lt (L A : Nat) (hA : 0 < A) :
    firstQ4P1Value L A < 2^(firstQ4P1Width L A) := by
  unfold firstQ4P1Value firstQ4P1Width
  have hC : 2^(L+2)-1 < 2^(L+2) :=
    Nat.sub_lt (Nat.pow_pos (by decide)) (by decide)
  have hprod :
      2^(A-1) * (2^(L+2)-1) <
        2^(A-1) * 2^(L+2) :=
    Nat.mul_lt_mul_of_pos_left hC (Nat.pow_pos (by decide))
  have hpow :
      2^(A-1) * 2^(L+2) = 2^(A+L+1) := by
    rw [← Nat.pow_add]
    congr 1
    omega
  exact Nat.lt_of_le_of_lt (Nat.sub_le _ _) (by simpa [hpow] using hprod)

/-- The root checkpoint's odd BinDec argument is exactly 2*q+1. -/
theorem firstQ4P1Value_odd (L A : Nat) (hA : 0 < A) :
    2 * firstQ4P1Value L A + 1 = firstQ4P1M L A - 1 := by
  have hpow2 : 4 ≤ 2^(L+2) := by
    have h := Nat.pow_le_pow_right (by decide : 0 < 2)
      (show 2 ≤ L+2 by omega)
    have hfour : (2:Nat)^2 = 4 := by decide
    rw [hfour] at h
    exact h
  have hC : 1 ≤ 2^(L+2)-1 := by omega
  have hprod : 0 < 2^(A-1) * (2^(L+2)-1) :=
    Nat.mul_pos (Nat.pow_pos (by decide)) (by omega)
  have hsub :
      (2^(A-1) * (2^(L+2)-1) - 1) + 1 =
        2^(A-1) * (2^(L+2)-1) :=
    Nat.sub_add_cancel (by omega)
  have hpowA : 2^A = 2^(A-1)*2 := by
    calc
      2^A = 2^((A-1)+1) := by congr 1; omega
      _ = 2^(A-1)*2 := by rw [Nat.pow_succ]
  have hmul :
      2 * (2^(A-1) * (2^(L+2)-1)) =
        2^A * (2^(L+2)-1) := by
    calc
      2 * (2^(A-1) * (2^(L+2)-1)) =
          (2*2^(A-1)) * (2^(L+2)-1) :=
            (Nat.mul_assoc 2 (2^(A-1)) (2^(L+2)-1)).symm
      _ = (2^(A-1)*2) * (2^(L+2)-1) := by
            rw [Nat.mul_comm 2 (2^(A-1))]
      _ = 2^A * (2^(L+2)-1) := by rw [← hpowA]
  have hcancel :
      2 * (2^(A-1) * (2^(L+2)-1) - 1) + 1 =
        2 * (2^(A-1) * (2^(L+2)-1)) - 1 := by omega
  calc
    2 * firstQ4P1Value L A + 1 =
        2 * (2^(A-1) * (2^(L+2)-1) - 1) + 1 := rfl
    _ = 2 * (2^(A-1) * (2^(L+2)-1)) - 1 := hcancel
    _ = 2^A * (2^(L+2)-1) - 1 := by rw [hmul]
    _ = firstQ4P1M L A - 1 := rfl

/-- The same odd identity, in the exact argument form of firstQ4Left2. -/
theorem firstQ4P1Value_odd_root (L A : Nat) (hA : 0 < A) :
    2 * firstQ4P1Value L A + 1 =
      2^(L+A+2)-2^A-1 := by
  rw [← firstQ4P1M_eq_rootM L A]
  exact firstQ4P1Value_odd L A hA

/-- The exact root first-checkpoint left side from Agent 24's source. -/
def firstQ4P1Left (L A : Nat) : List Bool :=
  [false,true,true] ++
    binDec (L+A+2) (2^(L+A+2)-2^A-1) ++ lh

/-- The first q4 checkpoint's right-facing side, starting at cell 2
(head coordinate 1). -/
def firstQ4P1Right (z : Nat) : List Bool :=
  [false,false,false] ++ List.replicate (3*z+5) true ++
    [false,false] ++ d1pow (2^z) ++ [false,false,false,false]

/-- Exact BinDec reparameterization of the root checkpoint word. -/
theorem firstQ4P1BinDec_reparam (L A : Nat) (hA : 0 < A) :
    binDec (L+A+2) (2^(L+A+2)-2^A-1) =
      d0 ++ binDec (A+L+1) (firstQ4P1Value L A) := by
  have hlen : L+A+2 = (A+L+1)+1 := by omega
  have hodd := firstQ4P1Value_odd_root L A hA
  rw [hlen] at hodd
  rw [hlen, ← hodd]
  exact binDec_odd (A+L+1) (firstQ4P1Value L A)
    (firstQ4P1Value_lt L A hA)

/-- The root checkpoint left side is already in the P1 side normal form. -/
theorem firstQ4P1Left_eq_reindexed
    (L A : Nat) (hA : 0 < A) :
    firstQ4P1Left L A =
      [false,true,true] ++ d0 ++
        binDec (A+L+1) (firstQ4P1Value L A) ++ lh := by
  simp [firstQ4P1Left, firstQ4P1BinDec_reparam L A hA,
    List.append_assoc]

#print axioms firstQ4P1M_eq_rootM
#print axioms firstQ4P1Value_lt
#print axioms firstQ4P1Value_odd
#print axioms firstQ4P1Value_odd_root
#print axioms firstQ4P1BinDec_reparam
#print axioms firstQ4P1Left_eq_reindexed

end BB6Coverage.Agent42FirstQ4P1Arithmetic
