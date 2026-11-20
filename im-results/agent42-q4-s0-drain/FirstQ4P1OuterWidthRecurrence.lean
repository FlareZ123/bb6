import FirstQ4P1Arithmetic
import Lean.Elab.Tactic.Omega

/-!
# Exact two-digit reduction of the outer BinDec counter

The positive-z q4 cycle handoff uses two consecutive zero-digit blocks
from the outer `binDec` word.  This file isolates the arithmetic fact
behind that consumption:

  q_A = 2^(A-1) * (2^(L+2)-1) - 1
      = 4*q_(A-2) + 3.

Consequently, whenever A>=3, the head-facing source word begins
`d0 ++ d0`, and deleting those two blocks leaves exactly the same
parameter family with A replaced by A-2 and width reduced by two.

This is an arithmetic/source-encoding lemma only.  It does not assert
that the TM2 trajectory performs the deletion; that requires the
q4Tail-to-S0 identity and the alternating prefix/postlude theorems.
-/ 

namespace BB6Coverage.Agent42FirstQ4P1Reduction

open BB6Coverage.Agent8S1Encoder
open BB6Coverage.Agent42FirstQ4P1Arithmetic

/-- One full pair of zero-digit blocks is the exact outer-value update. -/
theorem firstQ4P1Value_twoBit_step (L A : Nat) (hA : 3 ≤ A) :
    firstQ4P1Value L A =
      4 * firstQ4P1Value L (A-2) + 3 := by
  have hAeq : A-1 = (A-3)+2 := by omega
  have hAeq' : (A-2)-1 = A-3 := by omega
  have hpow : 2^(A-1) = 4*2^(A-3) := by
    calc
      2^(A-1) = 2^((A-3)+2) := by rw [hAeq]
      _ = 2^(A-3)*2^2 := by rw [Nat.pow_add]
      _ = 2^(A-3)*4 := by rw [show (2:Nat)^2 = 4 by decide]
      _ = 4*2^(A-3) := Nat.mul_comm _ _
  have hmul :
      2^(A-1)*(2^(L+2)-1) =
        4*(2^(A-3)*(2^(L+2)-1)) := by
    rw [hpow]
    ac_rfl
  have hpow4 : 4 ≤ 2^(L+2) := by
    have h := Nat.pow_le_pow_right (by decide : 0 < 2)
      (show 2 ≤ L+2 by omega)
    have hfour : (2:Nat)^2 = 4 := by decide
    rw [hfour] at h
    exact h
  have hC : 0 < 2^(L+2)-1 := by omega
  have hX : 0 < 2^(A-3)*(2^(L+2)-1) :=
    Nat.mul_pos (Nat.pow_pos (by decide)) hC
  unfold firstQ4P1Value
  rw [hAeq', hmul]
  change 4*(2^(A-3)*(2^(L+2)-1))-1 =
    4*(2^(A-3)*(2^(L+2)-1)-1)+3
  omega

/-- For A>=3, the outer BinDec word begins with exactly two d0 blocks.
The remaining word is the same encoding with A decreased by two. -/
theorem firstQ4P1BinDec_twoD0 (L A : Nat) (hA : 3 ≤ A) :
    binDec (firstQ4P1Width L A) (firstQ4P1Value L A) =
      d0 ++ d0 ++
        binDec (firstQ4P1Width L (A-2))
          (firstQ4P1Value L (A-2)) := by
  let w := firstQ4P1Width L (A-2)
  let q := firstQ4P1Value L (A-2)
  have hApos : 0 < A-2 := by omega
  have hwidth : firstQ4P1Width L A = w+2 := by
    dsimp [w,firstQ4P1Width]
    omega
  have hqbound : q < 2^w := by
    dsimp [w,q]
    exact firstQ4P1Value_lt L (A-2) hApos
  have hstep := firstQ4P1Value_twoBit_step L A hA
  have hqrepr : firstQ4P1Value L A = 2*(2*q+1)+1 := by
    dsimp [q] at hstep ⊢
    omega
  have hmidbound : 2*q+1 < 2^(w+1) := by
    rw [Nat.pow_succ]
    omega
  have hbin1 :
      binDec (w+2) (2*(2*q+1)+1) =
        d0 ++ binDec (w+1) (2*q+1) := by
    have h := binDec_odd (w+1) (2*q+1) hmidbound
    simpa [show w+2=(w+1)+1 by omega] using h
  have hbin2 :
      binDec (w+1) (2*q+1) = d0 ++ binDec w q :=
    binDec_odd w q hqbound
  calc
    binDec (firstQ4P1Width L A) (firstQ4P1Value L A)
        = binDec (w+2) (2*(2*q+1)+1) := by
            rw [hwidth,hqrepr]
    _ = d0 ++ binDec (w+1) (2*q+1) := hbin1
    _ = d0 ++ d0 ++ binDec w q := by
          rw [hbin2]
          simp [List.append_assoc]

/-- The repeated zero-digit encoding is additive in its block count. -/
private theorem d0pow_add (m n : Nat) :
    d0pow (m+n) = d0pow m ++ d0pow n := by
  induction m with
  | zero => simp [d0pow]
  | succ m ih =>
      simp [Nat.succ_add,d0pow,ih,List.append_assoc]

/-- Two more zero-digit blocks extend the existing d0-power prefix. -/
private theorem d0pow_two_add (k : Nat) :
    d0pow (2*(k+1)) = d0 ++ d0 ++ d0pow (2*k) := by
  have harg : 2*(k+1) = 2+(2*k) := by omega
  rw [harg,d0pow_add]
  simp [d0pow,List.append_assoc]

/-- After k complete two-block reductions, exactly 2k d0 blocks have
been exposed and the residual BinDec width parameter is A-2k. -/
theorem firstQ4P1BinDec_iterated (L A k : Nat) (hk : 2*k+1 ≤ A) :
    binDec (firstQ4P1Width L A) (firstQ4P1Value L A) =
      d0pow (2*k) ++
        binDec (firstQ4P1Width L (A-2*k))
          (firstQ4P1Value L (A-2*k)) := by
  induction k generalizing A with
  | zero =>
      simp [d0pow]
  | succ k ih =>
      have hA3 : 3 ≤ A := by omega
      have hrec : 2*k+1 ≤ A-2 := by omega
      rw [firstQ4P1BinDec_twoD0 L A hA3]
      rw [ih (A-2) hrec]
      have hsub : A-2-2*k = A-2*(k+1) := by omega
      rw [d0pow_two_add k,hsub]
      simp [List.append_assoc]

/-- The outer value obeys the matching closed multiplicative recurrence:
each two-block reduction divides q+1 by four. -/
theorem firstQ4P1Value_iterated (L A k : Nat) (hk : 2*k+1 ≤ A) :
    firstQ4P1Value L A + 1 =
      4^k * (firstQ4P1Value L (A-2*k)+1) := by
  induction k generalizing A with
  | zero => simp
  | succ k ih =>
      have hA3 : 3 ≤ A := by omega
      have hrec : 2*k+1 ≤ A-2 := by omega
      have hstep := firstQ4P1Value_twoBit_step L A hA3
      have hplus :
          firstQ4P1Value L A + 1 =
            4*(firstQ4P1Value L (A-2)+1) := by
        rw [hstep]
        omega
      calc
        firstQ4P1Value L A + 1 =
            4*(firstQ4P1Value L (A-2)+1) := hplus
        _ = 4*(4^k*(firstQ4P1Value L (A-2-2*k)+1)) := by
              rw [ih (A-2) hrec]
        _ = 4^(k+1)*(firstQ4P1Value L (A-2*(k+1))+1) := by
              rw [Nat.pow_succ]
              have hsub : A-2-2*k = A-2*(k+1) := by omega
              rw [hsub]
              ac_rfl


/-- The initial P2 tail before the second-cycle frame: four fixed ones,
the outer BinDec word, then the fixed left-history suffix. -/
def firstQ4P1Tail0 (L A : Nat) : List Bool :=
  List.replicate 4 true ++
    (binDec (firstQ4P1Width L A) (firstQ4P1Value L A) ++ lh)

private theorem d0pow_length (n : Nat) :
    (d0pow n).length = 3*n := by
  induction n with
  | zero => simp [d0pow]
  | succ n ih =>
      simp [d0pow, ih, d0]
      omega

/-- Expose two further d0 blocks after the already-consumed 2k blocks. -/
private theorem d0pow_twoBlocks_right (k : Nat) :
    d0pow (2*(k+1)) = d0pow (2*k) ++ d0 ++ d0 := by
  have harg : 2*(k+1) = 2*k+2 := by omega
  rw [harg, d0pow_add]
  simp [d0pow, List.append_assoc]

/-- At every later P2 boundary, the next tail begins with the required
100 guard, followed by the final 1 of the second d0 block and the residual
outer counter with A reduced by two more. The offset 6+6k consists of the
four fixed setup ones and 2k complete d0 blocks. This is an encoder/list
identity, not a claim that the TM trajectory has performed those deletions. -/
theorem firstQ4P1Tail0_dropSixPlusSixK
    (L A k : Nat) (hk : 2*k+3 ≤ A) :
    (firstQ4P1Tail0 L A).drop (6+6*k) =
      [true,false,false,true] ++
        binDec (firstQ4P1Width L (A-2*(k+1)))
          (firstQ4P1Value L (A-2*(k+1))) ++ lh := by
  have hiter := firstQ4P1BinDec_iterated L A (k+1) (by omega)
  rw [firstQ4P1Tail0, hiter, d0pow_twoBlocks_right]
  simp only [List.append_assoc]
  let r := binDec (firstQ4P1Width L (A-2*(k+1)))
    (firstQ4P1Value L (A-2*(k+1)))
  change (List.replicate 4 true ++
    (d0pow (2*k) ++ (d0 ++ (d0 ++ (r ++ lh))))).drop (6+6*k) =
      [true,false,false,true] ++ r ++ lh
  have hlarge : 4 ≤ 6+6*k := by omega
  have hdropRep : (List.replicate 4 true).drop (6+6*k) = [] := by
    simp [hlarge]
  have hrepLen : (List.replicate 4 true).length = 4 := by simp
  have hidx1 : 6+6*k-4 = 2+6*k := by omega
  rw [List.drop_append]
  simp only [List.length_replicate, hdropRep, hidx1, List.nil_append]
  have hpowLen : (d0pow (2*k)).length = 6*k := by
    rw [d0pow_length]
    omega
  have hdropPow : (d0pow (2*k)).drop (2+6*k) = [] := by
    simp [hpowLen]
  have hidx2 : 2+6*k-6*k = 2 := by omega
  rw [List.drop_append]
  simp only [hpowLen, hdropPow, hidx2, List.nil_append]
  rw [List.drop_append]
  simp [d0, r]


/-- At the terminal outer widths, the residual BinDec word has only one
nonzero digit block. This is the exact arithmetic boundary left after the
two-d0-block descent; it is not a TM terminal-run theorem. -/
private theorem binDec_allZeroBits (len : Nat) :
    binDec len (2^len-1) = d0pow len := by
  induction len with
  | zero => simp [binDec,d0pow,binaryCounterFuel]
  | succ len ih =>
      have hpow : 2^(len+1) = 2*2^len := by
        rw [Nat.pow_succ]
        ac_rfl
      have hvalue : 2^(len+1)-1 = 2*(2^len-1)+1 := by
        rw [hpow]
        have hp0 : 0 < 2^len := Nat.pow_pos (by decide)
        have hp : 1 ≤ 2^len := by omega
        omega
      have hbound : 2^len-1 < 2^len := by
        have hp : 0 < 2^len := Nat.pow_pos (by decide)
        omega
      rw [hvalue, binDec_odd len (2^len-1) hbound, ih]
      simp [d0pow]

/-- When A=1, the residual outer counter is one d1 block followed by
L+1 zero-digit blocks. -/
theorem firstQ4P1BinDec_A1 (L : Nat) :
    binDec (firstQ4P1Width L 1) (firstQ4P1Value L 1) =
      d1 ++ d0pow (L+1) := by
  have hwidth : firstQ4P1Width L 1 = (L+1)+1 := by
    dsimp [firstQ4P1Width]
    omega
  have hpow : 2^(L+2) = 2*2^(L+1) := by
    rw [Nat.pow_succ]
    ac_rfl
  have hvalue : firstQ4P1Value L 1 = 2*(2^(L+1)-1) := by
    simp [firstQ4P1Value]
    rw [hpow]
    have hp0 : 0 < 2^(L+1) := Nat.pow_pos (by decide)
    have hp : 1 ≤ 2^(L+1) := by omega
    omega
  have hbound : 2^(L+1)-1 < 2^(L+1) := by
    have hp : 0 < 2^(L+1) := Nat.pow_pos (by decide)
    omega
  rw [hwidth,hvalue,binDec_even (L+1) (2^(L+1)-1) hbound]
  rw [binDec_allZeroBits]

/-- When A=2, the residual outer counter is d0, then d1, then L+1
zero-digit blocks. -/
theorem firstQ4P1BinDec_A2 (L : Nat) :
    binDec (firstQ4P1Width L 2) (firstQ4P1Value L 2) =
      d0 ++ d1 ++ d0pow (L+1) := by
  have hwidth : firstQ4P1Width L 2 = (L+2)+1 := by
    dsimp [firstQ4P1Width]
    omega
  have hvalue : firstQ4P1Value L 2 = 2*(2^(L+2)-2)+1 := by
    simp [firstQ4P1Value]
    have hpowle := Nat.pow_le_pow_right (by decide : 0<2)
      (show 2 ≤ L+2 by omega)
    have hfour : (2:Nat)^2 = 4 := by decide
    rw [hfour] at hpowle
    have hp : 2 ≤ 2^(L+2) := by omega
    omega
  have hbound : 2^(L+2)-2 < 2^(L+2) := by
    have hp : 2 ≤ 2^(L+2) := by
      have hpowle := Nat.pow_le_pow_right (by decide : 0<2)
        (show 2 ≤ L+2 by omega)
      have hfour : (2:Nat)^2 = 4 := by decide
      rw [hfour] at hpowle
      omega
    omega
  rw [hwidth,hvalue,binDec_odd (L+2) (2^(L+2)-2) hbound]
  have hw : firstQ4P1Width L 1 = L+2 := by
    simp [firstQ4P1Width]
    omega
  have hv : firstQ4P1Value L 1 = 2^(L+2)-2 := by
    simp [firstQ4P1Value]
    omega
  have hA1 : binDec (L+2) (2^(L+2)-2) =
      d1 ++ d0pow (L+1) := by
    rw [← hv, ← hw]
    exact firstQ4P1BinDec_A1 L
  rw [hA1]
  simp [List.append_assoc]


/-- The terminal marker-1 q4 family uses M(A,L)=2^A*(2^(L+2)-1)
and width A+L+2. -/
def firstQ4P1TerminalM (A L : Nat) : Nat :=
  2^A * (2^(L+2)-1)

def firstQ4P1TerminalWidth (A L : Nat) : Nat :=
  A+L+2

/-- Reindexing the outer counter A as terminal parameter A-1 preserves
the encoded width. -/
theorem firstQ4P1Width_terminal (L A : Nat) (hA : 0 < A) :
    firstQ4P1Width L A = firstQ4P1TerminalWidth (A-1) L := by
  unfold firstQ4P1Width firstQ4P1TerminalWidth
  omega

/-- The outer value q(L,A) is exactly M(A-1,L)-1, the j=1
left-counter value in the terminal q4 checkpoint family. -/
theorem firstQ4P1Value_terminal (L A : Nat) :
    firstQ4P1Value L A = firstQ4P1TerminalM (A-1) L - 1 := by
  rfl

/-- The outer BinDec word is exactly the inner left counter of the
terminal q4 checkpoint at j=1, after reindexing A to A-1. -/
theorem firstQ4P1BinDec_terminalCheckpointLeft
    (L A : Nat) (hA : 0 < A) :
    binDec (firstQ4P1Width L A) (firstQ4P1Value L A) =
      binDec (firstQ4P1TerminalWidth (A-1) L)
        (firstQ4P1TerminalM (A-1) L - 1) := by
  rw [firstQ4P1Width_terminal L A hA,
    firstQ4P1Value_terminal L A]

#print axioms firstQ4P1Value_twoBit_step
#print axioms firstQ4P1BinDec_twoD0
#print axioms firstQ4P1BinDec_iterated
#print axioms firstQ4P1Value_iterated

end BB6Coverage.Agent42FirstQ4P1Reduction
