import FirstQ4P1Arithmetic
import Lean.Elab.Tactic.Omega

/-!
# General arithmetic for the q4Tail-to-S1 terminal reparameterization

This module isolates the arbitrary-A BinDec identities behind the direct
complete-dispatcher route. It is a source draft until locally compiled.
-/

namespace BB6Coverage.Agent44GeneralQ4TailArithmetic

open BB6Coverage.Agent8S1Encoder
open BB6Coverage.Agent42FirstQ4P1Arithmetic

private theorem binDec_max (k : Nat) :
    binDec k (2^k-1) = d0pow k := by
  induction k with
  | zero =>
      simp [binDec,binaryCounterFuel,d0pow]
  | succ k ih =>
      have hp : 0 < 2^k := Nat.pow_pos (by decide)
      have hbound : 2^k-1 < 2^k := by omega
      have hpow : 2^(k+1) = 2^k*2 := by rw [Nat.pow_succ]
      have hnum : 2^(k+1)-1 = 2*(2^k-1)+1 := by omega
      rw [hnum,binDec_odd k (2^k-1) hbound]
      simp [d0pow,d0,ih]

/-- For every A>=1, the first-q4 P1 value has a uniform block expansion. -/
theorem firstQ4P1Value_binDec_shape (L A : Nat) (hA : 1≤A) :
    binDec (A+L+1) (firstQ4P1Value L A) =
      d0pow (A-1) ++ d1 ++ d0pow (L+1) := by
  induction A using Nat.strong_induction_on with
  | h A ih =>
      by_cases hA1 : A=1
      · subst A
        have hp : 0 < 2^(L+1) := Nat.pow_pos (by decide)
        have hbound : 2^(L+1)-1 < 2^(L+1) := by omega
        have hpow : 2^(L+2) = 2^(L+1)*2 := by
          rw [show L+2=(L+1)+1 by omega,Nat.pow_succ]
        have hnum : firstQ4P1Value L 1 = 2*(2^(L+1)-1) := by
          unfold firstQ4P1Value
          omega
        rw [show 1+L+1=(L+1)+1 by omega,hnum]
        rw [binDec_even (L+1) (2^(L+1)-1) hbound]
        rw [binDec_max (L+1)]
        simp [d0pow,d1,List.append_assoc]
      · have hA2 : 2≤A := by omega
        have hprev : 1≤A-1 := by omega
        have hprevlt : A-1<A := by omega
        have hpow : 2^(A-1)=2^(A-2)*2 := by
          rw [show A-1=(A-2)+1 by omega,Nat.pow_succ]
        have hnum :
            firstQ4P1Value L A =
              2*firstQ4P1Value L (A-1)+1 := by
          unfold firstQ4P1Value
          omega
        have hbound := firstQ4P1Value_lt L (A-1) hprev
        rw [show A+L+1=(A-1+L+1)+1 by omega,hnum]
        rw [binDec_odd (A-1+L+1) (firstQ4P1Value L (A-1))
          (by simpa [firstQ4P1Width] using hbound)]
        rw [ih (A-1) hprevlt hprev]
        rw [show A-1=(A-2)+1 by omega]
        simp [d0pow,List.append_assoc]

/-- The general terminal index N=M-3 has a closed BinDec block form. -/
theorem q4TerminalIndex_binDec_shape (L A : Nat) (hA : 2≤A) :
    binDec (A+L+2) (firstQ4P1M L A-3) =
      d0 ++ d1 ++ d0pow (A-2) ++ d1 ++ d0pow (L+1) := by
  let qprev : Nat := firstQ4P1Value L (A-1)
  have hprev : 1≤A-1 := by omega
  have hwidth : (A-1)+L+1=A+L := by omega
  have hqbound : qprev < 2^(A+L) := by
    have h := firstQ4P1Value_lt L (A-1) hprev
    simpa [qprev,firstQ4P1Width,hwidth] using h
  have h2qbound : 2*qprev < 2^(A+L+1) := by
    have h := Nat.mul_lt_mul_left 2 hqbound
    have hpow : 2*2^(A+L)=2^(A+L+1) := by
      calc
        2*2^(A+L) = 2^(A+L)*2 := Nat.mul_comm _ _
        _ = 2^(A+L+1) := by rw [Nat.pow_succ]
    omega
  have hpow : 2^A=4*2^(A-2) := by
    calc
      2^A = 2^((A-2)+2) := by congr 1 <;> omega
      _ = 2^(A-2)*2^2 := by rw [Nat.pow_add]
      _ = 4*2^(A-2) := by norm_num [Nat.mul_comm]
  have hterm :
      2^(A-2)*(2^(L+2)-1) =
        firstQ4P1Value L (A-1)+1 := by
    unfold firstQ4P1Value
    rw [show (A-1)-1=A-2 by omega]
    have hCpos : 0<2^(L+2)-1 := by
      have hp : 0<2^(L+2) := Nat.pow_pos (by decide)
      omega
    have hprodpos :
        0<2^(A-2)*(2^(L+2)-1) :=
      Nat.mul_pos (Nat.pow_pos (by decide)) hCpos
    omega
  have hM :
      firstQ4P1M L A =
        4*(firstQ4P1Value L (A-1)+1) := by
    unfold firstQ4P1M
    rw [hpow]
    calc
      (4*2^(A-2))*(2^(L+2)-1)
          = 4*(2^(A-2)*(2^(L+2)-1)) := by rw [Nat.mul_assoc]
      _ = 4*(firstQ4P1Value L (A-1)+1) := by rw [hterm]
  have hN : firstQ4P1M L A-3 = 2*(2*qprev)+1 := by
    rw [hM]
    dsimp [qprev]
    omega
  calc
    binDec (A+L+2) (firstQ4P1M L A-3)
        = binDec ((A+L+1)+1) (2*(2*qprev)+1) := by
            rw [show A+L+2=(A+L+1)+1 by omega,hN]
    _ = d0 ++ binDec (A+L+1) (2*qprev) :=
          binDec_odd (A+L+1) (2*qprev) h2qbound
    _ = d0 ++ d1 ++ binDec (A+L) qprev := by
          rw [show A+L+1=(A+L)+1 by omega]
          rw [binDec_even (A+L) qprev hqbound]
    _ = d0 ++ d1 ++ d0pow (A-2) ++ d1 ++ d0pow (L+1) := by
          have hshape :=
            firstQ4P1Value_binDec_shape L (A-1) hprev
          have hexp : (A-1)-1=A-2 := by omega
          have hshape' :
              binDec (A+L) (firstQ4P1Value L (A-1)) =
                d0pow (A-2) ++ d1 ++ d0pow (L+1) := by
            rw [← hwidth,← hexp]
            exact hshape
          simpa [qprev] using
            congrArg (fun xs => d0 ++ d1 ++ xs) hshape'

private theorem pow_two_even_mod_three (k : Nat) :
    (2^(2*k)) % 3 = 1 := by
  induction k with
  | zero => norm_num
  | succ k ih =>
      calc
        (2^(2*(k+1))) % 3 = (2^(2*k+2)) % 3 := by
          congr 1 <;> omega
        _ = (2^(2*k) * 2^2) % 3 := by
          rw [Nat.pow_add]
        _ = ((2^(2*k) % 3) * (2^2 % 3)) % 3 := by
          rw [Nat.mul_mod]
        _ = 1 := by norm_num [ih]

private theorem pow_two_mod_three_of_even (n : Nat)
    (hn : n%2=0) : (2^n)%3=1 := by
  have hdiv : 2∣n := Nat.dvd_of_mod_eq_zero hn
  rcases hdiv with ⟨k,hk⟩
  simpa [hk] using pow_two_even_mod_three k

/-- N=M-3 is divisible by three whenever L is even. -/
theorem q4TerminalIndex_mod_three (L A : Nat)
    (hL : 4≤L) (hA : 2≤A) (hLeven : L%2=0) :
    (firstQ4P1M L A-3)%3=0 := by
  have heven : (L+2)%2=0 := by omega
  have hpow := pow_two_mod_three_of_even (L+2) heven
  have hfactor : (2^(L+2)-1)%3=0 := by omega
  have hMmod : firstQ4P1M L A%3=0 := by
    unfold firstQ4P1M
    rw [Nat.mul_mod]
    simp [hfactor]
  have hpowA : 4≤2^A := by
    have h := Nat.pow_le_pow_right (by decide : 0<2) hA
    have hfour : (2:Nat)^2=4 := by decide
    simpa [hfour] using h
  have hpowL : 2≤2^(L+2) := by
    have h := Nat.pow_le_pow_right (by decide : 0<2)
      (show 1≤L+2 by omega)
    simpa using h
  have hC : 1≤2^(L+2)-1 := by omega
  have hmul := Nat.mul_le_mul hpowA hC
  have hMge : 3≤firstQ4P1M L A := by
    unfold firstQ4P1M
    norm_num at hmul
    exact le_trans (by decide) hmul
  omega

#print axioms firstQ4P1Value_binDec_shape
#print axioms q4TerminalIndex_binDec_shape
#print axioms q4TerminalIndex_mod_three

end BB6Coverage.Agent44GeneralQ4TailArithmetic
