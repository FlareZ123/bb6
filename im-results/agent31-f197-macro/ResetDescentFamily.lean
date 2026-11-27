import ResetTransport
import ResetDescentCore

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace F197
open Q

def ppre (t : Tape) : Tape :=
  pre [true, false, true, false, true, true, false, false] t
def spre (t : Tape) : Tape :=
  pre [true, true, true, true, true, false, false, false] t
def jpre (t : Tape) : Tape := pre [true, false, false] t
def uRight (t : Tape) : Tape :=
  pre [false, false, true, true, true, true, false, false, false] t
def xRight (t : Tape) : Tape :=
  pre [false, false, true, false] t
def dTail : Tape := pre [true, true] blank
def eRight : Tape := pre [false, false, true] blank

def pPow : Nat → Tape → Tape
  | 0, t => t
  | n+1, t => ppre (pPow n t)

def sPow : Nat → Tape → Tape
  | 0, t => t
  | n+1, t => spre (sPow n t)

def consumeCost : Nat → Nat
  | 0 => 0
  | n+1 => 36 + consumeCost n

def decoderCost : Nat → Nat
  | 0 => 27
  | n+1 => 32 + decoderCost n

theorem pPow_ppre (n : Nat) (t : Tape) :
    pPow n (ppre t) = ppre (pPow n t) := by
  induction n with
  | zero => rfl
  | succ n ih =>
      simp only [pPow]
      rw [ih]

theorem sPow_spre (n : Nat) (t : Tape) :
    sPow n (spre t) = spre (sPow n t) := by
  induction n with
  | zero => rfl
  | succ n ih =>
      simp only [sPow]
      rw [ih]

/-- Consume n additional P blocks after the first one has created u·... . -/
theorem consume_us_iter (n : Nat) (l r : Tape) :
    run (consumeCost n) (other B (pPow n l) (uRight r)) =
      some (other B l (uRight (sPow n r))) := by
  induction n generalizing l r with
  | zero => rfl
  | succ n ih =>
      change run (36 + consumeCost n)
        (other B (ppre (pPow n l)) (uRight r)) =
        some (other B l (uRight (spre (sPow n r))))
      rw [run_add]
      change (run 36
        (other B (ppre (pPow n l)) (uRight r))).bind (run (consumeCost n)) =
        some (other B l (uRight (spre (sPow n r))))
      rw [show run 36 (other B (ppre (pPow n l)) (uRight r)) =
          some (other B (pPow n l) (uRight (spre r))) by
            simpa [ppre, uRight, spre] using reset_P_consume_us (pPow n l) r]
      simp only [Option.bind_some]
      rw [ih (l := l) (r := spre r), sPow_spre]

/-- Starting from reset right e, n+1 P blocks become u·s^n·d. -/
theorem consume_e_succ (n : Nat) (l : Tape) :
    run (36 + consumeCost n) (other B (pPow (n+1) l) eRight) =
      some (other B l (uRight (sPow n dTail))) := by
  change run (36 + consumeCost n)
    (other B (ppre (pPow n l)) eRight) =
    some (other B l (uRight (sPow n dTail)))
  rw [run_add]
  change (run 36 (other B (ppre (pPow n l)) eRight)).bind
      (run (consumeCost n)) =
    some (other B l (uRight (sPow n dTail)))
  rw [show run 36 (other B (ppre (pPow n l)) eRight) =
      some (other B (pPow n l) (uRight dTail)) by
        simpa [ppre, eRight, uRight, dTail] using reset_P_consume_e (pPow n l)]
  simp only [Option.bind_some]
  exact consume_us_iter n l dTail

/-- Decode x·s^k·d by moving k+1 copies of P onto the left. -/
theorem decoder_iter (k : Nat) (l : Tape) :
    run (decoderCost k) (other B (jpre l) (xRight (sPow k dTail))) =
      some (other B (pPow (k+1) l) eRight) := by
  induction k generalizing l with
  | zero =>
      simpa [decoderCost, sPow, pPow, jpre, xRight, dTail, eRight, ppre]
        using reset_decoder_d l
  | succ k ih =>
      change run (32 + decoderCost k)
        (other B (jpre l) (xRight (spre (sPow k dTail)))) =
        some (other B (ppre (pPow (k+1) l)) eRight)
      rw [run_add]
      change (run 32
        (other B (jpre l) (xRight (spre (sPow k dTail))))).bind
        (run (decoderCost k)) =
        some (other B (ppre (pPow (k+1) l)) eRight)
      rw [show run 32
          (other B (jpre l) (xRight (spre (sPow k dTail)))) =
          some (other B (jpre (ppre l)) (xRight (sPow k dTail))) by
            simpa [jpre, ppre, xRight, spre] using
              reset_decoder_s l (sPow k dTail)]
      simp only [Option.bind_some]
      rw [ih (l := ppre l), pPow_ppre]

def mta (l : Tape) : Tape :=
  pre [true, false, false, true, true, false, false, true, false,
       true, false, true, true, false, false, true, false, true,
       false, true, false, true, true, false, false, true, false] l

def mkta (l : Tape) : Tape :=
  pre [true, false, false, true, true, false, false, true, false,
       true, false, true, true, false, false, true, false, true,
       false, true, false, true, true, false, false, true, false,
       true, true, false, false, true, false, true, false, true,
       true, false, false, true, true, false, false, true, false] l

/-- Exact n=2 endpoint of the new descent family. -/
theorem reset_descent_two (l : Tape) :
    run 388 (other B (pPow 2 (mta l)) eRight) =
      some (other B (mkta l) eRight) := by
  rw [show 388 = 72 + 316 by rfl, run_add]
  rw [show run 72 (other B (pPow 2 (mta l)) eRight) =
      some (other B (mta l) (uRight (sPow 1 dTail))) by
        simpa [consumeCost] using consume_e_succ 1 (mta l)]
  simp only [Option.bind_some]
  simpa [mta, mkta, uRight, sPow, spre, dTail, eRight] using
    reset_descent_n2_middle_316 l

/-- Exact n=3 endpoint of the new descent family. -/
theorem reset_descent_three (l : Tape) :
    run 456 (other B (pPow 3 (mta l)) eRight) =
      some (other B (pPow 1 (mkta l)) eRight) := by
  rw [show 456 = 108 + (321 + 27) by rfl, run_add]
  rw [show run 108 (other B (pPow 3 (mta l)) eRight) =
      some (other B (mta l) (uRight (sPow 2 dTail))) by
        simpa [consumeCost] using consume_e_succ 2 (mta l)]
  simp only [Option.bind_some]
  rw [run_add]
  rw [show run 321 (other B (mta l) (uRight (sPow 2 dTail))) =
      some (other B (jpre (mkta l)) (xRight dTail)) by
        simpa [mta, mkta, uRight, sPow, spre, dTail, jpre, xRight] using
          reset_descent_middle_d_321 l]
  simp only [Option.bind_some]
  simpa [decoderCost, sPow, pPow] using decoder_iter 0 (mkta l)

/-- For every k, this is n=k+4:
    P^(k+4) M T A  ->  P^(k+2) M K T A,
    with exact primitive cost recorded compositionally. -/
theorem reset_descent_ge_four (k : Nat) (l : Tape) :
    run ((36 + consumeCost (k+3)) + (321 + decoderCost (k+1)))
      (other B (pPow (k+4) (mta l)) eRight) =
      some (other B (pPow (k+2) (mkta l)) eRight) := by
  rw [run_add]
  rw [show run (36 + consumeCost (k+3))
        (other B (pPow (k+4) (mta l)) eRight) =
      some (other B (mta l) (uRight (sPow (k+3) dTail))) by
        simpa using consume_e_succ (k+3) (mta l)]
  simp only [Option.bind_some]
  rw [run_add]
  rw [show run 321 (other B (mta l) (uRight (sPow (k+3) dTail))) =
      some (other B (jpre (mkta l)) (xRight (sPow (k+1) dTail))) by
        simpa [mta, mkta, uRight, sPow, spre, jpre, xRight] using
          reset_descent_middle_s_321 l (sPow k dTail)]
  simp only [Option.bind_some]
  simpa using decoder_iter (k+1) (mkta l)

#print axioms consume_us_iter
#print axioms consume_e_succ
#print axioms decoder_iter
#print axioms reset_descent_two
#print axioms reset_descent_three
#print axioms reset_descent_ge_four

end F197
