import ATCarriedParser
import ATCostGrowth

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace F197
open Q

/- Two-independent-parameter complement to atp_family: an arbitrary
   leading P^n= (AAT)^n marker is consumed to the right, the TAT carry
   transducer processes an arbitrary paired data list, and a finite
   right-counter decoder restores P^n at the left.
   These statements all use the original six-state primitive `run`. -/

/-- Right terminal stack d=11 preceded by n copies of s=(5,3). -/
def atSStack : Nat → Tape
  | 0 => pre [true,true] blank
  | n+1 =>
      pre [true,true,true,true,true,false,false,false] (atSStack n)

/-- P-counter on the right: Q^0=e, Q^(n+1)=u s^n d. -/
def atQ : Nat → Tape
  | 0 => pre [true] blank
  | n+1 =>
      pre [true,true,true,true,false,false,false] (atSStack n)

/-- Exactly n copies of P=AAT on the left tape. -/
def atPreP : Nat → Tape → Tape
  | 0, l => l
  | n+1, l =>
      pre [true,false,true,false,true,true,false,false] (atPreP n l)

theorem atSStack_first (n : Nat) : (atSStack n) 0 = true := by
  cases n <;> rfl

theorem atQ_first (n : Nat) : (atQ n) 0 = true := by
  cases n <;> rfl

theorem atPreP_shift (n : Nat) (l : Tape) :
    atPreP (n+1) l =
      atPreP n (pre [true,false,true,false,true,true,false,false] l) := by
  induction n with
  | zero => rfl
  | succ n ih =>
      change pre [true,false,true,false,true,true,false,false]
          (atPreP (n+1) l) =
        pre [true,false,true,false,true,true,false,false]
          (atPreP n (pre [true,false,true,false,true,true,false,false] l))
      rw [ih]

/-- The standard P-counter consumes exactly 36 primitive steps per P,
    for arbitrarily large n and any run-aligned remaining left tape. -/
theorem atPConsume (n : Nat) (l : Tape) (hl : l 0 = true) :
    run (36*n)
      (other B (atPreP n l) (atpRight (atQ 0))) =
    some (other B l (atpRight (atQ n))) := by
  induction n generalizing l with
  | zero => rfl
  | succ n ih =>
      have htime : 36*(n+1) = 36*n + 36 := by omega
      rw [htime, atPreP_shift n l, run_add]
      rw [ih (l := pre [true,false,true,false,true,true,false,false] l) (by rfl)]
      simp only [Option.bind_some]
      cases n with
      | zero =>
          simpa [atQ,atpRight,pre] using atc_consume_e l hl
      | succ k =>
          have hS : (atSStack k) 0 = true := atSStack_first k
          simpa [atQ,atSStack,atpRight,pre] using
            atc_consume_u l (atSStack k) hl hS

#print axioms atPConsume

end F197
