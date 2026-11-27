import ATCarriedParser
import ATCostGrowth

set_option maxRecDepth 100000
set_option maxHeartbeats 500000

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

/-- The 36-step transport is uniform in the current counter depth. -/
theorem atPConsume_step (n : Nat) (l : Tape) (hl : l 0 = true) :
    run 36
      (other B
        (pre [true,false,true,false,true,true,false,false] l)
        (atpRight (atQ n))) =
    some (other B l (atpRight (atQ (n+1)))) := by
  cases n with
  | zero =>
      change run 36
        (other B (pre [true,false,true,false,true,true,false,false] l)
          (pre [false,false,true] blank)) =
        some (other B l
          (pre [false,false,true,true,true,true,false,false,false,
            true,true] blank))
      exact atc_consume_e l hl
  | succ k =>
      have hS : (atSStack k) 0 = true := atSStack_first k
      change run 36
        (other B
          (pre [true,false,true,false,true,true,false,false] l)
          (pre [false,false,true,true,true,true,false,false,false]
            (atSStack k))) =
        some (other B l
          (pre [false,false,true,true,true,true,false,false,false,
            true,true,true,true,true,false,false,false] (atSStack k)))
      exact atc_consume_u l (atSStack k) hl hS

#print axioms atPConsume_step

end F197
