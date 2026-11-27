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

/-- Decoder of s^k d at right A, depositing k+1 copies of P. -/
theorem atPDecodeS (k : Nat) (l : Tape) (hl : l 0 = true) :
    run (32*k + 27)
      (other B (atpJ l) (atpXRight (atSStack k))) =
    some (other B (atPreP (k+1) l) (atpRight (atQ 0))) := by
  induction k generalizing l with
  | zero =>
      simpa [atSStack,atPreP,atQ,atpJ,atpXRight,atpRight,pre] using
        atc_counter_d l hl
  | succ k ih =>
      have htime : 32*(k+1) + 27 = 32 + (32*k + 27) := by omega
      rw [htime,run_add]
      rw [show run 32
        (other B (atpJ l) (atpXRight (atSStack (k+1)))) =
        some (other B
          (atpJ (pre [true,false,true,false,true,true,false,false] l))
          (atpXRight (atSStack k))) by
        simpa [atSStack,atpJ,atpXRight,pre] using
          atc_counter_s l (atSStack k) hl (atSStack_first k)]
      simp only [Option.bind_some]
      simpa [atPreP_shift] using
        ih (l := pre [true,false,true,false,true,true,false,false] l) (by rfl)

/-- Complete right carry: 31 + 32*n steps convert J/X, A C Q^n
    to P^n AAAT X at a terminal e-boundary. -/
theorem atCounterDecode (n : Nat) (l : Tape) (hl : l 0 = true) :
    run (31 + 32*n)
      (other B (atpJ l)
        (atpXRight (pre [true,true,false] (atQ n)))) =
    some
      (other B
        (atPreP n
          (pre [true,false,true,false,true,false,true,true,false,false] l))
        (atpRight (atQ 0))) := by
  cases n with
  | zero =>
      simpa [atQ,atPreP,atpJ,atpXRight,atpRight,pre] using
        atc_counter_base l hl
  | succ k =>
      have htime : 31 + 32*(k+1) = 36 + (32*k + 27) := by omega
      rw [htime,run_add]
      rw [show run 36
        (other B (atpJ l)
          (atpXRight (pre [true,true,false] (atQ (k+1))))) =
        some
          (other B
            (atpJ (pre
              [true,false,true,false,true,false,true,true,false,false] l))
            (atpXRight (atSStack k))) by
        simpa [atQ,atpJ,atpXRight,pre] using
          atc_counter_u l (atSStack k) hl (atSStack_first k)]
      simp only [Option.bind_some]
      exact atPDecodeS k
        (pre [true,false,true,false,true,false,true,true,false,false] l)
        (by rfl)

/-- Exact two-parameter reset family, not yet with the closed cost. -/
theorem atp_full_family (n : Nat) (data : List Bool) (l : Tape)
    (hne : data ≠ []) (hl : l 0 = true) :
    run (36*n +
      ((46 + (atpScanCost data + atpCarryCost data.reverse)) +
        (31 + 32*n)))
      (other B
        (atPreP n
          (pre [true,true,false,false,true,false,true,true,false,false]
            (atpSource data l)))
        (atpRight (atQ 0))) =
    some
      (other B
        (atPreP n
          (pre [true,false,true,false,true,false,true,true,false,false]
            (atpPhi data.reverse l)))
        (atpRight (atQ 0))) := by
  have ht : (pre
      [true,true,false,false,true,false,true,true,false,false]
      (atpSource data l)) 0 = true := by rfl
  have hd : data.reverse ≠ [] := by simpa using hne
  rw [run_add]
  rw [atPConsume n
    (pre [true,true,false,false,true,false,true,true,false,false]
      (atpSource data l)) ht]
  simp only [Option.bind_some]
  rw [run_add, atp_staged_with data l (atQ n) hne hl (atQ_first n)]
  simp only [Option.bind_some]
  exact atCounterDecode n (atpPhi data.reverse l)
    (atpPhi_first data.reverse l hd)

/-- The finite-data carry decoder is the old reset decoder less exactly
    31 terminal transitions, independent of data length and composition. -/
theorem atpCarryCost_relation (data : List Bool) (hne : data ≠ []) :
    atpCarryCost data + 31 = atpDecCost data := by
  induction data with
  | nil => exact (hne rfl).elim
  | cons c tail ih =>
      cases tail with
      | nil => cases c <;> decide
      | cons d ds =>
          have hh : d::ds ≠ [] := by simp
          have h := ih hh
          cases c <;> simp [atpCarryCost,atpDecCost] at * <;> omega

/-- Full closed cost: 156 + 68(n+q) + 14t for q+1 data symbols
    of which t are T.  The formulation uses length q+1. -/
theorem atpFullCost_formula (n : Nat) (data : List Bool)
    (hne : data ≠ []) :
    36*n +
      ((46 + (atpScanCost data + atpCarryCost data.reverse)) +
        (31 + 32*n)) =
      68*n + 88 + 68*data.length + 14*atCountT data := by
  have hd : data.reverse ≠ [] := by simpa using hne
  have hrel := atpCarryCost_relation data.reverse hd
  have htot := atpTotalCost_formula data hne
  omega

/-- Source-connected exact two-parameter F197 rewrite with primitive-step
    count independent of the suffix X and no intermediate halt. -/
theorem atp_full_family_closed (n : Nat) (data : List Bool) (l : Tape)
    (hne : data ≠ []) (hl : l 0 = true) :
    run (68*n + 88 + 68*data.length + 14*atCountT data)
      (other B
        (atPreP n
          (pre [true,true,false,false,true,false,true,true,false,false]
            (atpSource data l)))
        (atpRight (atQ 0))) =
    some
      (other B
        (atPreP n
          (pre [true,false,true,false,true,false,true,true,false,false]
            (atpPhi data.reverse l)))
        (atpRight (atQ 0))) := by
  rw [← atpFullCost_formula n data hne]
  exact atp_full_family n data l hne hl

#print axioms atPConsume
#print axioms atPDecodeS
#print axioms atCounterDecode
#print axioms atp_full_family
#print axioms atpFullCost_formula
#print axioms atp_full_family_closed

end F197
