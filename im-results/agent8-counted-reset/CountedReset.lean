import ChampionRootBridge
import S1Encoder
import CostRecurrence
import CountPattern
import Lean.Elab.Tactic.Omega

/-!
# Counted TM63 reset drain

This module isolates the repeated S0 decrement phase (BusyCoq Incs0)
from the Rst0/Rst1/Rst2 macros.  It does not assume that the single-step
Inc0 theorem has already been proved: the raw-run composition theorem
takes that theorem as an explicit premise.  The arithmetic identity
connecting the actual descending v2 sequence to CountPattern.carryPattern
is proved here, so the 2^b-1 drain cost is exact rather than a fitted sum.
-/

namespace BB6Coverage.Agent8CountedReset

open BB6Coverage
open BB6Coverage.Agent48Champion
open BB6Coverage.Agent8S1Encoder
open BB6ChampionArithmetic

/-- Exact cost expected for one source S0 decrement with right unary
counter c.  Agent 26's uniform local theorem gives this as 48+12k+12c,
where k is the trailing-zero count of the positive left counter. -/
def inc0Cost (z c : Nat) : Nat := 48 + 12*v2 z + 12*c

/-- Descending valuation word: v2(n), v2(n-1), ..., v2(1). -/
def descV2 : Nat → List Nat
  | 0 => []
  | n+1 => v2 (n+1) :: descV2 n

theorem v2_of_odd (n : Nat) (hmod : n % 2 ≠ 0) : v2 n = 0 := by
  rw [v2.eq_1]
  by_cases hsmall : n ≤ 1
  · simp [hsmall]
  · rw [dif_neg hsmall, if_neg hmod]

theorem v2_of_even (n : Nat) (hgt : 1 < n) (hmod : n % 2 = 0) :
    v2 n = 1 + v2 (n/2) := by
  rw [v2.eq_1]
  simp [Nat.not_le_of_gt hgt,hmod]

/-- The 2-adic valuation of a power of two is its exponent. -/
theorem v2_pow2 (b : Nat) : v2 (2^b) = b := by
  induction b with
  | zero => simp [v2]
  | succ b ih =>
      have hpow : 2^(b+1) = 2*2^b := by
        rw [Nat.pow_succ]
        ac_rfl
      have hbase : 0 < 2^b := Nat.pow_pos (by decide)
      have hgt : 1 < 2^(b+1) := by rw [hpow]; omega
      have hmod : 2^(b+1) % 2 = 0 := by rw [hpow]; omega
      have hdiv : 2^(b+1) / 2 = 2^b := by rw [hpow]; omega
      simp [v2,Nat.not_le_of_gt hgt,hmod,hdiv,ih]
      omega


/-- The odd part contributes no trailing zeros, so the valuation of
(2*q+1)*2^r is exactly r. This identifies the carry exponent in the S1
factorization with the cost parameter used by the uniform local theorem. -/
theorem v2_odd_factor (q r : Nat) :
    v2 ((2*q+1)*2^r) = r := by
  induction r with
  | zero =>
      have hodd : (2*q+1) % 2 ≠ 0 := by omega
      simpa using v2_of_odd (2*q+1) hodd
  | succ r ih =>
      have hpow : 2^(r+1) = 2*2^r := by
        rw [Nat.pow_succ]
        ac_rfl
      have hprod : (2*q+1)*2^(r+1) =
          2*((2*q+1)*2^r) := by
        rw [hpow]
        ac_rfl
      have hpos : 0 < (2*q+1)*2^r :=
        Nat.mul_pos (by omega) (Nat.pow_pos (by decide))
      have hgt : 1 < 2*((2*q+1)*2^r) := by omega
      have hmod : (2*((2*q+1)*2^r)) % 2 = 0 := by omega
      have hdiv : (2*((2*q+1)*2^r)) / 2 = (2*q+1)*2^r := by omega
      calc
        v2 ((2*q+1)*2^(r+1)) =
            v2 (2*((2*q+1)*2^r)) := by rw [hprod]
        _ = 1 + v2 ((2*((2*q+1)*2^r))/2) :=
            v2_of_even _ hgt hmod
        _ = 1 + v2 ((2*q+1)*2^r) := by rw [hdiv]
        _ = r+1 := by rw [ih]; omega

/-- Factorization witnesses expose the exact valuation used by Inc0. -/
theorem v2_of_odd_factorization (z q r : Nat)
    (hz : z = (2*q+1)*2^r) : v2 z = r := by
  rw [hz]
  exact v2_odd_factor q r

/-- Adding a nonzero number smaller than 2^b to 2^b does not change
its 2-adic valuation. This is the key dyadic shift identity behind the
palindromic carry pattern. -/
theorem v2_add_pow (b k : Nat) (hk0 : 0 < k) (hklt : k < 2^b) :
    v2 (2^b+k) = v2 k := by
  induction b generalizing k with
  | zero => omega
  | succ b ih =>
      have hpow : 2^(b+1) = 2*2^b := by
        rw [Nat.pow_succ]
        ac_rfl
      have hbase : 0 < 2^b := Nat.pow_pos (by decide)
      by_cases he : k % 2 = 0
      · let t := k/2
        have hkEq : k = 2*t := by dsimp [t]; omega
        have ht0 : 0 < t := by dsimp [t]; omega
        have htlt : t < 2^b := by
          rw [hpow] at hklt
          dsimp [t]
          omega
        have hsum : 2^(b+1)+k = 2*(2^b+t) := by
          rw [hpow,hkEq]
          omega
        have hgtSum : 1 < 2^(b+1)+k := by
          rw [hpow]
          omega
        have hmodSum : (2^(b+1)+k) % 2 = 0 := by
          rw [hsum]
          omega
        have hdivSum : (2^(b+1)+k) / 2 = 2^b+t := by
          rw [hsum]
          omega
        have hgtK : 1 < k := by omega
        calc
          v2 (2^(b+1)+k) =
              1 + v2 ((2^(b+1)+k)/2) :=
            v2_of_even _ hgtSum hmodSum
          _ = 1 + v2 (2^b+t) := by rw [hdivSum]
          _ = 1 + v2 t := by rw [ih t ht0 htlt]
          _ = v2 k := by
            rw [v2_of_even k hgtK he]
      · have hmodK : k % 2 < 2 := Nat.mod_lt k (by decide)
        have hoddK : k % 2 ≠ 0 := by omega
        have hmodPow : (2^(b+1)) % 2 = 0 := by
          rw [hpow]
          simp
        have hmodSum : (2^(b+1)+k) % 2 ≠ 0 := by
          rw [Nat.add_mod,hmodPow]
          simpa using hoddK
        rw [v2_of_odd _ hmodSum,v2_of_odd k hoddK]

/-- Exact decomposition of the descending valuation word after a dyadic
shift. -/
theorem descV2_shift (b n : Nat) (hn : n < 2^b) :
    descV2 (2^b+n) = descV2 n ++ [b] ++ descV2 (2^b-1) := by
  induction n with
  | zero =>
      have hpos : 0 < 2^b := Nat.pow_pos (by decide)
      have hsplit : 2^b = (2^b-1)+1 := by omega
      have h1 := congrArg descV2 hsplit
      have h2 := congrArg v2 hsplit
      have hstep : descV2 (2^b) = v2 (2^b) :: descV2 (2^b-1) := by
        calc
          descV2 (2^b) = descV2 ((2^b-1)+1) := h1
          _ = v2 ((2^b-1)+1) :: descV2 (2^b-1) := rfl
          _ = v2 (2^b) :: descV2 (2^b-1) := by rw [← h2]
      change descV2 (2^b) = [b] ++ descV2 (2^b-1)
      rw [hstep,v2_pow2]
      rfl
  | succ n ih =>
      have hn' : n < 2^b := by omega
      have harg : 2^b+n+1 = 2^b+(n+1) := by omega
      have hval : v2 (2^b+n+1) = v2 (n+1) := by
        rw [harg]
        exact v2_add_pow b (n+1) (by omega) (by omega)
      simp [descV2,hval,ih hn',List.append_assoc]

/-- The actual descending v2 values from 2^b-1 to 1 are exactly the
source carryPattern, not merely a list with the same length and sum. -/
theorem descV2_binary (b : Nat) :
    descV2 (2^b-1) = carryPattern b := by
  induction b with
  | zero =>
      simp [descV2,carryPattern]
  | succ b ih =>
      have hpow : 2^(b+1) = 2*2^b := by
        rw [Nat.pow_succ]
        ac_rfl
      have hlt : 2^b-1 < 2^b := by omega
      have hsplit : 2^(b+1)-1 = 2^b+(2^b-1) := by
        rw [hpow]
        omega
      have hs := descV2_shift b (2^b-1) hlt
      rw [← hsplit] at hs
      rw [hs,ih]
      rfl

/-- The exact cost of draining n positive counter units, starting with
right-counter value c. Each decrement increases c by one. -/
def drainCost : Nat → Nat → Nat
  | 0, _ => 0
  | n+1, c => inc0Cost (n+1) c + drainCost n (c+1)

theorem drainCost_eq_charge (n c : Nat) :
    drainCost n c = charge (descV2 n) c := by
  induction n generalizing c with
  | zero => rfl
  | succ n ih =>
      simp [drainCost,inc0Cost,descV2,charge,ih]

/-- For the all-ones binary counter, the exact decrement cost is the
already established geometric drainPattern. -/
theorem drainCost_binary (b : Nat) :
    drainCost (2^b-1) 0 = drainPattern b := by
  rw [drainCost_eq_charge,descV2_binary]
  rfl

/-- Closed form for the all-ones drain, obtained from the actual v2
sequence rather than an independent cost fit. -/
/-- Additive closed form; this is the natural equation for composing
the drain with the reset prefix without relying on truncated subtraction. -/
theorem drainCost_binary_additive (b : Nat) :
    drainCost (2^b-1) 0 + 12*b + 48 = 6*4^b + 42*2^b := by
  rw [drainCost_binary]
  exact drainPattern_closed b

/-- Equivalent subtractive closed form for the all-ones drain. -/
theorem drainCost_binary_closed (b : Nat) :
    drainCost (2^b-1) 0 = 6*4^b + 42*2^b - 12*b - 48 := by
  have h := drainCost_binary_additive b
  omega

/-- Composition law for the original primitive TM63 run semantics. -/
theorem run_add (m : Machine) (c : Config) (a b : Nat) :
    run m (a+b) c =
      (run m a c).bind (fun d => run m b d) := by
  induction b with
  | zero => simp [run]
  | succ b ih =>
      rw [Nat.add_succ,run,ih]
      cases h : run m a c with
      | none => simp
      | some d => simp [run]

/-- Counted Incs0 theorem in the original infinite-tape Config semantics.
The only machine-specific premise is the uniform one-step Inc0 count;
all repeated-run composition and endpoint arithmetic are proved here. -/
theorem countedIncs0 (l : List Bool) (len n b : Nat) (h : Int)
    (hn : n < 2^len)
    (hInc0 : ∀ z c, 0 < z → z < 2^len →
      run tm2 (inc0Cost z c) (s0Config l len z c h) =
        some (s0Config l len (z-1) (c+1) h)) :
    run tm2 (drainCost n b) (s0Config l len n b h) =
      some (s0Config l len 0 (b+n) h) := by
  induction n generalizing b with
  | zero =>
      simp [drainCost,run]
  | succ n ih =>
      have hfirst :
          run tm2 (inc0Cost (n+1) b) (s0Config l len (n+1) b h) =
            some (s0Config l len n (b+1) h) := by
        apply hInc0 (n+1) b
        · omega
        · omega
      have htail :
          run tm2 (drainCost n (b+1)) (s0Config l len n (b+1) h) =
            some (s0Config l len 0 (b+1+n) h) :=
        ih (b+1) (by omega)
      calc
        run tm2 (drainCost (n+1) b) (s0Config l len (n+1) b h) =
            (run tm2 (inc0Cost (n+1) b)
              (s0Config l len (n+1) b h)).bind
                (fun c => run tm2 (drainCost n (b+1)) c) := by
                  simp only [drainCost]
                  exact run_add tm2 (s0Config l len (n+1) b h)
                    (inc0Cost (n+1) b) (drainCost n (b+1))
        _ = run tm2 (drainCost n (b+1))
              (s0Config l len n (b+1) h) := by simp [hfirst]
        _ = some (s0Config l len 0 (b+1+n) h) := htail
        _ = some (s0Config l len 0 (b+(n+1)) h) := by
              simpa [show b+1+n = b+(n+1) by omega] using htail

/-- The second phase of Rst0/Rst1/Rst2: drain the all-ones counter
2^b-1 to zero and transfer its value to the right unary counter. -/
theorem countedIncs0_binary (l : List Bool) (len b : Nat) (h : Int)
    (hbound : 2^b-1 < 2^len)
    (hInc0 : ∀ z c, 0 < z → z < 2^len →
      run tm2 (inc0Cost z c) (s0Config l len z c h) =
        some (s0Config l len (z-1) (c+1) h)) :
    run tm2 (drainPattern b) (s0Config l len (2^b-1) 0 h) =
      some (s0Config l len 0 (2^b-1) h) := by
  have hrun := countedIncs0 l len (2^b-1) 0 h hbound hInc0
  rw [drainCost_binary b] at hrun
  simpa using hrun

/-- Candidate prefix cost for the first, non-drain part of one
Rst0/Rst1/Rst2 stage. -/
def resetPrefixCost (m n a b : Nat) : Nat :=
  48 + 12*(a+v2 n) + 15 + 4*m + 3*b

/-- The proposed all-parameter Rst0/Rst1/Rst2 cost is exactly the
candidate prefix plus the proved geometric all-ones drain. -/
theorem proposedIncrementCost_decomp (m n a b : Nat) :
    proposedIncrementCost m n a b =
      resetPrefixCost m n a b + drainCost (2^b-1) 0 := by
  have h := drainCost_binary_additive b
  unfold proposedIncrementCost resetPrefixCost
  omega

/-- Marker-dependent second-counter length in the source reset macros. -/
def resetDelta (m : Nat) : Nat :=
  if m % 3 = 0 then 1 else 2

/-- The source reset's all-ones drain fits in its expanded second-counter
length whenever the old length a is positive. -/
theorem resetDrainBound (a b m : Nat) (ha : 0 < a) :
    2^b-1 < 2^(a+b+resetDelta m) := by
  have hexp : b < a+b+resetDelta m := by
    unfold resetDelta
    split <;> omega
  have hpow : 2^b ≤ 2^(a+b+resetDelta m) :=
    Nat.pow_le_pow_right (by decide : 0 < 2) (Nat.le_of_lt hexp)
  have hpos : 0 < 2^b := Nat.pow_pos (by decide)
  omega

/-- If the counted prefix of a reset stage reaches its S0 all-ones
intermediate, the complete counted drain follows with the exact proposed
Rst0/Rst1/Rst2 cost. This isolates the remaining prefix proof cleanly. -/
theorem countedRst012_of_prefix
    (cfg : Config) (l : List Bool) (a b m n : Nat) (h : Int)
    (ha : 0 < a)
    (hprefix :
      run tm2 (resetPrefixCost m n a b) cfg =
        some (s0Config l (a+b+resetDelta m) (2^b-1) 0 h))
    (hInc0 : ∀ z c, 0 < z → z < 2^(a+b+resetDelta m) →
      run tm2 (inc0Cost z c)
        (s0Config l (a+b+resetDelta m) z c h) =
          some (s0Config l (a+b+resetDelta m) (z-1) (c+1) h)) :
    run tm2 (proposedIncrementCost m n a b) cfg =
      some (s0Config l (a+b+resetDelta m) 0 (2^b-1) h) := by
  have hbound := resetDrainBound a b m ha
  have htail := countedIncs0_binary l (a+b+resetDelta m) b h hbound hInc0
  have hdecomp := proposedIncrementCost_decomp m n a b
  rw [hdecomp,run_add,hprefix,drainCost_binary b]
  exact htail

#print axioms v2_odd_factor
#print axioms v2_of_odd_factorization
#print axioms v2_add_pow
#print axioms descV2_binary
#print axioms drainCost_binary_closed
#print axioms run_add
#print axioms countedIncs0
#print axioms countedIncs0_binary
#print axioms proposedIncrementCost_decomp
#print axioms countedRst012_of_prefix

end BB6Coverage.Agent8CountedReset
