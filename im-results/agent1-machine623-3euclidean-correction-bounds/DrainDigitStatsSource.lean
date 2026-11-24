import Agent49ParitySource
import Agent22ExactDrainCocycleSource
import Agent41DrainValuationNormalForm
import DrainDigitTransducerCarry
import Agent1SignedCoordinateNormalForm

/-!
# Source-exact bridge from the #623 B-drain to the three-state digit transducer.

The valuation recursion of the unchanged source drain is encoded as a sparse
ternary word.  The word is then identified with the output of the three-state
transducer, including its digit counts.  No transition definitions are copied.
-/

namespace BB6.Agent1DrainDigitStatsSource

open BusyBeaver.M_1RB0LE_0RC1RC_0RD1LA_1LD0LA_1LF1LC_HHH0LA
open BB6.Agent49ParitySource
open BB6.Agent22ExactDrainCocycleSource
open BB6.Agent41DrainValuationNormalForm
open BB6.Agent1SignedCoordinateNormalForm

/-- Split a low-order run of ternary ones, with enough fuel for every Nat input. -/
def splitLowOnesFuel : Nat → Nat → Nat × Nat
  | 0, _ => (0, 0)
  | fuel + 1, k =>
      if k % 3 = 1 then
        let p := splitLowOnesFuel fuel (k / 3)
        (p.1 + 1, p.2)
      else
        (0, k)

theorem splitLowOnesFuel_spec (fuel k : Nat) (hk : k < fuel) :
    k = ternaryOnes (splitLowOnesFuel fuel k).1
        + 3 ^ (splitLowOnesFuel fuel k).1 * (splitLowOnesFuel fuel k).2 ∧
    (splitLowOnesFuel fuel k).2 % 3 ≠ 1 := by
  induction fuel generalizing k with
  | zero =>
      omega
  | succ fuel ih =>
      by_cases h1 : k % 3 = 1
      · have hkpos : 0 < k := by omega
        have hdiv : k / 3 < k := by omega
        have hq : k / 3 < fuel := by omega
        let p := splitLowOnesFuel fuel (k / 3)
        have ht := ih (k / 3) hq
        have ht' :
            k / 3 = ternaryOnes p.1 + 3 ^ p.1 * p.2 ∧ p.2 % 3 ≠ 1 := by
          simpa [p] using ht
        rcases ht' with ⟨ht1, ht2⟩
        have hkmod : k = 1 + 3 * (k / 3) := by
          have h := Nat.mod_add_div k 3
          omega
        have hone : ternaryOnes (p.1 + 1) = 3 * ternaryOnes p.1 + 1 := rfl
        have hpow : 3 ^ (p.1 + 1) = 3 * 3 ^ p.1 := by
          simp [Nat.pow_succ]
        simp only [splitLowOnesFuel, if_pos h1]
        change k = ternaryOnes (p.1 + 1) + 3 ^ (p.1 + 1) * p.2 ∧
          p.2 % 3 ≠ 1
        constructor
        · calc
            k = 1 + 3 * (k / 3) := hkmod
            _ = 1 + 3 * (ternaryOnes p.1 + 3 ^ p.1 * p.2) := by rw [ht1]
            _ = ternaryOnes (p.1 + 1) + 3 ^ (p.1 + 1) * p.2 := by
              rw [hone, hpow]
              ring
        · exact ht2
      · simp [splitLowOnesFuel, h1, ternaryOnes]

def splitLowOnes (k : Nat) : Nat × Nat :=
  splitLowOnesFuel (k + 1) k

theorem splitLowOnes_spec (k : Nat) :
    k = ternaryOnes (splitLowOnes k).1
        + 3 ^ (splitLowOnes k).1 * (splitLowOnes k).2 ∧
    (splitLowOnes k).2 % 3 ≠ 1 := by
  unfold splitLowOnes
  exact splitLowOnesFuel_spec (k + 1) k (by omega)

structure DrainDigitStep where
  v : Nat
  eps : Nat
  q : Nat
  deriving Repr

def drainDigitStep (b : Nat) : DrainDigitStep :=
  let p := splitLowOnes b
  ⟨p.1, if p.2 % 3 = 2 then 1 else 0, p.2 / 3⟩

theorem drainDigitStep_spec (b : Nat) :
    (drainDigitStep b).eps ≤ 1 ∧
    b = ternaryOnes (drainDigitStep b).v
          + 3 ^ (drainDigitStep b).v *
              (3 * (drainDigitStep b).q + 2 * (drainDigitStep b).eps) ∧
    (drainDigitStep b).q ≤ b := by
  cases hsplit : splitLowOnes b with
  | mk v z =>
      have hsp := splitLowOnes_spec b
      rw [hsplit] at hsp
      rcases hsp with ⟨hdec, hnot⟩
      have hmod : z % 3 = 0 ∨ z % 3 = 2 := by
        have hlt := Nat.mod_lt z (by decide)
        omega
      have hpow : 1 ≤ 3 ^ v := by positivity
      have hmul : z ≤ 3 ^ v * z := by
        have h := Nat.mul_le_mul_right z hpow
        simpa using h
      have hzle : z ≤ b := by
        rw [hdec]
        omega
      have hqle : z / 3 ≤ b := le_trans (Nat.div_le_self _ _) hzle
      simp only [drainDigitStep, hsplit]
      change (if z % 3 = 2 then 1 else 0) ≤ 1 ∧
        b = ternaryOnes v + 3 ^ v * (3 * (z / 3) +
          2 * (if z % 3 = 2 then 1 else 0)) ∧ z / 3 ≤ b
      rcases hmod with h0 | h2
      · have hz : z = 3 * (z / 3) := by
          have h := Nat.mod_add_div z 3
          omega
        simp only [h0, if_false]
        constructor
        · decide
        constructor
        · calc
            b = ternaryOnes v + 3 ^ v * z := hdec
            _ = ternaryOnes v + 3 ^ v * (3 * (z / 3) + 2 * 0) := by rw [hz]; ring
        · exact hqle
      · have hz : z = 3 * (z / 3) + 2 := by
          have h := Nat.mod_add_div z 3
          omega
        simp only [h2, if_true]
        constructor
        · decide
        constructor
        · calc
            b = ternaryOnes v + 3 ^ v * z := hdec
            _ = ternaryOnes v + 3 ^ v * (3 * (z / 3) + 2 * 1) := by rw [hz]; ring
        · exact hqle

structure DrainDigitSummary where
  length : Nat
  ones : Nat
  twos : Nat
  value : Nat
  deriving Repr

def drainDigitSummary : Nat → DrainDigitSummary
  | 0 => ⟨0, 0, 0, 0⟩
  | b + 1 =>
      let s := drainDigitStep b
      let t := drainDigitSummary s.q
      ⟨s.v + 1 + t.length,
       (if s.eps = 0 then 1 else 0) + t.ones,
       s.eps + t.twos,
       (1 + s.eps) * 3 ^ s.v + 3 ^ (s.v + 1) * t.value⟩
termination_by b => b
decreasing_by
  simp_wf
  have hq := (drainDigitStep_spec b).2.2
  omega

theorem drainDigitSummary_succ (b : Nat) :
    drainDigitSummary (b + 1) =
      ⟨(drainDigitStep b).v + 1 + (drainDigitSummary (drainDigitStep b).q).length,
       (if (drainDigitStep b).eps = 0 then 1 else 0)
          + (drainDigitSummary (drainDigitStep b).q).ones,
       (drainDigitStep b).eps
          + (drainDigitSummary (drainDigitStep b).q).twos,
       (1 + (drainDigitStep b).eps) * 3 ^ (drainDigitStep b).v
          + 3 ^ ((drainDigitStep b).v + 1)
              * (drainDigitSummary (drainDigitStep b).q).value⟩ := by
  simp [drainDigitSummary]

theorem ternaryOnes_mono : ∀ m n : Nat, m ≤ n → ternaryOnes m ≤ ternaryOnes n := by
  intro m n h
  induction n generalizing m with
  | zero =>
      have hm : m = 0 := by omega
      subst m
      simp [ternaryOnes]
  | succ n ih =>
      by_cases hmn : m ≤ n
      · have hprev := ih hmn
        have hstep : ternaryOnes n ≤ ternaryOnes (n + 1) := by
          simp [ternaryOnes]
          omega
        exact le_trans hprev hstep
      · have hm : m = n + 1 := by omega
        subst m
        exact le_rfl

theorem ternaryOnes_parity (n : Nat) : ternaryOnes n % 2 = n % 2 := by
  induction n with
  | zero => simp [ternaryOnes]
  | succ n ih =>
      simp [ternaryOnes, Nat.add_mod, Nat.mul_mod, ih]

theorem drainDigitSummary_value_formula (b : Nat) :
    4 * (drainDigitSummary b).value + 1 =
      2 * b + 3 ^ (drainDigitSummary b).length := by
  induction b using Nat.strongRecOn with
  | ind b ih =>
      cases b with
      | zero =>
          simp [drainDigitSummary]
      | succ k =>
          let s := drainDigitStep k
          let t := drainDigitSummary s.q
          have hs := drainDigitStep_spec k
          have hlt : s.q < k + 1 := by
            have hq : s.q ≤ k := by simpa [s] using hs.2.2
            omega
          have ht := ih s.q hlt
          have hdecomp : k = ternaryOnes s.v + 3 ^ s.v * (3 * s.q + 2 * s.eps) := by
            simpa [s] using hs.2.1
          have hpow : 3 ^ (s.v + 1 + t.length) = 3 ^ s.v * 3 ^ (t.length + 1) := by
            rw [show s.v + 1 + t.length = s.v + (t.length + 1) by omega,
              Nat.pow_add]
          have hcoeff : 4 + 4 * s.eps + 12 * t.value =
              1 + 4 * s.eps + 6 * s.q + 3 ^ (t.length + 1) := by
            have ht3 := congrArg (fun x : Nat => 3 * x) ht
            have hpowt : 3 ^ (t.length + 1) = 3 * 3 ^ t.length := by
              simp [Nat.pow_succ]
            omega
          have htwice := twice_ones_add_one_eq_pow s.v
          have hleft :
              4 * ((1 + s.eps) * 3 ^ s.v + 3 ^ (s.v + 1) * t.value) + 1 =
                3 ^ s.v * (1 + 4 * s.eps + 6 * s.q + 3 ^ (t.length + 1)) + 1 := by
            rw [Nat.pow_succ]
            calc
              4 * ((1 + s.eps) * 3 ^ s.v + (3 ^ s.v * 3) * t.value) + 1 =
                  3 ^ s.v * (4 + 4 * s.eps + 12 * t.value) + 1 := by ring
              _ = 3 ^ s.v * (1 + 4 * s.eps + 6 * s.q + 3 ^ (t.length + 1)) + 1 := by
                rw [hcoeff]
          have hright :
              2 * (k + 1) + 3 ^ (s.v + 1 + t.length) =
                3 ^ s.v * (1 + 4 * s.eps + 6 * s.q + 3 ^ (t.length + 1)) + 1 := by
            rw [hpow, hdecomp]
            calc
              2 * (ternaryOnes s.v + 3 ^ s.v * (3 * s.q + 2 * s.eps) + 1)
                  + 3 ^ s.v * 3 ^ (t.length + 1) =
                (2 * ternaryOnes s.v + 1) + 1
                  + 3 ^ s.v * (6 * s.q + 4 * s.eps + 3 ^ (t.length + 1)) := by ring
              _ = 3 ^ s.v * (1 + 4 * s.eps + 6 * s.q + 3 ^ (t.length + 1)) + 1 := by
                rw [htwice]
                ring
          rw [drainDigitSummary_succ]
          change 4 * ((1 + s.eps) * 3 ^ s.v + 3 ^ (s.v + 1) * t.value) + 1 =
            2 * (k + 1) + 3 ^ (s.v + 1 + t.length)
          exact hleft.trans hright.symm

theorem drainDigitSummary_value_lt_pow (b : Nat) :
    (drainDigitSummary b).value < 3 ^ (drainDigitSummary b).length := by
  induction b using Nat.strongRecOn with
  | ind b ih =>
      cases b with
      | zero =>
          simp [drainDigitSummary]
      | succ k =>
          let s := drainDigitStep k
          let t := drainDigitSummary s.q
          have hs := drainDigitStep_spec k
          have hq : s.q < k + 1 := by
            have hq' : s.q ≤ k := by simpa [s] using hs.2.2
            omega
          have ht := ih s.q hq
          have heps : s.eps ≤ 1 := by simpa [s] using hs.1
          have htail : t.value + 1 ≤ 3 ^ t.length := by omega
          have hsmall : 1 + s.eps + 3 * t.value < 3 ^ (t.length + 1) := by
            have hp : 3 ^ (t.length + 1) = 3 * 3 ^ t.length := by
              rw [Nat.pow_succ]
              exact Nat.mul_comm _ _
            omega
          have hmain :
              (1 + s.eps) * 3 ^ s.v + 3 ^ (s.v + 1) * t.value
                < 3 ^ s.v * 3 ^ (t.length + 1) := by
            rw [Nat.pow_succ]
            calc
              (1 + s.eps) * 3 ^ s.v + (3 ^ s.v * 3) * t.value
                  = 3 ^ s.v * (1 + s.eps + 3 * t.value) := by ring
              _ < 3 ^ s.v * 3 ^ (t.length + 1) :=
                Nat.mul_lt_mul_of_pos_left hsmall (Nat.pow_pos (by decide))
          have hpow : 3 ^ (s.v + 1 + t.length) = 3 ^ s.v * 3 ^ (t.length + 1) := by
            rw [show s.v + 1 + t.length = s.v + (t.length + 1) by omega,
              Nat.pow_add]
          rw [drainDigitSummary_succ]
          change (1 + s.eps) * 3 ^ s.v + 3 ^ (s.v + 1) * t.value
              < 3 ^ (s.v + 1 + t.length)
          rw [hpow]
          exact hmain

theorem drainDigitSummary_length_parity (b : Nat) :
    (drainDigitSummary b).length % 2 = b % 2 := by
  induction b using Nat.strongRecOn with
  | ind b ih =>
      cases b with
      | zero =>
          simp [drainDigitSummary]
      | succ k =>
          let s := drainDigitStep k
          let t := drainDigitSummary s.q
          have hs := drainDigitStep_spec k
          have hq : s.q < k + 1 := by
            have hq' : s.q ≤ k := by simpa [s] using hs.2.2
            omega
          have ht := ih s.q hq
          have hdecomp : k = ternaryOnes s.v + 3 ^ s.v * (3 * s.q + 2 * s.eps) := by
            simpa [s] using hs.2.1
          have hpowodd : 3 ^ s.v % 2 = 1 := pow3_odd s.v
          have htaumod : ternaryOnes s.v % 2 = s.v % 2 :=
            ternaryOnes_parity s.v
          have hlowmod : (3 * s.q + 2 * s.eps) % 2 = s.q % 2 := by omega
          have hprodmod :
              (3 ^ s.v * (3 * s.q + 2 * s.eps)) % 2 = s.q % 2 := by
            rw [Nat.mul_mod, hpowodd, hlowmod]
            simp
          have hpar : (k + 1) % 2 = (s.v + 1 + s.q) % 2 := by
            rw [hdecomp]
            omega
          rw [drainDigitSummary_succ]
          change (s.v + 1 + t.length) % 2 = (k + 1) % 2
          rw [hpar]
          simp [Nat.add_mod, ht]

/-- Count a fixed low-to-high ternary digit in an integer word of fixed length. -/
def countDigitInt (digit : Int) : Nat → Int → Nat
  | 0, _ => 0
  | n + 1, x => (if x % 3 = digit then 1 else 0) + countDigitInt digit n (x / 3)

theorem int_digit_split (out tail : Int) (hout0 : 0 ≤ out) (hout1 : out < 3) :
    (out + 3 * tail) % 3 = out ∧ (out + 3 * tail) / 3 = tail := by
  omega

theorem countDigitInt_shift (digit out tail : Int) (n : Nat)
    (hout0 : 0 ≤ out) (hout1 : out < 3) :
    countDigitInt digit (n + 1) (out + 3 * tail) =
      (if out = digit then 1 else 0) + countDigitInt digit n tail := by
  have h := int_digit_split out tail hout0 hout1
  simp [countDigitInt, h.1, h.2]

theorem countDigitInt_pow_shift (digit : Int) (hd : digit = 1 ∨ digit = 2)
    (v n : Nat) (z : Int) :
    countDigitInt digit (v + n) (Int.ofNat (3 ^ v) * z) =
      countDigitInt digit n z := by
  induction v with
  | zero =>
      simp [countDigitInt]
  | succ v ih =>
      have hlen : (v + 1) + n = (v + n) + 1 := by omega
      have hpow : Int.ofNat (3 ^ (v + 1)) * z =
          3 * (Int.ofNat (3 ^ v) * z) := by
        simp [Nat.pow_succ, Int.natCast_mul]
        ring
      rw [hlen, hpow]
      have hsplit := int_digit_split (0 : Int) (Int.ofNat (3 ^ v) * z)
        (by norm_num) (by norm_num)
      simp only [countDigitInt, hsplit.1, hsplit.2]
      have hz : (0 : Int) ≠ digit := by
        rcases hd with h | h <;> simp [h]
      simpa [hz] using ih

theorem countDigitInt_sparse (digit : Int) (hd : digit = 1 ∨ digit = 2)
    (v L eps : Nat) (N : Int) (heps : eps ≤ 1) :
    countDigitInt digit (v + 1 + L)
        (Int.ofNat (3 ^ v) * (Int.ofNat (1 + eps) + 3 * N)) =
      (if Int.ofNat (1 + eps) = digit then 1 else 0) +
        countDigitInt digit L N := by
  have hlen : v + 1 + L = v + (L + 1) := by omega
  rw [hlen]
  rw [countDigitInt_pow_shift digit hd v (L + 1)
    (Int.ofNat (1 + eps) + 3 * N)]
  have hout0 : 0 ≤ Int.ofNat (1 + eps) := by positivity
  have hnat : 1 + eps < 3 := by omega
  have hout1 : Int.ofNat (1 + eps) < 3 := by exact_mod_cast hnat
  have hsplit := int_digit_split (Int.ofNat (1 + eps)) N hout0 hout1
  have hsplit' :
      (1 + (eps : Int) + 3 * N) % 3 = 1 + (eps : Int) ∧
      (1 + (eps : Int) + 3 * N) / 3 = N := by
    simpa [Int.natCast_add, Int.natCast_one] using hsplit
  simp [countDigitInt, hsplit'.1, hsplit'.2]

theorem runStats_count_digit (n b : Nat) (s : DrainState) :
    (runStats n b s).ones =
        countDigitInt 1 n (runStats n b s).output ∧
    (runStats n b s).twos =
        countDigitInt 2 n (runStats n b s).output := by
  induction n generalizing b s with
  | zero =>
      simp [runStats, countDigitInt]
  | succ n ih =>
      cases hst : step s (b % 3) with
      | mk s' out =>
          have hout : 0 ≤ out ∧ out ≤ 2 := by
            simpa [hst] using step_output_bounds s (b % 3)
          have htail := ih (b / 3) s'
          constructor
          · simp only [runStats, hst]
            rw [countDigitInt_shift 1 out
              (runStats n (b / 3) s').output n hout.1 (by omega)]
            rw [htail.1]
            omega
          · simp only [runStats, hst]
            rw [countDigitInt_shift 2 out
              (runStats n (b / 3) s').output n hout.1 (by omega)]
            rw [htail.2]
            omega

theorem drainDigitSummary_counts (b : Nat) :
    countDigitInt 1 (drainDigitSummary b).length
        (Int.ofNat (drainDigitSummary b).value) =
          (drainDigitSummary b).ones ∧
    countDigitInt 2 (drainDigitSummary b).length
        (Int.ofNat (drainDigitSummary b).value) =
          (drainDigitSummary b).twos := by
  induction b using Nat.strongRecOn with
  | ind b ih =>
      cases b with
      | zero =>
          simp [drainDigitSummary, countDigitInt]
      | succ k =>
          let s := drainDigitStep k
          let t := drainDigitSummary s.q
          have hs := drainDigitStep_spec k
          have hq : s.q < k + 1 := by
            have hq' : s.q ≤ k := by simpa [s] using hs.2.2
            omega
          have ht := ih s.q hq
          have hval :
              Int.ofNat ((1 + s.eps) * 3 ^ s.v + 3 ^ (s.v + 1) * t.value) =
                Int.ofNat (3 ^ s.v) *
                  (Int.ofNat (1 + s.eps) + 3 * Int.ofNat t.value) := by
            simp [Nat.pow_succ, Int.natCast_mul, Int.natCast_add]
            ring
          have hcount1 := countDigitInt_sparse 1 (by left; rfl)
            s.v t.length s.eps (Int.ofNat t.value) (by simpa [s] using hs.1)
          have hcount2 := countDigitInt_sparse 2 (by right; rfl)
            s.v t.length s.eps (Int.ofNat t.value) (by simpa [s] using hs.1)
          rw [drainDigitSummary_succ]
          change
            countDigitInt 1 (s.v + 1 + t.length)
                (Int.ofNat ((1 + s.eps) * 3 ^ s.v + 3 ^ (s.v + 1) * t.value)) =
                  (if s.eps = 0 then 1 else 0) + t.ones ∧
            countDigitInt 2 (s.v + 1 + t.length)
                (Int.ofNat ((1 + s.eps) * 3 ^ s.v + 3 ^ (s.v + 1) * t.value)) =
                  s.eps + t.twos
          rw [hval, hcount1, hcount2]
          rcases ht with ⟨ht1, ht2⟩
          constructor
          · rw [ht1]
            by_cases he : s.eps = 0
            · simp [he]
            · have he1 : s.eps = 1 := by omega
              simp [he, he1]
          · rw [ht2]
            by_cases he : s.eps = 0
            · simp [he]
            · have he1 : s.eps = 1 := by omega
              simp [he, he1]

theorem drainB_digit_summary (b : Nat) :
    ∀ a d aa dd : Nat, b ≤ ternaryOnes a →
      drainB a b d = some (.D aa dd) →
      (aa + (drainDigitSummary b).length =
          a + 2 * (drainDigitSummary b).twos) ∧
      (2 * aa + dd =
          2 * a + d + 3 * b
            + 2 * ((drainDigitSummary b).ones + (drainDigitSummary b).twos)) := by
  induction b using Nat.strongRecOn with
  | ind b ih =>
      intro a d aa dd hbudget hdrain
      cases b with
      | zero =>
          simp [drainB] at hdrain
          cases hdrain
          simp [drainDigitSummary]
          constructor <;> omega
      | succ k =>
          let s := drainDigitStep k
          have hs := drainDigitStep_spec k
          have hstrict : k < ternaryOnes a := by omega
          have hdecomp : k = ternaryOnes s.v
              + 3 ^ s.v * (3 * s.q + 2 * s.eps) := by
            simpa [s] using hs.2.1
          have htau : ternaryOnes s.v ≤ k := by omega
          have hvlt : s.v < a := by
            by_contra hnot
            have hav : a ≤ s.v := by omega
            have hmono := ternaryOnes_mono a s.v hav
            omega
          have ha : s.v + 1 - s.eps ≤ a := by
            have heps : s.eps ≤ 1 := by simpa [s] using hs.1
            omega
          let a1 := a + 2 * s.eps - (s.v + 1)
          let d1 := d + 2 * (k + 1) + 3
              + (6 * s.q + 1 + 4 * s.eps) * ternaryOnes s.v
              + 2 * s.v + 2 * (1 - s.eps)
          have heval : evalA a k (d + 2 * (k + 1) + 3) = some (a1, s.q, d1) := by
            simpa [a1, d1] using
              (evalA_3adic_run a k (d + 2 * (k + 1) + 3)
                s.v s.q s.eps (by simpa [s] using hs.1)
                hdecomp ha)
          have hbudget1 : s.q ≤ ternaryOnes a1 := by
            obtain ⟨a1', q', d1', heval', hb1⟩ :=
              evalA_ones_budget a k (d + 2 * (k + 1) + 3) hstrict
            rw [heval] at heval'
            simp only [Option.some.injEq, Prod.mk.injEq] at heval'
            rcases heval' with ⟨hA, hq, hD⟩
            subst a1'
            subst q'
            subst d1'
            exact hb1
          rw [drainB] at hdrain
          have hpos : k + 1 ≠ 0 := by omega
          simp only [if_neg hpos, Nat.succ_sub_one, heval, Option.bind_some] at hdrain
          have hlt : s.q < k + 1 := by
            have hq : s.q ≤ k := by simpa [s] using hs.2.2
            omega
          simp only [if_pos hlt] at hdrain
          have hrec := ih s.q hlt a1 d1 aa dd hbudget1 hdrain
          have hpot := evalA_weighted_exact a k
            (d + 2 * (k + 1) + 3) a1 s.q d1 hstrict heval
          have hR : (if s.eps = 0 then 1 else 0) + s.eps = 1 := by
            cases s.eps with
            | zero => simp
            | succ e =>
                have he : e = 0 := by omega
                subst e
                simp
          rw [drainDigitSummary_succ]
          constructor
          · change aa + (s.v + 1 + (drainDigitSummary s.q).length) =
                a + 2 * (s.eps + (drainDigitSummary s.q).twos)
            have hfirst := hrec.1
            dsimp [a1] at hfirst
            omega
          · change 2 * aa + dd =
                2 * a + d + 3 * (k + 1)
                  + 2 * (((if s.eps = 0 then 1 else 0)
                    + (drainDigitSummary s.q).ones)
                    + (s.eps + (drainDigitSummary s.q).twos))
            have hsecond := hrec.2
            dsimp [a1] at hpot
            have hR' :
                ((if s.eps = 0 then 1 else 0)
                  + (drainDigitSummary s.q).ones)
                  + (s.eps + (drainDigitSummary s.q).twos) =
                1 + (drainDigitSummary s.q).ones
                  + (drainDigitSummary s.q).twos := by omega
            rw [hR']
            omega

/-- Exact source drain formula in terms of the three-state transducer's output digits. -/
theorem drainB_digit_transducer (b a d aa dd : Nat)
    (hbudget : b ≤ ternaryOnes a)
    (hdrain : drainB a b d = some (.D aa dd)) :
    aa + (drainDigitSummary b).length =
        a + 2 * (runStats (drainDigitSummary b).length
          (b % 3 ^ (drainDigitSummary b).length) DrainState.A).twos ∧
    dd + 4 * (runStats (drainDigitSummary b).length
          (b % 3 ^ (drainDigitSummary b).length) DrainState.A).twos =
        d + 3 * b + 2 * (drainDigitSummary b).length
          + 2 * ((runStats (drainDigitSummary b).length
            (b % 3 ^ (drainDigitSummary b).length) DrainState.A).ones
            + (runStats (drainDigitSummary b).length
              (b % 3 ^ (drainDigitSummary b).length) DrainState.A).twos) := by
  let L := (drainDigitSummary b).length
  let stats := runStats L (b % 3 ^ L) DrainState.A
  have hsource := drainB_digit_summary b a d aa dd hbudget hdrain
  have hpar : L % 2 = b % 2 := by
    simpa [L] using drainDigitSummary_length_parity b
  have hbound : (drainDigitSummary b).value < 3 ^ L := by
    simpa [L] using drainDigitSummary_value_lt_pow b
  have hformula := drainDigitSummary_value_formula b
  have hformulaInt :
      4 * Int.ofNat (drainDigitSummary b).value + 1 =
        2 * Int.ofNat b + pow3 L := by
    have hcast := congrArg Int.ofNat hformula
    simpa [pow3_eq_nat, Int.natCast_add, Int.natCast_mul] using hcast
  have hvalueBound : Int.ofNat (drainDigitSummary b).value < pow3 L := by
    rw [pow3_eq_nat]
    exact Int.ofNat_lt.mpr hbound
  have hpowSucc : pow3 (L + 1) = 3 * pow3 L := by
    simp [pow3]
  have hsize : 2 * Int.ofNat b - 1 < pow3 (L + 1) := by
    rw [hpowSucc]
    omega
  have hrun := runStats_exact_of_bounds L b hpar hsize
  have houtput : stats.output = Int.ofNat (drainDigitSummary b).value := by
    have hrun' : 4 * (runStats L (b % 3 ^ L) DrainState.A).output =
        2 * Int.ofNat b - 1 + pow3 L := by
      simpa [stats] using hrun
    change (runStats L (b % 3 ^ L) DrainState.A).output =
      Int.ofNat (drainDigitSummary b).value
    omega
  have hcounts := runStats_count_digit L (b % 3 ^ L) DrainState.A
  have hsummaryCounts := drainDigitSummary_counts b
  have hones : stats.ones = (drainDigitSummary b).ones := by
    rw [hcounts.1, houtput]
    exact hsummaryCounts.1
  have htwos : stats.twos = (drainDigitSummary b).twos := by
    rw [hcounts.2, houtput]
    exact hsummaryCounts.2
  rcases hsource with ⟨hfirst, hweighted⟩
  constructor
  · rw [htwos]
    simpa [L] using hfirst
  · have htarget : dd + 4 * (drainDigitSummary b).twos =
        d + 3 * b + 2 * (drainDigitSummary b).length
          + 2 * ((drainDigitSummary b).ones + (drainDigitSummary b).twos) := by
      omega
    have htarget' : dd + 4 * stats.twos =
        d + 3 * b + 2 * L + 2 * (stats.ones + stats.twos) := by
      rw [hones, htwos]
      simpa [L] using htarget
    exact htarget'

/-- The full source evaluator-call count, reduced modulo three, is exactly
the phase register of the nine-state drain product.  The weighted source
identity identifies the full call count with the number of nonzero emitted
digits, while `drainNineRun_count_mod3` computes that count in finite state. -/
def drainDigitPhase9 (b : Nat) : Nat :=
  (drainNineRun (drainDigitSummary b).length
    (b % 3 ^ (drainDigitSummary b).length) (DrainState.A, 0)).2

theorem drainB_full_count_mod3
    (b a d aa dd : Nat)
    (hbudget : b ≤ ternaryOnes a)
    (hdrain : drainB a b d = some (.D aa dd)) :
    ∃ r : Nat,
      2 * aa + dd = 2 * a + d + 3 * b + 2 * r ∧
      r % 3 = drainDigitPhase9 b := by
  let L := (drainDigitSummary b).length
  let stats := runStats L (b % 3 ^ L) DrainState.A
  obtain ⟨r, hr⟩ := drainB_weighted_exact b a d aa dd hbudget hdrain
  have htrans := drainB_digit_transducer b a d aa dd hbudget hdrain
  have hcount : r = stats.ones + stats.twos := by
    dsimp [stats, L] at *
    omega
  have hphase := drainNineRun_count_mod3 L (b % 3 ^ L) DrainState.A
  refine ⟨r, hr, ?_⟩
  dsimp [drainDigitPhase9, L]
  rw [hcount]
  simpa [stats] using hphase.symm

#print axioms drainB_full_count_mod3

#print axioms drainB_digit_transducer

/-- The actual source drain's signed first-counter drop and full evaluator-call
count are exactly the weighted digit statistics used by the carry automaton.
The count is the complete `drainB` iteration count: when the RE high-level
branch bundles its initial evaluator into the `drainB` argument, that
evaluator is counted here too. -/
def drainDigitStats (b : Nat) : DrainStats :=
  runStats (drainDigitSummary b).length
    (b % 3 ^ (drainDigitSummary b).length) DrainState.A

theorem drainB_digit_source_correction_interface
    (b a d aa dd : Nat) (s : Sector) (br : Branch)
    (hbudget : b ≤ ternaryOnes a)
    (hdrain : drainB a b d = some (.D aa dd)) :
    (a : Int) - (aa : Int) =
      ((drainDigitSummary b).length : Int) -
        2 * ((drainDigitStats b).twos : Int) ∧
    ∃ r : Nat,
      2 * aa + dd = 2 * a + d + 3 * b + 2 * r ∧
      r = (drainDigitStats b).ones + (drainDigitStats b).twos ∧
      -(34 * ((drainDigitSummary b).length : Int) + 122) ≤
        corrC s br ((a : Int) - (aa : Int)) (r : Int) ∧
      corrC s br ((a : Int) - (aa : Int)) (r : Int) ≤
        34 * ((drainDigitSummary b).length : Int) + 122 ∧
      -(24 * ((drainDigitSummary b).length : Int) + 84) ≤
        corrF s br ((a : Int) - (aa : Int)) (r : Int) ∧
      corrF s br ((a : Int) - (aa : Int)) (r : Int) ≤
        24 * ((drainDigitSummary b).length : Int) + 84 := by
  let L := (drainDigitSummary b).length
  let stats := drainDigitStats b
  have htrans := drainB_digit_transducer b a d aa dd hbudget hdrain
  have hfirst : aa + L = a + 2 * stats.twos := by
    simpa [L, stats, drainDigitStats] using htrans.1
  have hsecond :
      dd + 4 * stats.twos =
        d + 3 * b + 2 * L + 2 * (stats.ones + stats.twos) := by
    simpa [L, stats, drainDigitStats] using htrans.2
  have hdrop : (a : Int) - (aa : Int) =
      (L : Int) - 2 * (stats.twos : Int) := by omega
  obtain ⟨r, hweighted⟩ :=
    drainB_weighted_exact b a d aa dd hbudget hdrain
  have hcount : r = stats.ones + stats.twos := by omega
  have hweights := runStats_weight_bounds L (b % 3 ^ L) DrainState.A
  have hE0 : 0 ≤ (stats.twos : Int) := by
    simpa [weightedE, stats, drainDigitStats, L] using hweights.1
  have hER : (stats.twos : Int) ≤ ((stats.ones + stats.twos : Nat) : Int) := by
    simpa [weightedE, weightedR, stats, drainDigitStats, L] using hweights.2.1
  have hRL : ((stats.ones + stats.twos : Nat) : Int) ≤ (L : Int) := by
    simpa [weightedR, stats, drainDigitStats, L] using hweights.2.2
  have hbound := correction_count_bounds s br (L : Int)
    (stats.twos : Int) ((stats.ones + stats.twos : Nat) : Int)
    hE0 hER hRL
  have hRInt : (r : Int) = ((stats.ones + stats.twos : Nat) : Int) := by omega
  have hbound' :
      -(34 * (L : Int) + 122) ≤
        corrC s br ((a : Int) - (aa : Int)) (r : Int) ∧
      corrC s br ((a : Int) - (aa : Int)) (r : Int) ≤
        34 * (L : Int) + 122 ∧
      -(24 * (L : Int) + 84) ≤
        corrF s br ((a : Int) - (aa : Int)) (r : Int) ∧
      corrF s br ((a : Int) - (aa : Int)) (r : Int) ≤
        24 * (L : Int) + 84 := by
    simpa [hdrop, hRInt] using hbound
  exact ⟨hdrop, r, hweighted, hcount,
    hbound'.1, hbound'.2.1, hbound'.2.2.1, hbound'.2.2.2⟩

#print axioms drainB_digit_source_correction_interface

end BB6.Agent1DrainDigitStatsSource
