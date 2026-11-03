import Lean

/-!
Exact ternary drain identities for the BB6 #623 accelerated arithmetic.
This standalone file duplicates the two elementary source arithmetic
definitions from google-deepmind/cryptids@c86f158 (Apache-2.0).
It does NOT itself prove equivalence with the upstream raw Turing machine.
Lean 4.36.0-rc2, no sorry or custom axioms.
-/

namespace BB623
inductive S where
  | D (a d : Nat)
  deriving DecidableEq, Repr

def evalA (a k m : Nat) : Option (Nat × Nat × Nat) :=
  if k % 3 = 2 then some (a + 1, k / 3, m)
  else if a = 0 then (if k % 3 = 0 then none else some (0, k / 3, m))
  else if k % 3 = 0 then some (a - 1, k / 3, m + 2)
  else evalA (a - 1) (k / 3) (m + 2 * (k / 3) + 3)
termination_by a
decreasing_by omega

def drainB (a b d : Nat) : Option S :=
  if b = 0 then some (.D a d)
  else
    (evalA a (b - 1) (d + 2 * b + 3)).bind fun p =>
      if p.2.1 < b then drainB p.1 p.2.1 p.2.2 else none
termination_by b
decreasing_by omega

theorem evalA_nine (x m : Nat) :
    evalA 3 (9*x+7) m = some (3,x,m+6*x+7) := by
  have h1 : (9*x+7)%3 = 1 := by omega
  have h2 : (9*x+7)/3 = 3*x+2 := by omega
  have h3 : (3*x+2)%3 = 2 := by omega
  have h4 : (3*x+2)/3 = x := by omega
  rw [evalA]
  simp [h1,h2,evalA,h3,h4]
  omega

theorem drainB_nine (x d : Nat) :
    drainB 3 (9*x+8) d = drainB 3 x (d+24*x+26) := by
  rw [drainB]
  have hn : 9*x+8 ≠ 0 := by omega
  have hp : 9*x+8-1 = 9*x+7 := by omega
  have hlt : x < 9*x+8 := by omega
  simp only [if_neg hn, hp, evalA_nine, Option.bind_some, if_pos hlt]
  congr 1
  omega


/-- Source-matched evaluator residual bound (same argument as Agent49). -/
theorem evalA_b_le_k (a : Nat) :
    ∀ k m aa bb dd : Nat, evalA a k m = some (aa,bb,dd) → bb ≤ k := by
  induction a with
  | zero =>
    intro k m aa bb dd h
    rw [evalA] at h
    by_cases h2 : k%3 = 2
    · simp [h2] at h
      cases h
      omega
    · by_cases h0 : k%3 = 0
      · simp [h2,h0] at h
      · simp [h2,h0] at h
        cases h
        omega
  | succ a ih =>
    intro k m aa bb dd h
    rw [evalA] at h
    by_cases h2 : k%3 = 2
    · simp [h2] at h
      cases h
      omega
    · by_cases h0 : k%3 = 0
      · simp [h2,h0] at h
        cases h
        omega
      · simp [h2,h0] at h
        have ht := ih (k/3) (m+2*(k/3)+3) aa bb dd h
        omega

theorem evalA_nine_minus_one (a b m : Nat) (hb : 0 < b) :
    evalA a (9*b-1) m = some (a+1,3*b-1,m) := by
  have hm : (9*b-1)%3 = 2 := by omega
  have hd : (9*b-1)/3 = 3*b-1 := by omega
  rw [evalA]
  simp [hm,hd]

theorem evalA_three_minus_two (a b m : Nat) (hb : 0 < b) :
    evalA (a+1) (3*b-2) m = evalA a (b-1) (m+2*(b-1)+3) := by
  have hm : (3*b-2)%3 = 1 := by omega
  have hz : (3*b-2)%3 ≠ 0 := by omega
  have hd : (3*b-2)/3 = b-1 := by omega
  rw [evalA]
  simp [hm,hz,hd]

/-- Exact two-digit pumping for ALL positive block counts, including halting. -/
theorem drainB_scale_nine (a b d : Nat) (hb : 0 < b) :
    drainB a (9*b) d = drainB a b (d+24*b+2) := by
  have h9 : 9*b ≠ 0 := by omega
  have h3 : 3*b-1 ≠ 0 := by omega
  have hfirst : 3*b-1 < 9*b := by omega
  have h3sub : (3*b-1)-1=3*b-2 := by omega
  have hm9 : d+2*(9*b)+3=d+18*b+3 := by omega
  have hm3 : (d+18*b+3)+2*(3*b-1)+3=d+24*b+4 := by omega
  have hm : (d+24*b+4)+2*(b-1)+3=(d+24*b+2)+2*b+3 := by omega
  rw [drainB]
  simp only [if_neg h9, hm9, evalA_nine_minus_one a b (d+18*b+3) hb,
    Option.bind_some, if_pos hfirst]
  rw [drainB]
  simp only [if_neg h3, h3sub, hm3, evalA_three_minus_two a b (d+24*b+4) hb, hm]
  have hright : drainB a b (d+24*b+2) =
      (evalA a (b-1) ((d+24*b+2)+2*b+3)).bind (fun p =>
         if p.2.1 < b then drainB p.1 p.2.1 p.2.2 else none) := by
    rw [drainB]
    simp only [if_neg (by omega : b ≠ 0)]
  rw [hright]
  cases he : evalA a (b-1) ((d+24*b+2)+2*b+3) with
  | none => simp [he]
  | some p =>
    rcases p with ⟨aa,bb,dd⟩
    have small := evalA_b_le_k a (b-1) ((d+24*b+2)+2*b+3) aa bb dd he
    have hbb : bb < b := by omega
    have hbb3 : bb < 3*b-1 := by omega
    simp only [he, Option.bind_some, if_pos hbb, if_pos hbb3]

#print axioms drainB_scale_nine

theorem evalA_four (m : Nat) :
    evalA 3 4 m = some (0,0,m+10) := by
  simp [evalA, Nat.add_assoc]

theorem evalA_sixteen (m : Nat) :
    evalA 3 16 m = some (3,1,m+13) := by
  simp [evalA, Nat.add_assoc]

theorem evalA_zero (m : Nat) :
    evalA 3 0 m = some (2,0,m+2) := by
  simp [evalA]

def oddPulse : Nat → Nat
  | 0 => 5
  | n+1 => 9 * oddPulse n + 8

def oddGain : Nat → Nat
  | 0 => 23
  | n+1 => 24 * oddPulse n + 26 + oddGain n

def evenPulse : Nat → Nat
  | 0 => 17
  | n+1 => 9 * evenPulse n + 8

def evenGain : Nat → Nat
  | 0 => 57
  | n+1 => 24 * evenPulse n + 26 + evenGain n

theorem oddPulse_run (n d : Nat) :
    drainB 3 (oddPulse n) d = some (.D 0 (d + oddGain n)) := by
  induction n generalizing d with
  | zero =>
    change drainB 3 5 d = some (.D 0 (d + 23))
    rw [drainB]
    simp only [if_neg (by decide : (5:Nat) ≠ 0), Nat.reduceSub, Nat.reduceMul, Nat.reduceAdd]
    rw [evalA_four]
    simp only [Option.bind_some, if_pos (by decide : (0:Nat) < 5)]
    rw [drainB]
    simp only [if_pos (by decide : (0:Nat) = 0)]
    congr 1
  | succ n ih =>
    change drainB 3 (9 * oddPulse n + 8) d =
      some (.D 0 (d + (24 * oddPulse n + 26 + oddGain n)))
    rw [drainB_nine, ih]
    simp only [Nat.add_assoc]

theorem evenPulse_run (n d : Nat) :
    drainB 3 (evenPulse n) d = some (.D 2 (d + evenGain n)) := by
  induction n generalizing d with
  | zero =>
    change drainB 3 17 d = some (.D 2 (d + 57))
    rw [drainB]
    simp only [if_neg (by decide : (17:Nat) ≠ 0), Nat.reduceSub, Nat.reduceMul, Nat.reduceAdd]
    rw [evalA_sixteen]
    simp only [Option.bind_some, if_pos (by decide : 1 < 17)]
    rw [drainB]
    simp only [if_neg (by decide : (1:Nat) ≠ 0), Nat.reduceSub, Nat.reduceMul, Nat.reduceAdd]
    rw [evalA_zero]
    simp only [Option.bind_some, if_pos (by decide : (0:Nat) < 1)]
    rw [drainB]
    simp only [if_pos (by decide : (0:Nat) = 0)]
    congr 1
  | succ n ih =>
    change drainB 3 (9 * evenPulse n + 8) d =
      some (.D 2 (d + (24 * evenPulse n + 26 + evenGain n)))
    rw [drainB_nine, ih]
    simp only [Nat.add_assoc]

theorem oddPulse_closed (n : Nat) :
    oddPulse n + 1 = 6 * 9 ^ n := by
  induction n with
  | zero => decide
  | succ n ih =>
    simp only [oddPulse, Nat.pow_succ]
    omega

theorem evenPulse_closed (n : Nat) :
    evenPulse n + 1 = 18 * 9 ^ n := by
  induction n with
  | zero => decide
  | succ n ih =>
    simp only [evenPulse, Nat.pow_succ]
    omega

theorem oddGain_closed (n : Nat) :
    oddGain n = 18 * 9 ^ n + 2*n + 5 := by
  induction n with
  | zero => decide
  | succ n ih =>
    have h := oddPulse_closed n
    simp only [oddGain, Nat.pow_succ]
    omega

theorem evenGain_closed (n : Nat) :
    evenGain n = 54 * 9 ^ n + 2*n + 3 := by
  induction n with
  | zero => decide
  | succ n ih =>
    have h := evenPulse_closed n
    simp only [evenGain, Nat.pow_succ]
    omega

theorem odd_pulse_exact (n d : Nat) :
    drainB 3 (oddPulse n) d =
      some (.D 0 (d + 18*9^n + 2*n + 5)) := by
  rw [oddPulse_run, oddGain_closed]
  simp only [Nat.add_assoc]

theorem even_pulse_exact (n d : Nat) :
    drainB 3 (evenPulse n) d =
      some (.D 2 (d + 54*9^n + 2*n + 3)) := by
  rw [evenPulse_run, evenGain_closed]
  simp only [Nat.add_assoc]

#print axioms odd_pulse_exact
#print axioms even_pulse_exact
#print axioms oddPulse_run
#print axioms evenPulse_run
#print axioms evalA_nine
#print axioms drainB_nine
end BB623
