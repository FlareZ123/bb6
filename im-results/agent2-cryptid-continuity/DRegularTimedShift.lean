import Lean.Elab.Tactic.Omega
import DRegularDurationShift

set_option maxRecDepth 8192
set_option linter.unusedSimpArgs false

namespace BB6.DRegularTimedShift
open DRegular BB6.DRegularShift BB6.DRegularDurationShift

def quadCoeff : Nat → Nat
 | 0 => 0
 | n+1 => 12*(3^n)*(3^n) + 64*quadCoeff n

def linearCoeff : Nat → L → Nat
 | 0, _ => 0
 | n+1, s => (3^n)*slope s + 8*linearCoeff n ((next s).getD s)

private theorem combine (D E L U M Q p : Nat) :
    (D + (E*L)*p + 12*(E*p)*(E*p)) +
    (U + M*(8*p) + Q*(8*p)*(8*p)) =
    (D+U) + (E*L+8*M)*p + (12*E*E+64*Q)*p*p := by
  have h1 : 12*(E*p)*(E*p) = (12*E*E)*p*p := by ac_rfl
  have h2 : Q*(8*p)*(8*p) = (64*Q)*p*p := by
    calc
      Q*(8*p)*(8*p) = (8*8*Q)*p*p := by ac_rfl
      _ = (64*Q)*p*p := by rfl
  have h3 : M*(8*p)=(8*M)*p := by ac_rfl
  rw [h1,h2,h3]
  simp only [Nat.add_mul, Nat.mul_add, Nat.mul_assoc]
  omega

/-- Exact elapsed primitive-time difference over any defined regular
    itinerary, polynomial in the 3^n unary-lift parameter. -/
theorem accumulated_shift (n : Nat) : ∀ (s t : L) (p : Nat), Canon s →
    run n s = some t →
    accumulated n (shiftNat s (3^n*p)) =
      accumulated n s + linearCoeff n s * p + quadCoeff n*p*p := by
  induction n with
  | zero =>
    intro s t p hc hr
    simp [accumulated,linearCoeff,quadCoeff]
  | succ n ih =>
    intro s t p hc hr
    cases hs : next s with
    | none =>
      simp [run,hs] at hr
    | some u =>
      have hu : run n u = some t := by simpa [run,hs] using hr
      have hc' : Canon u := DRegular.next_canon s u hc hs
      have hpow3 : 3^(n+1)*p = 3*(3^n*p) := by
        simp only [Nat.pow_succ]
        ac_rfl
      have hstep : next (shiftNat s (3^(n+1)*p)) =
          some (shiftNat u (3^n*(8*p))) := by
        rw [hpow3, next_shift_raw s hc.1 (3^n*p), hs]
        simp only [Option.map_some]
        congr 1
        simp only [shiftNat]
        congr 1
        ac_rfl
      have haccbase : accumulated (n+1) s =
          duration s + accumulated n u := by simp [accumulated,hs]
      have hacclift : accumulated (n+1) (shiftNat s (3^(n+1)*p)) =
          duration (shiftNat s (3^(n+1)*p)) +
            accumulated n (shiftNat u (3^n*(8*p))) := by
        simp [accumulated,hstep]
      have hduration : duration (shiftNat s (3^(n+1)*p)) =
          duration s + (3^n*slope s)*p + 12*(3^n*p)*(3^n*p) := by
        rw [hpow3]
        change duration (bumpInput s (3^n*p)) = _
        rw [duration_shift s hc.1 (3^n*p)]
        congr 1
        ac_rfl
      have hih := ih u t (8*p) hc' hu
      rw [hacclift,haccbase,hduration,hih]
      rw [show linearCoeff (n+1) s = 3^n*slope s+8*linearCoeff n u
        by simp [linearCoeff,hs]]
      rw [show quadCoeff (n+1) = 12*3^n*3^n+64*quadCoeff n by rfl]
      change (duration s + (3^n*slope s)*p + 12*(3^n*p)*(3^n*p)) +
          (accumulated n u + linearCoeff n u*(8*p) + quadCoeff n*(8*p)*(8*p)) =
        (duration s+accumulated n u) +
          ((3^n*slope s+8*linearCoeff n u)*p) +
          (12*3^n*3^n+64*quadCoeff n)*p*p
      exact combine (duration s) (3^n) (slope s) (accumulated n u)
        (linearCoeff n u) (quadCoeff n) p

private theorem three_square (n : Nat) : 3^n*3^n=9^n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    calc
      3^(n+1)*3^(n+1) = (3^n*3^n)*(3*3) := by
        simp only [Nat.pow_succ]
        ac_rfl
      _ = 9^(n+1) := by rw [ih]; simp only [Nat.pow_succ]

/-- Closed integer identity for universal quadratic coefficient:
    55*Q_n+12*9^n=12*64^n, hence Q_n=12*(64^n-9^n)/55. -/
theorem quad_closed (n : Nat) :
    55*quadCoeff n + 12*9^n = 12*64^n := by
  induction n with
  | zero => decide
  | succ n ih =>
    have hthree : 12*3^n*3^n = 12*9^n := by
      calc
        12*3^n*3^n = 12*(3^n*3^n) := by ac_rfl
        _ = 12*9^n := by rw [three_square]
    have hrec : quadCoeff (n+1) = 12*9^n+64*quadCoeff n := by
      change 12*3^n*3^n+64*quadCoeff n=_
      rw [hthree]
    calc
      55*quadCoeff (n+1)+12*9^(n+1) =
          64*(55*quadCoeff n+12*9^n) := by
        rw [hrec]
        simp only [Nat.pow_succ]
        simp only [Nat.mul_add, Nat.add_mul, Nat.mul_assoc]
        omega
      _ = 64*(12*64^n) := by rw [ih]
      _ = 12*64^(n+1) := by simp only [Nat.pow_succ]; ac_rfl

#print axioms quad_closed
#print axioms accumulated_shift
end BB6.DRegularTimedShift
