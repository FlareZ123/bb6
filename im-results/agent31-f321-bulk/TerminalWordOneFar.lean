import TerminalWordCandidate
import Lean.Elab.Tactic.Omega

namespace BB6.Agent31F321Density

theorem terminalNumerator_high (c:Nat) (w:List InverseLetter) :
    terminalNumerator c (.high::w) =
      terminalNumerator c w + ((c:Int)+3) * (2:Int)^(compile w).shift := by
  unfold terminalNumerator
  simp only [compile, advance]
  have hp : (2:Int)^((compile w).shift+1) =
      2 * (2:Int)^(compile w).shift := by
    rw [Int.pow_succ]
    ac_rfl
  rw [hp]
  let P : Int := (2:Int)^(compile w).shift
  let S : Int := (compile w).sumDecrease
  let V : Int := (compile w).v
  change V + P * (2-S) + (2*P) * (S+1+(c:Int)-1) =
    (V + P*(S+(c:Int)-1)) + ((c:Int)+3)*P
  have h2PS : (2*P)*S = 2*(P*S) := by ac_rfl
  have h2Pc : (2*P)*(c:Int) = 2*(P*(c:Int)) := by ac_rfl
  have hcP : ((c:Int)+3)*P = P*(c:Int)+3*P := by
    rw [Int.add_mul]
    have hcp : (c:Int)*P = P*(c:Int) := by ac_rfl
    rw [hcp]
  have hPS : P*(S+(c:Int)-1) = P*S+P*(c:Int)-P := by
    simp only [Int.mul_sub, Int.mul_add, Int.mul_one]
  have hP2S : P*(2-S) = 2*P-P*S := by
    simp only [Int.mul_sub]
    have h : P*2=2*P := by ac_rfl
    rw [h]
  rw [hcP,hPS,hP2S]
  simp only [Int.mul_add, Int.mul_sub] at *
  rw [h2PS, h2Pc]
  omega

def highThenFar : Nat → List InverseLetter
  | 0 => [.far]
  | n+1 => .high :: highThenFar n

theorem highThenFar_shift (n:Nat) :
    (compile (highThenFar n)).shift = n+2 := by
  induction n with
  | zero => rfl
  | succ n ih => simp [highThenFar, compile, advance, ih]

theorem highThenFar_denom (n:Nat) : terminalDenom (highThenFar n) = 7 := by
  induction n with
  | zero => decide
  | succ n ih => simpa [highThenFar,terminalDenom] using ih

theorem highThenFar_num_one (n:Nat) :
    terminalNumerator 1 (highThenFar n) = (2:Int)^(n+4)+3 := by
  induction n with
  | zero => decide
  | succ n ih =>
      rw [highThenFar, terminalNumerator_high, ih, highThenFar_shift]
      have hp : (2:Int)^(n+1+4) = 2*(2:Int)^(n+4) := by
        rw [show n+1+4=(n+4)+1 by omega, Int.pow_succ]
        ac_rfl
      have he : (2:Int)^(n+2) * 4 = (2:Int)^(n+4) := by
        calc
          (2:Int)^(n+2) * 4 = (2:Int)^(n+2) * (2:Int)^2 := by rfl
          _ = (2:Int)^((n+2)+2) := (Int.pow_add 2 (n+2) 2).symm
          _ = (2:Int)^(n+4) := by congr 1 <;> omega
      change (2:Int)^(n+4) + 3 + 4*(2:Int)^(n+2) = (2:Int)^(n+1+4)+3
      rw [hp]
      have he' : 4*(2:Int)^(n+2) = (2:Int)^(n+4) := by
        rw [← he]
        ac_rfl
      rw [he']
      omega

theorem highThenFar_num_two (n:Nat) :
    terminalNumerator 2 (highThenFar n) = 5*(2:Int)^(n+2)+3 := by
  induction n with
  | zero => decide
  | succ n ih =>
      rw [highThenFar, terminalNumerator_high, ih, highThenFar_shift]
      have hp : (2:Int)^(n+1+2) = 2*(2:Int)^(n+2) := by
        rw [show n+1+2=(n+2)+1 by omega, Int.pow_succ]
        ac_rfl
      rw [hp]
      omega

private theorem pow2_mod7_trichotomy (n:Nat) :
    2^n % 7 = 1 ∨ 2^n % 7 = 2 ∨ 2^n % 7 = 4 := by
  induction n with
  | zero => left; decide
  | succ n ih =>
      rw [Nat.pow_succ, Nat.mul_mod]
      rcases ih with h1 | h2 | h4
      · right; left; omega
      · right; right; omega
      · left; omega

/-- An exact terminal inverse word consisting of n High letters followed by a
    single Far letter can never end at an anchor whose second counter is 2. -/
theorem highThenFar_anchor_two_impossible
    {n d R : Nat}
    (hp : FormalInversePath (d:Int) (highThenFar n) (R:Int) 2) : False := by
  have hc := formal_inverse_terminal_candidate hp
  rw [highThenFar_denom, highThenFar_num_two] at hc
  have hm := congrArg (fun z : Int => z % 7) hc
  have hpow := pow2_mod7_trichotomy (n+2)
  rcases hpow with h1 | h2 | h4
  · have hpz : ((2:Int)^(n+2)) % 7 = 1 := by exact_mod_cast h1
    omega
  · have hpz : ((2:Int)^(n+2)) % 7 = 2 := by exact_mod_cast h2
    omega
  · have hpz : ((2:Int)^(n+2)) % 7 = 4 := by exact_mod_cast h4
    omega

private theorem pow2_mod7_phase (n:Nat) :
    (n%3=0 ∧ 2^n%7=1) ∨
    (n%3=1 ∧ 2^n%7=2) ∨
    (n%3=2 ∧ 2^n%7=4) := by
  induction n with
  | zero => left; decide
  | succ n ih =>
      rw [Nat.pow_succ, Nat.mul_mod]
      rcases ih with h0 | h1 | h2
      · right; left
        constructor <;> omega
      · right; right
        constructor <;> omega
      · left
        constructor <;> omega

/-- In the c=1 single-F family, integrality forces the number of leading High
    letters to be 1 modulo 3. -/
theorem highThenFar_anchor_one_mod3
    {n d R : Nat}
    (hp : FormalInversePath (d:Int) (highThenFar n) (R:Int) 1) :
    n % 3 = 1 := by
  have hc := formal_inverse_terminal_candidate hp
  rw [highThenFar_denom, highThenFar_num_one] at hc
  have hm := congrArg (fun z : Int => z % 7) hc
  have phase := pow2_mod7_phase (n+4)
  rcases phase with h0 | h1 | h2
  · have hpz : ((2:Int)^(n+4)) % 7 = 1 := by exact_mod_cast h0.2
    omega
  · have hpz : ((2:Int)^(n+4)) % 7 = 2 := by exact_mod_cast h1.2
    omega
  · omega

#print axioms terminalNumerator_high
#print axioms highThenFar_num_one
#print axioms highThenFar_num_two
#print axioms highThenFar_anchor_two_impossible
#print axioms highThenFar_anchor_one_mod3


private theorem pow2_mod3_phase (n:Nat) :
    (n%2=0 ∧ 2^n%3=1) ∨ (n%2=1 ∧ 2^n%3=2) := by
  induction n with
  | zero => left; decide
  | succ n ih =>
      rw [Nat.pow_succ, Nat.mul_mod]
      rcases ih with h0 | h1
      · right; constructor <;> omega
      · left; constructor <;> omega

/-- A single-F terminal inverse word compatible with the authentic root
    terminal phase d == 1 (mod 6) must come from c=1 and have n == 4 (mod 6).
    This is a root-phase arithmetic statement; the last-anchor decomposition
    supplies exactly these hypotheses for an authentic single-F suffix. -/
theorem highThenFar_root_phase
    {n d R c : Nat}
    (hc : c=1 ∨ c=2)
    (hd : d%6=1)
    (hp : FormalInversePath (d:Int) (highThenFar n) (R:Int) (c:Int)) :
    c=1 ∧ n%6=4 := by
  have hc1 : c=1 := by
    rcases hc with rfl | rfl
    · rfl
    · exact False.elim (highThenFar_anchor_two_impossible hp)
  subst c
  have hn3 := highThenFar_anchor_one_mod3 hp
  have heq := formal_inverse_terminal_candidate hp
  rw [highThenFar_denom, highThenFar_num_one] at heq
  have hm := congrArg (fun z : Int => z % 3) heq
  have hphase := pow2_mod3_phase (n+4)
  have hn2 : n%2=0 := by
    rcases hphase with h0 | h1
    · omega
    · have hpz : ((2:Int)^(n+4)) % 3 = 2 := by exact_mod_cast h1.2
      omega
  constructor
  · rfl
  · omega

#print axioms highThenFar_root_phase

end BB6.Agent31F321Density
