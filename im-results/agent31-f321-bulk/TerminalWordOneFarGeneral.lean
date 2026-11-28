import TerminalWordOneFar
import Lean.Elab.Tactic.Omega

namespace BB6.Agent31F321Density

theorem terminalNumerator_far (c:Nat) (w:List InverseLetter) :
    terminalNumerator c (.far::w) =
      terminalNumerator c w +
        3 * ((c:Int) + (compile w).sumDecrease + 5) *
          (2:Int)^(compile w).shift := by
  unfold terminalNumerator
  simp only [compile, advance]
  have hp : (2:Int)^((compile w).shift+2) =
      4 * (2:Int)^(compile w).shift := by
    rw [Int.pow_add]
    simp [Int.mul_comm]
  rw [hp]
  let P : Int := (2:Int)^(compile w).shift
  let S : Int := (compile w).sumDecrease
  let V : Int := (compile w).v
  change V - 6*P + (4*P)*(S+6+(c:Int)-1) =
    (V + P*(S+(c:Int)-1)) + 3*((c:Int)+S+5)*P
  have h4PS : (4*P)*S = 4*(P*S) := by ac_rfl
  have h4Pc : (4*P)*(c:Int) = 4*(P*(c:Int)) := by ac_rfl
  have h3cP : 3*((c:Int)+S+5)*P =
      3*(P*(c:Int)) + 3*(P*S) + 15*P := by
    simp only [Int.mul_add, Int.add_mul]
    have hc : 3*(c:Int)*P = 3*(P*(c:Int)) := by ac_rfl
    have hs : 3*S*P = 3*(P*S) := by ac_rfl
    rw [hc,hs]
    omega
  have hPS : P*(S+(c:Int)-1)=P*S+P*(c:Int)-P := by
    simp only [Int.mul_sub, Int.mul_add, Int.mul_one]
  rw [h3cP,hPS]
  simp only [Int.mul_add, Int.mul_sub] at *
  rw [h4PS,h4Pc]
  omega

def prependHigh : Nat → List InverseLetter → List InverseLetter
  | 0, w => w
  | n+1, w => .high :: prependHigh n w

def pureHigh (n:Nat) : List InverseLetter := prependHigh n []

def oneFarWord (a b:Nat) : List InverseLetter :=
  prependHigh a (.far :: pureHigh b)

theorem prependHigh_shift (n:Nat) (w:List InverseLetter) :
    (compile (prependHigh n w)).shift = (compile w).shift+n := by
  induction n with
  | zero => simp [prependHigh]
  | succ n ih =>
      simp [prependHigh,compile,advance,ih]
      omega

theorem prependHigh_sumDecrease (n:Nat) (w:List InverseLetter) :
    (compile (prependHigh n w)).sumDecrease =
      (compile w).sumDecrease+n := by
  induction n with
  | zero => simp [prependHigh]
  | succ n ih =>
      simp [prependHigh,compile,advance,ih]
      omega

theorem prependHigh_denom (n:Nat) (w:List InverseLetter) :
    terminalDenom (prependHigh n w) = terminalDenom w := by
  induction n with
  | zero => simp [prependHigh]
  | succ n ih => simpa [prependHigh,terminalDenom] using ih

theorem prependHigh_num_balance (c n:Nat) (w:List InverseLetter) :
    terminalNumerator c (prependHigh n w) +
        ((c:Int)+3)*(2:Int)^(compile w).shift =
      terminalNumerator c w +
        ((c:Int)+3)*(2:Int)^((compile w).shift+n) := by
  induction n with
  | zero => simp [prependHigh]
  | succ n ih =>
      rw [prependHigh, terminalNumerator_high, prependHigh_shift]
      have hp : (2:Int)^((compile w).shift+n+1) =
          2*(2:Int)^((compile w).shift+n) := by
        rw [Int.pow_succ]
        ac_rfl
      rw [show (compile w).shift+(n+1) = (compile w).shift+n+1 by omega, hp]
      have hmul : ((c:Int)+3) * (2 * (2:Int)^((compile w).shift+n)) =
          2 * (((c:Int)+3) * (2:Int)^((compile w).shift+n)) := by ac_rfl
      rw [hmul]
      omega

theorem pureHigh_shift (n:Nat) : (compile (pureHigh n)).shift=n := by
  simpa [pureHigh,compile,initial] using prependHigh_shift n ([]:List InverseLetter)

theorem pureHigh_sumDecrease (n:Nat) :
    (compile (pureHigh n)).sumDecrease=n := by
  simpa [pureHigh,compile,initial] using prependHigh_sumDecrease n ([]:List InverseLetter)

theorem pureHigh_denom (n:Nat) : terminalDenom (pureHigh n)=1 := by
  simpa [pureHigh,terminalDenom] using prependHigh_denom n ([]:List InverseLetter)

theorem oneFarWord_denom (a b:Nat) :
    terminalDenom (oneFarWord a b) = 6*2^b+1 := by
  rw [oneFarWord, prependHigh_denom]
  simp only [terminalDenom]
  rw [pureHigh_denom, pureHigh_shift]
  rw [Nat.pow_succ]
  omega

theorem oneFarWord_num_balance (c a b:Nat) :
    terminalNumerator c (oneFarWord a b) + 3 =
      ((c:Int)+3)*(2:Int)^(a+b+2) +
      3*((b:Int)+2)*(2:Int)^b := by
  unfold oneFarWord
  have hpre := prependHigh_num_balance c a (.far :: pureHigh b)
  have htail := prependHigh_num_balance c b ([]:List InverseLetter)
  have hs := pureHigh_shift b
  have hS := pureHigh_sumDecrease b
  have hfar := terminalNumerator_far c (pureHigh b)
  have hnil : terminalNumerator c [] = (c:Int) := by
    simp [terminalNumerator,compile,initial]
    omega
  simp only [compile, initial, Nat.zero_add, Int.pow_zero, Int.mul_one] at htail
  rw [hnil] at htail
  change terminalNumerator c (pureHigh b) + ((c:Int)+3) =
      (c:Int) + ((c:Int)+3)*(2:Int)^b at htail
  rw [hs,hS] at hfar
  simp only [compile, advance] at hpre
  rw [hs] at hpre
  have hp : (2:Int)^(b+2+a) = (2:Int)^(a+b+2) := by
    congr 1 <;> omega
  rw [hp] at hpre
  have htail' : terminalNumerator c (pureHigh b) =
      ((c:Int)+3)*(2:Int)^b - 3 := by
    omega
  rw [htail'] at hfar
  have hfar' : terminalNumerator c (.far :: pureHigh b) =
      ((c:Int)+3)*(2:Int)^b - 3 +
      3*((c:Int)+(b:Int)+5)*(2:Int)^b := by
    exact hfar
  rw [hfar'] at hpre
  have hpow2 : (2:Int)^(b+2) = 4*(2:Int)^b := by
    rw [Int.pow_add]
    simp [Int.mul_comm]
  rw [hpow2] at hpre
  have hab : ((c:Int)+3)*(2:Int)^b +
        3*((c:Int)+(b:Int)+5)*(2:Int)^b =
      4*((c:Int)+3)*(2:Int)^b + 3*((b:Int)+2)*(2:Int)^b := by
    let P : Int := (2:Int)^b
    change ((c:Int)+3)*P + 3*((c:Int)+(b:Int)+5)*P =
      4*((c:Int)+3)*P + 3*((b:Int)+2)*P
    have hc3 : 3*(c:Int)*P = 3*((c:Int)*P) := by ac_rfl
    have hb3 : 3*(b:Int)*P = 3*((b:Int)*P) := by ac_rfl
    have h4c : 4*(c:Int)*P = 4*((c:Int)*P) := by ac_rfl
    simp only [Int.add_mul, Int.mul_add]
    rw [hc3,hb3,h4c]
    omega
  have hC4 : ((c:Int)+3) * (4*(2:Int)^b) =
      4*((c:Int)+3)*(2:Int)^b := by ac_rfl
  rw [hC4] at hpre
  omega

theorem oneFarWord_near_minus_three
    {a b d R c:Nat}
    (hp : FormalInversePath (d:Int) (oneFarWord a b) (R:Int) (c:Int)) :
    ∃ z:Int, (d:Int)+3 = (2:Int)^b * z := by
  have heq := formal_inverse_terminal_candidate hp
  have hnum := oneFarWord_num_balance c a b
  have hden : (terminalDenom (oneFarWord a b):Int) =
      6*(2:Int)^b+1 := by
    rw [oneFarWord_denom]
    rw [Int.natCast_add, Int.natCast_mul, Int.natCast_pow]
    rfl
  rw [hden] at heq
  have hpow : (2:Int)^(a+b+2) = (2:Int)^b * (2:Int)^(a+2) := by
    rw [show a+b+2=b+(a+2) by omega, Int.pow_add]
  rw [hpow] at hnum
  let K : Int := ((c:Int)+3)*(2:Int)^(a+2) + 3*((b:Int)+2)
  have hfactor :
      ((c:Int)+3)*((2:Int)^b*(2:Int)^(a+2)) +
          3*((b:Int)+2)*(2:Int)^b = (2:Int)^b*K := by
    dsimp [K]
    have hleft : ((c:Int)+3)*((2:Int)^b*(2:Int)^(a+2)) =
        (2:Int)^b * (((c:Int)+3)*(2:Int)^(a+2)) := by ac_rfl
    have hright : 3*((b:Int)+2)*(2:Int)^b =
        (2:Int)^b * (3*((b:Int)+2)) := by ac_rfl
    rw [hleft,hright]
    exact (Int.mul_add ((2:Int)^b) (((c:Int)+3)*(2:Int)^(a+2)) (3*((b:Int)+2))).symm
  rw [hfactor] at hnum
  refine ⟨K - 6*(d:Int), ?_⟩
  have h6 : (6*(2:Int)^b)*(d:Int) = 6*((2:Int)^b*(d:Int)) := by ac_rfl
  have hp6 : (2:Int)^b*(6*(d:Int)) = 6*((2:Int)^b*(d:Int)) := by ac_rfl
  simp only [Int.add_mul] at heq
  rw [h6] at heq
  rw [Int.mul_sub, hp6]
  omega

#print axioms terminalNumerator_far
#print axioms oneFarWord_denom
#print axioms oneFarWord_num_balance
#print axioms oneFarWord_near_minus_three
end BB6.Agent31F321Density
