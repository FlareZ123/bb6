import TerminalWordOneFarGeneral
import Lean.Elab.Tactic.Omega

namespace BB6.Agent31F321Density

/-- Dyadic shift added by compiling a prefix in front of an already compiled
    inverse suffix. -/
def wordShift : List InverseLetter → Nat
  | [] => 0
  | .high :: p => wordShift p + 1
  | .far :: p => wordShift p + 2

theorem compile_append_shift (p w : List InverseLetter) :
    (compile (p ++ w)).shift = (compile w).shift + wordShift p := by
  induction p with
  | nil => simp [wordShift]
  | cons x ps ih =>
      cases x <;> simp [wordShift, compile, advance, ih] <;> omega

/-- Prepending an arbitrary H/F prefix changes the exact terminal denominator
    only by a multiple of the suffix dyadic scale. -/
theorem terminalDenom_append_factor (p w : List InverseLetter) :
    ∃ k : Nat,
      terminalDenom (p ++ w) =
        terminalDenom w + 2^(compile w).shift * k := by
  induction p with
  | nil => exact ⟨0, by simp⟩
  | cons x ps ih =>
      rcases ih with ⟨k,hk⟩
      cases x with
      | high =>
          exact ⟨k, by simpa [terminalDenom] using hk⟩
      | far =>
          let t : Nat := wordShift ps
          refine ⟨k + 3*2^(t+1), ?_⟩
          simp only [List.cons_append, terminalDenom]
          rw [hk, compile_append_shift]
          have hp : 2^((compile w).shift + t + 1) =
              2^(compile w).shift * 2^(t+1) := by
            rw [show (compile w).shift+t+1=(compile w).shift+(t+1) by omega,
                Nat.pow_add]
          rw [hp]
          have h3 : 3 * (2^(compile w).shift * 2^(t+1)) =
              2^(compile w).shift * (3 * 2^(t+1)) := by ac_rfl
          rw [h3, Nat.mul_add]
          ac_rfl

/-- The signed terminal numerator has the same prefix-stability property. -/
theorem terminalNumerator_append_factor (c : Nat)
    (p w : List InverseLetter) :
    ∃ k : Int,
      terminalNumerator c (p ++ w) =
        terminalNumerator c w + (2:Int)^(compile w).shift * k := by
  induction p with
  | nil => exact ⟨0, by simp⟩
  | cons x ps ih =>
      rcases ih with ⟨k,hk⟩
      cases x with
      | high =>
          let t : Nat := wordShift ps
          refine ⟨k + ((c:Int)+3)*(2:Int)^t, ?_⟩
          simp only [List.cons_append]
          rw [terminalNumerator_high, hk, compile_append_shift]
          have hp : (2:Int)^((compile w).shift+t) =
              (2:Int)^(compile w).shift * (2:Int)^t := by
            rw [Int.pow_add]
          rw [hp]
          have hscale : ((c:Int)+3) *
              ((2:Int)^(compile w).shift * (2:Int)^t) =
              (2:Int)^(compile w).shift * (((c:Int)+3)*(2:Int)^t) := by ac_rfl
          rw [hscale, Int.mul_add]
          ac_rfl
      | far =>
          let t : Nat := wordShift ps
          let S : Nat := (compile (ps ++ w)).sumDecrease
          refine ⟨k + 3*((c:Int)+(S:Int)+5)*(2:Int)^t, ?_⟩
          simp only [List.cons_append]
          rw [terminalNumerator_far, hk, compile_append_shift]
          change terminalNumerator c w + (2:Int)^(compile w).shift*k +
              3*((c:Int)+(S:Int)+5) *
                (2:Int)^((compile w).shift+t) = _
          have hp : (2:Int)^((compile w).shift+t) =
              (2:Int)^(compile w).shift * (2:Int)^t := by
            rw [Int.pow_add]
          rw [hp]
          have hscale : 3*((c:Int)+(S:Int)+5) *
              ((2:Int)^(compile w).shift * (2:Int)^t) =
              (2:Int)^(compile w).shift *
                (3*((c:Int)+(S:Int)+5)*(2:Int)^t) := by ac_rfl
          rw [hscale]
          have hdist : (2:Int)^(compile w).shift *
              (k + 3*((c:Int)+(S:Int)+5)*(2:Int)^t) =
              (2:Int)^(compile w).shift*k +
                (2:Int)^(compile w).shift *
                  (3*((c:Int)+(S:Int)+5)*(2:Int)^t) := by
            exact Int.mul_add _ _ _
          rw [hdist]
          ac_rfl

/-- Closed denominator form for a last-Far suffix with b trailing Highs. -/
theorem farPureHigh_denom (b : Nat) :
    terminalDenom (.far :: pureHigh b) = 6*2^b+1 := by
  simpa [oneFarWord, prependHigh] using oneFarWord_denom 0 b

/-- Closed numerator form for the same suffix, written as divisibility of N+3. -/
theorem farPureHigh_num_plus_three (c b : Nat) :
    terminalNumerator c (.far :: pureHigh b) + 3 =
      (2:Int)^b * (4*((c:Int)+3) + 3*((b:Int)+2)) := by
  have h := oneFarWord_num_balance c 0 b
  simp only [oneFarWord, prependHigh, Nat.zero_add] at h
  have hp : (2:Int)^(b+2) = (2:Int)^b * 4 := by
    rw [Int.pow_add]
    simp
  rw [hp] at h
  calc
    terminalNumerator c (.far :: pureHigh b) + 3
        = ((c:Int)+3)*((2:Int)^b*4) + 3*((b:Int)+2)*(2:Int)^b := h
    _ = (2:Int)^b * (4*((c:Int)+3) + 3*((b:Int)+2)) := by
      have h1 : ((c:Int)+3)*((2:Int)^b*4) =
          (2:Int)^b*(4*((c:Int)+3)) := by ac_rfl
      have h2 : 3*((b:Int)+2)*(2:Int)^b =
          (2:Int)^b*(3*((b:Int)+2)) := by ac_rfl
      rw [h1,h2]
      exact (Int.mul_add _ _ _).symm

/-- Strong general last-Far theorem. Earlier inverse letters are arbitrary:
    if the final Far is followed by b Highs before the terminal gate, then
    d+3 has a factor 2^b, and the residual quotient has parity b. -/
theorem lastFar_near_minus_three_parity
    {p : List InverseLetter} {b d R c : Nat}
    (hp : FormalInversePath (d:Int)
      (p ++ (.far :: pureHigh b)) (R:Int) (c:Int)) :
    ∃ z : Int, (d:Int)+3 = (2:Int)^b * z ∧
      z % 2 = (b:Int) % 2 := by
  let w : List InverseLetter := .far :: pureHigh b
  have hdenFac := terminalDenom_append_factor p w
  have hnumFac := terminalNumerator_append_factor c p w
  rcases hdenFac with ⟨kd,hdenFac⟩
  rcases hnumFac with ⟨kn,hnumFac⟩
  have hshift : (compile w).shift = b+2 := by
    dsimp [w]
    simp [compile,advance,pureHigh_shift]
  have hdenTail := farPureHigh_denom b
  have hnumTail := farPureHigh_num_plus_three c b
  have heq := formal_inverse_terminal_candidate hp
  dsimp [w] at hdenFac hnumFac hshift hdenTail hnumTail
  rw [hshift] at hdenFac hnumFac
  rw [hdenTail] at hdenFac
  have hpowNat : 2^(b+2) = 2^b * 4 := by
    rw [Nat.pow_add]
  rw [hpowNat] at hdenFac
  have hpowInt : (2:Int)^(b+2) = (2:Int)^b * 4 := by
    rw [Int.pow_add]
    have h22 : (2:Int)^2 = 4 := by decide
    rw [h22]
  rw [hpowInt] at hnumFac
  have hdenCast : (terminalDenom (p ++ (.far :: pureHigh b)) : Int) =
      (6*(2:Int)^b+1) + ((2:Int)^b*4)*(kd:Int) := by
    exact_mod_cast hdenFac
  have hnumPlus :
      terminalNumerator c (p ++ (.far :: pureHigh b)) + 3 =
      (2:Int)^b *
        (4*((c:Int)+3)+3*((b:Int)+2)+4*kn) := by
    let P : Int := (2:Int)^b
    let A : Int := 4*((c:Int)+3)+3*((b:Int)+2)
    have htail : terminalNumerator c (.far :: pureHigh b) + 3 = P*A := by
      simpa [P,A] using hnumTail
    have hkn : ((2:Int)^b*4)*kn = P*(4*kn) := by
      dsimp [P]
      ac_rfl
    rw [hnumFac, hkn]
    calc
      terminalNumerator c (.far :: pureHigh b) + P*(4*kn) + 3
          = (terminalNumerator c (.far :: pureHigh b)+3) + P*(4*kn) := by omega
      _ = P*A + P*(4*kn) := by rw [htail]
      _ = P*(A + 4*kn) := (Int.mul_add _ _ _).symm
      _ = (2:Int)^b *
          (4*((c:Int)+3)+3*((b:Int)+2)+4*kn) := by rfl
  rw [hdenCast] at heq
  let Q : Int := 6 + 4*(kd:Int)
  let K : Int := 4*((c:Int)+3)+3*((b:Int)+2)+4*kn
  have hdenQ : (6*(2:Int)^b+1) + ((2:Int)^b*4)*(kd:Int) =
      1 + (2:Int)^b*Q := by
    dsimp [Q]
    rw [Int.mul_add]
    have h6 : (2:Int)^b * 6 = 6*(2:Int)^b := by ac_rfl
    have h4 : (2:Int)^b * (4*(kd:Int)) =
        ((2:Int)^b*4)*(kd:Int) := by ac_rfl
    rw [h6,h4]
    omega
  have hnumK : terminalNumerator c (p ++ (.far :: pureHigh b)) + 3 =
      (2:Int)^b*K := by simpa [K] using hnumPlus
  rw [hdenQ] at heq
  refine ⟨K - Q*(d:Int), ?_, ?_⟩
  · have h1 : (1 + (2:Int)^b*Q)*(d:Int) =
        (d:Int) + (2:Int)^b*(Q*(d:Int)) := by
      rw [Int.add_mul]
      ac_rfl
    rw [h1] at heq
    rw [Int.mul_sub]
    have hPQ : (2:Int)^b*(Q*(d:Int)) =
        ((2:Int)^b*Q)*(d:Int) := by ac_rfl
    omega
  · have hKmod : K % 2 = (b:Int) % 2 := by
      dsimp [K]
      omega
    have hQmod : Q % 2 = 0 := by
      dsimp [Q]
      omega
    have hQdmod : (Q*(d:Int)) % 2 = 0 := by
      rw [Int.mul_emod, hQmod]
      simp
    rw [Int.sub_emod, hKmod, hQdmod]
    omega

/-- Divisibility-only corollary used by the reset-tail analysis. -/
theorem lastFar_near_minus_three
    {p : List InverseLetter} {b d R c : Nat}
    (hp : FormalInversePath (d:Int)
      (p ++ (.far :: pureHigh b)) (R:Int) (c:Int)) :
    ∃ z : Int, (d:Int)+3 = (2:Int)^b * z := by
  rcases lastFar_near_minus_three_parity hp with ⟨z,hz,_⟩
  exact ⟨z,hz⟩

#print axioms compile_append_shift
#print axioms terminalDenom_append_factor
#print axioms terminalNumerator_append_factor
#print axioms lastFar_near_minus_three_parity
#print axioms lastFar_near_minus_three
end BB6.Agent31F321Density
