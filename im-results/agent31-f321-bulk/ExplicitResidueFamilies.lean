import FiniteResidueCheck
import Lean.Elab.Tactic.Omega

namespace BB6.Agent31F321Density

theorem pass_seven_mod8 (d:Nat) (h:d%8=7) : residuePass 2 d = true := by
  simp [residuePass, words, compile, advance, initial]
  omega

theorem pass_even (d:Nat) (h:d%2=0) : residuePass 1 d=true := by
  simp [residuePass, words, compile, advance, initial]
  omega

/-- Odd first/even second output has no source-map predecessor. -/
theorem no_incoming_odd_even {a b A D:Nat}
    (h:CounterMove a b A D) (hA:A%2=1) (hD:D%2=0) : False := by
  cases h with
  | high hxy => omega
  | equal => omega
  | far h1 h2 => omega
  | middleEven h1 h2 hp => omega
  | middleOdd h1 h2 hp => omega

/-- All even terminal indices are unreachable, including small ones. -/
theorem even_gate_never (d:Nat) (hd:d%2=0) :
    ∀ m, ¬CounterReach 1 1 m (d+1) d := by
  intro m hm
  cases hm with
  | step hr h =>
    have hodd:(d+1)%2=1 := by omega
    exact no_incoming_odd_even h hodd hd

theorem seven_mod8_high_never (d:Nat) (hd:d%8=7)
    (hD:21≤d) : ∀ m, ¬CounterReach 1 1 m (d+1) d := by
  have hb:6*2^2≤d+3 := by omega
  exact no_halting_gate_after_decide 2 d hb (pass_seven_mod8 d hd)

theorem no_incoming_even0_even {a b A D:Nat}
    (h:CounterMove a b A D) (hA:A%4=0) (hD:D%2=0):False := by
  cases h with
  | high hxy => omega
  | equal => omega
  | far h1 h2 => omega
  | middleEven h1 h2 hp => omega
  | middleOdd h1 h2 hp => omega

/-- All d≡7 (mod8) terminal gates have a bounded, dead inverse ancestry. -/
theorem seven_mod8_gate_never (d:Nat) (hd:d%8=7) :
    ∀ m, ¬CounterReach 1 1 m (d+1) d := by
  intro m hr
  have hLarge:3≤d := by omega
  cases hr with
  | step hr hm =>
      rcases large_second_only_high_far hm hLarge with hh|hf
      · have hAE:(d+1)%4=0 := by omega
        cases hr with
        | nil => omega
        | step hr2 hm2 =>
            exact no_incoming_even0_even hm2 (by omega) (by omega)
      · omega

theorem no_incoming_two_one {a b A D:Nat}
    (h:CounterMove a b A D) (hA:A=2) (hD:D=1):False := by
  cases h with
  | high hxy => omega
  | equal => omega
  | far h1 h2 => omega
  | middleEven h1 h2 hp => omega
  | middleOdd h1 h2 hp => omega

/-- All d≡1 (mod8) terminal gates have a bounded, dead inverse ancestry. -/
theorem one_mod8_gate_never (d:Nat) (hd:d%8=1) :
    ∀ m, ¬CounterReach 1 1 m (d+1) d := by
  by_cases hd1:d=1
  · subst d
    intro m hr
    cases hr with
    | step hr hm => exact no_incoming_two_one hm rfl rfl
  · have hLarge:9≤d := by omega
    intro m hr
    cases hr with
    | step hr hm =>
        have hdG:3≤d := by omega
        rcases large_second_only_high_far hm hdG with hh|hf
        · cases hr with
          | nil => omega
          | step hr2 hm2 =>
              rcases large_second_only_high_far hm2 (by omega) with hh2|hf2
              · cases hr2 with
                | nil => omega
                | step hr3 hm3 =>
                    exact no_incoming_odd_even hm3 (by omega) (by omega)
              · omega
        · cases hr with
          | nil => omega
          | step hr2 hm2 =>
              exact no_incoming_odd_even hm2 (by omega) (by omega)

#print axioms even_gate_never
#print axioms seven_mod8_gate_never
#print axioms one_mod8_gate_never
end BB6.Agent31F321Density
