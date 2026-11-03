import Row109Safe

namespace BB6.Row109Locality

-- Original source RightC/RightE (H0/H1) crossing D0/D1.
-- Source rule IDs 15,16,17,18 in the 67-clause textual grammar.
-- Output 'S0' is the pre-normalization representation of output D0;
-- output D1 is already normalized. Both source cases S0 < -> < D0
-- are separately proved in the 65-rule suite.
def gateRule (head digit : Bool) : Certificate :=
  match head, digit with
  | false, false => rule_14
  | true,  false => rule_15
  | false, true  => rule_16
  | true,  true  => rule_17

theorem gate_input_output (head digit : Bool) :
    (gateRule head digit).initialState = (if head then 4 else 2) ∧
    (gateRule head digit).finalState = (if head ^^ digit then 2 else 4) ∧
    (gateRule head digit).afterBits = (if head ^^ digit then 31 else 55) ∧
    (gateRule head digit).initialHead = 2 ∧
    (gateRule head digit).finalHead = 6 ∧
    (gateRule head digit).lo = 0 ∧
    (gateRule head digit).hi = 5 := by
  cases head <;> cases digit <;> decide

theorem gate_valid (head digit : Bool) :
    accepted (gateRule head digit) = true := by
  cases head <;> cases digit <;> decide

theorem gate_primitive_sound (head digit : Bool)
    (t : Int → Bool)
    (ht : ∀ p, InWindow (gateRule head digit).lo (gateRule head digit).hi p →
      t p = wordTape (gateRule head digit).beforeBits p) :
    let r := gateRule head digit
    let out := run r.steps {st := r.initialState, h := r.initialHead, tape := t}
    out.st = r.finalState ∧ out.h = r.finalHead ∧
    ∀ p, out.tape p =
      (if r.lo ≤ p ∧ p ≤ r.hi then wordTape r.afterBits (p - r.afterShift)
      else t p) := by
  exact accepted_sound (gateRule head digit) (gate_valid head digit) t ht

theorem gate_never_halts (head digit : Bool)
    (t : Int → Bool)
    (ht : ∀ p, InWindow (gateRule head digit).lo (gateRule head digit).hi p →
      t p = wordTape (gateRule head digit).beforeBits p)
    (k : Nat) (hk : k ≤ (gateRule head digit).steps) :
    (run k {st := (gateRule head digit).initialState,
            h := (gateRule head digit).initialHead, tape := t}).st ≠ 6 := by
  have hf : (gateRule head digit).finalState < 6 := by
    cases head <;> cases digit <;> decide
  exact accepted_no_halt (gateRule head digit) (gate_valid head digit) hf t ht k hk

#print axioms gate_primitive_sound
#print axioms gate_never_halts
end BB6.Row109Locality
