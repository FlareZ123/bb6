import ExactEndpoint
import CarryCert
import Carry350

namespace BB6.Agent43CarryCert
open BB6.Agent28FullPrefix
open BB6.Agent28 BB6.Agent1Quarter BB6.Agent1UpperTail BB6.Agent47P1
open BB6.Agent43LastResetStrength

theorem states_eq (Q j : Nat) (cs : List Nat) (K : Nat) :
    states Q j cs K = fullCarryStates Q j cs K := by
  induction K generalizing j cs with
  | zero => rfl
  | succ k ih =>
      exact ih (j+1) (step Q j cs)

theorem cert_interface (Q K : Nat) (h : Safe Q 0 [1] K []) :
    fullCarryStates Q 0 [1] K = [] ∧ ∀ i<K, 2 ∉ fullCarryStates Q 0 [1] i := by
  simpa only [Safe, states_eq] using h

theorem no_right_five_of_cert (n b m z K : Nat) (hn : 14≤n)
    (hK : 0<K) (h : Safe (7*2^n-(n+3)) 0 [1] K []) :
    ¬ CountCone (14*2^n-2*n-16) 3 b 5 m z := by
  obtain ⟨he, hno⟩ := cert_interface _ _ h
  exact source_no_right_five_of_no_two n b m z K hn hK he hno

theorem no_right_five_30 (b m z : Nat) :
    ¬ CountCone (14*2^30-2*30-16) 3 b 5 m z :=
  no_right_five_of_cert 30 b m z 82 (by decide) (by decide) safe30

theorem no_right_five_350 (b m z : Nat) :
    ¬ CountCone (14*2^350-2*350-16) 3 b 5 m z :=
  no_right_five_of_cert 350 b m z 586 (by decide) (by decide) safe350

#print axioms cert_interface
#print axioms no_right_five_of_cert
#print axioms no_right_five_30
#print axioms no_right_five_350
end BB6.Agent43CarryCert
