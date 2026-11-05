import Lean.Elab.Tactic.Omega

namespace BB429GateArithmetic
set_option maxHeartbeats 50000000
set_option maxRecDepth 32000

def old38 (u : Nat) : Prop :=
  (u%64=9 ∨ u%128=81 ∨ u%64=53 ∨ (u%128=125 ∧ u%1024≠125)) ∧
  u%1024≠253 ∧ u%1024≠381 ∧ u%1024≠509 ∧
  u%512≠393 ∧ u%512≠265 ∧ u%1024≠137 ∧ u%1024≠521

def newForbidden (u : Nat) : Prop :=
  u%512≠81 ∧ u%512≠309 ∧ u%512≠329 ∧
  u%512≠373 ∧ u%512≠457 ∧ u%512≠501 ∧
  u%1024≠181 ∧ u%1024≠437 ∧ u%1024≠585 ∧
  u%1024≠629 ∧ u%1024≠693 ∧ u%1024≠713 ∧
  u%1024≠757 ∧ u%1024≠977

def gate18 (u : Nat) : Prop :=
  u%1024=9 ∨ u%1024=53 ∨ u%1024=73 ∨
  u%1024=117 ∨ u%1024=201 ∨ u%1024=209 ∨
  u%1024=245 ∨ u%1024=337 ∨ u%1024=465 ∨
  u%1024=565 ∨ u%1024=637 ∨ u%1024=649 ∨
  u%1024=721 ∨ u%1024=765 ∨ u%1024=849 ∨
  u%1024=893 ∨ u%1024=949 ∨ u%1024=1021

theorem old38_and_fresh_iff_gate18 (u : Nat) :
    old38 u ∧ newForbidden u ↔ gate18 u := by
  simp only [old38, newForbidden, gate18]
  omega

#print axioms old38_and_fresh_iff_gate18
end BB429GateArithmetic
