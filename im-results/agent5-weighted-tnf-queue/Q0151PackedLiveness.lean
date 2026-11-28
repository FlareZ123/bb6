import Q0151MacroSteps

set_option maxHeartbeats 0
namespace BB6.Agent5Q0151PackedLiveness
open BB6Coverage BB6Coverage.Agent31Pump BB6Coverage.Agent13PackedZipper
open BB6.Agent5PackedSweep BB6.Agent5Q0151SourceMacro

/-!
A nonhalting soundness interface tailored to the actual q0-151 partial
machine. Any inductive region of genuine packed boundary configurations,
with one certified positive-length return from EVERY member, proves
nonhalting of all completions. The region may be defined using a finite
stack/grammar certificate; proving its closure is the remaining obligation.
-/

theorem prefix_run {a b : Nat} {x z : P} (hab : a ≤ b)
    (h : runP p b x = some z) : runP p a x ≠ none := by
  intro hn
  rw [show b = a + (b-a) by omega,runP_add,hn] at h
  contradiction

theorem live_of_region (Region : P → Prop)
    (entry : Nat) (base : P) (hentry : runP p entry startP = some base)
    (hbase : Region base)
    (progress : ∀ x, Region x → ∃ y, Region y ∧ Goes x y)
    (n : Nat) : runP p n startP ≠ none := by
  have extend : ∀ j, ∃ k y, j ≤ k ∧ Region y ∧ runP p k base = some y := by
    intro j
    induction j with
    | zero => exact ⟨0,base,by omega,hbase,rfl⟩
    | succ j ih =>
      obtain ⟨k,y,hk,hy,hky⟩ := ih
      obtain ⟨z,hz,⟨t,ht,hstep⟩⟩ := progress y hy
      exact ⟨k+t,z,by omega,hz,joinP hky hstep⟩
  obtain ⟨k,y,hk,_,hky⟩ := extend n
  exact prefix_run (show n ≤ entry+k by omega) (joinP hentry hky)

theorem never_of_region (Region : P → Prop)
    (entry : Nat) (base : P) (hentry : runP p entry startP = some base)
    (hbase : Region base)
    (progress : ∀ x, Region x → ∃ y, Region y ∧ Goes x y)
    (m : Machine) (hm : compatible p m) : NeverHalts m := by
  intro n
  have h := live_of_region Region entry base hentry hbase progress n
  have hencode := encode_run p n BB6Coverage.Agent31Pump.start
  rw [show encode BB6Coverage.Agent31Pump.start = startP from rfl] at hencode
  cases hz : BB6Coverage.Agent50Zipper.zrun p n BB6Coverage.Agent31Pump.start with
  | none => simp [hz] at hencode; exact False.elim (h hencode.symm)
  | some z =>
    have hs := BB6Coverage.Agent50Zipper.zrun_sound p m hm n _ _ hz
    rw [BB6Coverage.Agent31Pump.start_embed] at hs
    change (run m n blank).isSome = true
    rw [hs]; rfl

theorem cover_of_region (Region : P → Prop)
    (entry : Nat) (base : P) (hentry : runP p entry startP = some base)
    (hbase : Region base)
    (progress : ∀ x, Region x → ∃ y, Region y ∧ Goes x y) :
    Cover NeverHalts p :=
  .leaf p (never_of_region Region entry base hentry hbase progress)

#print axioms prefix_run
#print axioms live_of_region
#print axioms never_of_region
#print axioms cover_of_region
end BB6.Agent5Q0151PackedLiveness
