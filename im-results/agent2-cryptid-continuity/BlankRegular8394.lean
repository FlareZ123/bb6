import Lean.Elab.Tactic.Omega
import ERemaining

set_option maxHeartbeats 100000000
set_option maxRecDepth 50000
namespace BB6.BlankRegular8394
open CryptidBoundary BB6.BoundaryPadding BB6.Padding

def seed9 : DRegular.L := ⟨9,0,0⟩

private theorem source_seed : DRegularSource.sourceSection seed9 =
    init (List.replicate 7 true) := by
  simp [seed9,DRegularSource.sourceSection,oppairs]

private theorem seed_canon : DRegular.Canon seed9 := by
  simp [seed9,DRegular.Canon]

/-- A certified 8394-return source trace beginning at the authentic blank
    Turing-machine configuration, with exact accumulated raw transition time. -/
theorem blank8394 :
    ∃ t : DRegular.L,
      DRegular.run 8394 seed9 = some t ∧
      ObsEq
        (CryptidBoundary.run (36 + DRegular.accumulated 8394 seed9)
          CryptidBoundary.blank)
        (DRegularSource.sourceSection t) := by
  have hsome : (DRegular.run 8394 seed9).isSome = true := by decide
  cases h : DRegular.run 8394 seed9 with
  | none => simp [h] at hsome
  | some t =>
    refine ⟨t,rfl,?_⟩
    rw [CryptidBoundary.run_add,CryptidBoundary.blank36,←source_seed]
    exact DRegular.transport_obs
      CryptidBoundary.run DRegularSource.sourceSection ObsEq
      (fun c => rfl) CryptidBoundary.run_add
      (fun c => cfgEq_refl (represent c))
      (fun x y z h g => cfgEq_trans h g)
      (fun n x y h => source_congr n h)
      BB6.ERemaining.source_contract
      8394 seed9 t seed_canon h

#print axioms blank8394
end BB6.BlankRegular8394


namespace BB6.BlankRegular8394
open CryptidBoundary BB6.BoundaryPadding BB6.Padding

private theorem stopped_step (c : CryptidBoundary.Cfg) (h : c.st=6) :
    CryptidBoundary.step c = c := by
  cases c with
  | mk l bit r st =>
    change st=6 at h
    subst st
    cases bit <;> rfl

private theorem obs_state {c d : CryptidBoundary.Cfg} (h : ObsEq c d) :
    c.st=d.st := h.2.2.2

private theorem stopped_run (c : CryptidBoundary.Cfg) (n : Nat)
    (h : c.st=6) : CryptidBoundary.run n c = c := by
  induction n with
  | zero => rfl
  | succ n ih =>
    change CryptidBoundary.run n (CryptidBoundary.step c) = c
    rw [stopped_step c h]
    exact ih

/-- No configuration on the actual blank-tape trajectory up to the certified
    8394th regular return is the machine's frozen halt state. -/
theorem no_halt_before_blank8394 (n : Nat)
    (hn : n ≤ 36 + DRegular.accumulated 8394 seed9) :
    (CryptidBoundary.run n CryptidBoundary.blank).st ≠ 6 := by
  obtain ⟨t, hr, heq⟩ := blank8394
  have hlast : (CryptidBoundary.run
       (36 + DRegular.accumulated 8394 seed9) CryptidBoundary.blank).st = 5 := by
    have hs := obs_state heq
    simpa only [DRegularSource.sourceSection,CryptidBoundary.init] using hs
  intro hst
  have hrun : CryptidBoundary.run (36 + DRegular.accumulated 8394 seed9)
      CryptidBoundary.blank = CryptidBoundary.run
      ((36 + DRegular.accumulated 8394 seed9) - n)
      (CryptidBoundary.run n CryptidBoundary.blank) := by
    have ht : n + ((36 + DRegular.accumulated 8394 seed9) - n) =
        36 + DRegular.accumulated 8394 seed9 := by omega
    calc
      _ = CryptidBoundary.run
        (n + ((36 + DRegular.accumulated 8394 seed9) - n))
        CryptidBoundary.blank :=
          congrArg (fun m => CryptidBoundary.run m CryptidBoundary.blank) ht.symm
      _ = _ := CryptidBoundary.run_add _ _ _
  rw [stopped_run _ _ hst] at hrun
  rw [hrun] at hlast
  omega

#print axioms no_halt_before_blank8394
end BB6.BlankRegular8394


namespace BB6.BlankRegular8394
/-- A compact explicit decimal-order lower horizon for the genuine blank start. -/
theorem source_time_ge_10pow7152 :
    10^7152 ≤ 36 + DRegular.accumulated 8394 seed9 := by decide

theorem no_halt_10pow7152 (n : Nat) (hn : n ≤ 10^7152) :
    (CryptidBoundary.run n CryptidBoundary.blank).st ≠ 6 :=
  no_halt_before_blank8394 n (Nat.le_trans hn source_time_ge_10pow7152)

#print axioms source_time_ge_10pow7152
#print axioms no_halt_10pow7152
end BB6.BlankRegular8394
