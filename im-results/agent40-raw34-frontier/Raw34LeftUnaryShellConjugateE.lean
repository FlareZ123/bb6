import Raw34LeftUnaryShell
import Raw34LeftUnaryShellRD
import Raw34BinaryCounterF

set_option maxRecDepth 100000
set_option maxHeartbeats 0

/-!
Original-source E/F state-conjugate proofs for TWO additional
unbounded unary-shell Raw34 four-hole cylinders:
  1RB---_1RC---_0RD1LC_1LC1RE_1LC1RE_------
  1RB---_1RC---_0RD1LC_1LC1RE_1RD1RE_------
The original F-shell theorems transfer using the accepted
rename_run/state-swap lemma. Unassigned A1,B1,F0,F1 can HALT.
Source-closure acceptance of Shell and ShellRD is a prerequisite.
-/
namespace BB6.Agent40Raw34LeftUnaryShellConjugateE
open BB6Coverage BB6.Agent13BlankDelay

def pE (r : Bool) : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0,false => some (some ⟨true,true,1⟩)
  | 1,false => some (some ⟨true,true,2⟩)
  | 2,false => some (some ⟨false,true,3⟩)
  | 2,true  => some (some ⟨true,false,2⟩)
  | 3,false => some (some ⟨true,false,2⟩)
  | 3,true  => some (some ⟨true,true,4⟩)
  | 4,false => some (some ⟨true,r,if r then 3 else 2⟩)
  | 4,true  => some (some ⟨true,true,4⟩)
  | _,_ => none

private def ef : StatePerm := swapStates (4 : Fin 6) 5

def permPartial (p : PartialMachine) : PartialMachine := fun slot =>
  (p (ef.backward slot.1,slot.2)).map (Option.map (renameMove ef))

theorem source_lc :
    BB6.Agent40Raw34LeftUnaryShell.p = permPartial (pE false) := by
  have h : ∀ (s : Fin 6) (b : Bool),
      BB6.Agent40Raw34LeftUnaryShell.p (s,b) =
      permPartial (pE false) (s,b) := by decide
  funext slot
  rcases slot with ⟨s,b⟩
  exact h s b

theorem source_rd :
    BB6.Agent40Raw34LeftUnaryShellRD.p = permPartial (pE true) := by
  have h : ∀ (s : Fin 6) (b : Bool),
      BB6.Agent40Raw34LeftUnaryShellRD.p (s,b) =
      permPartial (pE true) (s,b) := by decide
  funext slot
  rcases slot with ⟨s,b⟩
  exact h s b

theorem perm_compatible (p : PartialMachine) (m : Machine)
    (hm : compatible p m) :
    compatible (permPartial p) (renameTable ef m) := by
  intro slot target hp
  unfold permPartial at hp
  cases hs : p (ef.backward slot.1,slot.2) with
  | none => simp [hs] at hp
  | some v =>
    have hm' := hm (ef.backward slot.1,slot.2) v hs
    simpa [renameTable,hs,hm'] using hp

theorem lift_never (p q : PartialMachine)
    (heq : p = permPartial q)
    (hnever : ∀ m, compatible p m → NeverHalts m)
    (m : Machine) (hm : compatible q m) : NeverHalts m := by
  intro n
  have hz : ef.forward 0 = 0 := by decide
  have hb : renameConfig ef blank = blank := by
    simp [renameConfig,blank,hz]
  have hr := rename_run ef m blank n
  rw [hb] at hr
  have hc : compatible p (renameTable ef m) := by
    rw [heq]
    exact perm_compatible q m hm
  have hLive := hnever (renameTable ef m) hc n
  rw [hr] at hLive
  cases h : run m n blank with
  | none => simp [h] at hLive
  | some c => rfl

theorem shell_lc_E_never (m : Machine)
    (hm : compatible (pE false) m) : NeverHalts m :=
  lift_never BB6.Agent40Raw34LeftUnaryShell.p (pE false) source_lc
    BB6.Agent40Raw34LeftUnaryShell.all_time_never m hm

theorem shell_rd_E_never (m : Machine)
    (hm : compatible (pE true) m) : NeverHalts m :=
  lift_never BB6.Agent40Raw34LeftUnaryShellRD.p (pE true) source_rd
    BB6.Agent40Raw34LeftUnaryShellRD.all_time_never m hm

#print axioms source_lc
#print axioms source_rd
#print axioms lift_never
#print axioms shell_lc_E_never
#print axioms shell_rd_E_never
end BB6.Agent40Raw34LeftUnaryShellConjugateE
