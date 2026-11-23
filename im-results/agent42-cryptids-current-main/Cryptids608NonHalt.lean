import CryptidsTapeAdapter
import BusyBeaver.Bridge
import IncrementalAudit
import ResidualFrontierManifest
import BusyBeaver.BB6.NonHalt.M_1RB0LC_1LC0RB_0LE0LD_1LCHHH_0RA1LF_1LA1LF
import BusyBeaver.BB6.NonHalt.M_1RB0RA_0RC0LD_1LA1RF_1LE1LD_1LB1RE_HHH1RA
import BusyBeaver.BB6.NonHalt.M_1RB0RA_0RC0LE_1LD1RF_1LB1RD_1LD1LE_HHH1RA
import BusyBeaver.BB6.NonHalt.M_1RB0RA_1RC0LC_0LD1RF_1RA1LE_1LD0LB_0REHHH
import BusyBeaver.BB6.NonHalt.M_1RB1RA_0LC0RA_1RC1LD_0LB1LE_1LF0RC_HHH0LD
import BusyBeaver.BB6.NonHalt.M_1RB1RA_1RC1LB_0LD0RA_1RF1LE_HHH1LF_1LC0LF

/-!
# Six upstream Lean nonhalting certificates grafted into the depth-four frontier

This is an intermediate source bridge. The six external modules are pinned by
the upstream Cryptids main commit recorded in the accompanying README. Each
module proves `IsNotHalt` for its literal RLE machine; `not_halts_to_agent8`
transfers that result to this repository's absolute-tape semantics. The
independent literal tables below prevent an accidental RLE/state-order
mismatch. Each complete singleton cylinder is grafted into the existing
`depth4ResidualAudit`; the exact open-set theorem preserves every other open
completion. The four external halting certificates are intentionally not
included because their `IsHalt` witnesses do not yet provide a bound for
`DecidedBelow 6`.

Pending compatible-toolchain preflight; no compilation is claimed here.
-/

namespace BB6.Cryptids608
open BB6Coverage BB6.ConjectureBridge

set_option maxRecDepth 12000
set_option maxHeartbeats 0

private theorem upstream_is_not_halt_to_agent8
    (source : ConjectureMachines.Machine 6 2)
    (hnot : BusyBeaver.IsNotHalt source.toBB) :
    NeverHalts (toAgent8 source) :=
  not_halts_to_agent8 source
    ((ConjectureMachines.isNotHalt_toBB_iff_not_halts source).mp hnot)

def source_r1 : ConjectureMachines.Machine 6 2 := BusyBeaver.M_1RB0LC_1LC0RB_0LE0LD_1LCHHH_0RA1LF_1LA1LF.machine
def original_r1 : Machine := toAgent8 source_r1
def expectedRLE_r1 : Machine := fun slot =>
  match slot.1.val, slot.2 with
  | 0, false => some ⟨true, true, 1⟩
  | 0, true => some ⟨false, false, 2⟩
  | 1, false => some ⟨true, false, 2⟩
  | 1, true => some ⟨false, true, 1⟩
  | 2, false => some ⟨false, false, 4⟩
  | 2, true => some ⟨false, false, 3⟩
  | 3, false => some ⟨true, false, 2⟩
  | 3, true => none
  | 4, false => some ⟨false, true, 0⟩
  | 4, true => some ⟨true, false, 5⟩
  | 5, false => some ⟨true, false, 0⟩
  | 5, true => some ⟨true, false, 5⟩
  | _, _ => none

theorem original_r1_eq_expectedRLE : original_r1 = expectedRLE_r1 := by
  funext slot
  rcases slot with ⟨q,b⟩
  fin_cases q <;> cases b <;> rfl

theorem original_r1_never : NeverHalts original_r1 :=
  upstream_is_not_halt_to_agent8 source_r1
    (by simpa [source_r1] using BusyBeaver.M_1RB0LC_1LC0RB_0LE0LD_1LCHHH_0RA1LF_1LA1LF.is_not_halt)

theorem literal_r1_never : NeverHalts expectedRLE_r1 := by
  rw [← original_r1_eq_expectedRLE]
  exact original_r1_never

def cylinder_r1 : PartialMachine := fun s => some (expectedRLE_r1 s)

theorem cover_r1 (bound : Nat) : Cover (DecidedBelow bound) cylinder_r1 := by
  apply Cover.leaf
  intro m hm
  have heq : m = expectedRLE_r1 := by
    funext slot
    exact hm slot (expectedRLE_r1 slot) rfl
  rw [heq]
  exact Or.inl literal_r1_never

local instance depth4ResidualOpenDecidable (m : Machine) :
    Decidable (depth4ResidualAudit.open m) :=
  FrontierAudit.openDecidable depth4ResidualAudit m

theorem oldOpen_r1 : depth4ResidualAudit.open expectedRLE_r1 := by
  decide

theorem cylinderMass_r1 : cylinderMass cylinder_r1 = 1 := by decide

def source_r2 : ConjectureMachines.Machine 6 2 := BusyBeaver.M_1RB0RA_0RC0LD_1LA1RF_1LE1LD_1LB1RE_HHH1RA.machine
def original_r2 : Machine := toAgent8 source_r2
def expectedRLE_r2 : Machine := fun slot =>
  match slot.1.val, slot.2 with
  | 0, false => some ⟨true, true, 1⟩
  | 0, true => some ⟨false, true, 0⟩
  | 1, false => some ⟨false, true, 2⟩
  | 1, true => some ⟨false, false, 3⟩
  | 2, false => some ⟨true, false, 0⟩
  | 2, true => some ⟨true, true, 5⟩
  | 3, false => some ⟨true, false, 4⟩
  | 3, true => some ⟨true, false, 3⟩
  | 4, false => some ⟨true, false, 1⟩
  | 4, true => some ⟨true, true, 4⟩
  | 5, false => none
  | 5, true => some ⟨true, true, 0⟩
  | _, _ => none

theorem original_r2_eq_expectedRLE : original_r2 = expectedRLE_r2 := by
  funext slot
  rcases slot with ⟨q,b⟩
  fin_cases q <;> cases b <;> rfl

theorem original_r2_never : NeverHalts original_r2 :=
  upstream_is_not_halt_to_agent8 source_r2
    (by simpa [source_r2] using BusyBeaver.M_1RB0RA_0RC0LD_1LA1RF_1LE1LD_1LB1RE_HHH1RA.is_not_halt)

theorem literal_r2_never : NeverHalts expectedRLE_r2 := by
  rw [← original_r2_eq_expectedRLE]
  exact original_r2_never

def cylinder_r2 : PartialMachine := fun s => some (expectedRLE_r2 s)

theorem cover_r2 (bound : Nat) : Cover (DecidedBelow bound) cylinder_r2 := by
  apply Cover.leaf
  intro m hm
  have heq : m = expectedRLE_r2 := by
    funext slot
    exact hm slot (expectedRLE_r2 slot) rfl
  rw [heq]
  exact Or.inl literal_r2_never

theorem oldOpen_r2 : depth4ResidualAudit.open expectedRLE_r2 := by
  decide

theorem cylinderMass_r2 : cylinderMass cylinder_r2 = 1 := by decide

def source_r3 : ConjectureMachines.Machine 6 2 := BusyBeaver.M_1RB0RA_0RC0LE_1LD1RF_1LB1RD_1LD1LE_HHH1RA.machine
def original_r3 : Machine := toAgent8 source_r3
def expectedRLE_r3 : Machine := fun slot =>
  match slot.1.val, slot.2 with
  | 0, false => some ⟨true, true, 1⟩
  | 0, true => some ⟨false, true, 0⟩
  | 1, false => some ⟨false, true, 2⟩
  | 1, true => some ⟨false, false, 4⟩
  | 2, false => some ⟨true, false, 3⟩
  | 2, true => some ⟨true, true, 5⟩
  | 3, false => some ⟨true, false, 1⟩
  | 3, true => some ⟨true, true, 3⟩
  | 4, false => some ⟨true, false, 3⟩
  | 4, true => some ⟨true, false, 4⟩
  | 5, false => none
  | 5, true => some ⟨true, true, 0⟩
  | _, _ => none

theorem original_r3_eq_expectedRLE : original_r3 = expectedRLE_r3 := by
  funext slot
  rcases slot with ⟨q,b⟩
  fin_cases q <;> cases b <;> rfl

theorem original_r3_never : NeverHalts original_r3 :=
  upstream_is_not_halt_to_agent8 source_r3
    (by simpa [source_r3] using BusyBeaver.M_1RB0RA_0RC0LE_1LD1RF_1LB1RD_1LD1LE_HHH1RA.is_not_halt)

theorem literal_r3_never : NeverHalts expectedRLE_r3 := by
  rw [← original_r3_eq_expectedRLE]
  exact original_r3_never

def cylinder_r3 : PartialMachine := fun s => some (expectedRLE_r3 s)

theorem cover_r3 (bound : Nat) : Cover (DecidedBelow bound) cylinder_r3 := by
  apply Cover.leaf
  intro m hm
  have heq : m = expectedRLE_r3 := by
    funext slot
    exact hm slot (expectedRLE_r3 slot) rfl
  rw [heq]
  exact Or.inl literal_r3_never

theorem oldOpen_r3 : depth4ResidualAudit.open expectedRLE_r3 := by
  decide

theorem cylinderMass_r3 : cylinderMass cylinder_r3 = 1 := by decide

def source_r4 : ConjectureMachines.Machine 6 2 := BusyBeaver.M_1RB0RA_1RC0LC_0LD1RF_1RA1LE_1LD0LB_0REHHH.machine
def original_r4 : Machine := toAgent8 source_r4
def expectedRLE_r4 : Machine := fun slot =>
  match slot.1.val, slot.2 with
  | 0, false => some ⟨true, true, 1⟩
  | 0, true => some ⟨false, true, 0⟩
  | 1, false => some ⟨true, true, 2⟩
  | 1, true => some ⟨false, false, 2⟩
  | 2, false => some ⟨false, false, 3⟩
  | 2, true => some ⟨true, true, 5⟩
  | 3, false => some ⟨true, true, 0⟩
  | 3, true => some ⟨true, false, 4⟩
  | 4, false => some ⟨true, false, 3⟩
  | 4, true => some ⟨false, false, 1⟩
  | 5, false => some ⟨false, true, 4⟩
  | 5, true => none
  | _, _ => none

theorem original_r4_eq_expectedRLE : original_r4 = expectedRLE_r4 := by
  funext slot
  rcases slot with ⟨q,b⟩
  fin_cases q <;> cases b <;> rfl

theorem original_r4_never : NeverHalts original_r4 :=
  upstream_is_not_halt_to_agent8 source_r4
    (by simpa [source_r4] using BusyBeaver.M_1RB0RA_1RC0LC_0LD1RF_1RA1LE_1LD0LB_0REHHH.is_not_halt)

theorem literal_r4_never : NeverHalts expectedRLE_r4 := by
  rw [← original_r4_eq_expectedRLE]
  exact original_r4_never

def cylinder_r4 : PartialMachine := fun s => some (expectedRLE_r4 s)

theorem cover_r4 (bound : Nat) : Cover (DecidedBelow bound) cylinder_r4 := by
  apply Cover.leaf
  intro m hm
  have heq : m = expectedRLE_r4 := by
    funext slot
    exact hm slot (expectedRLE_r4 slot) rfl
  rw [heq]
  exact Or.inl literal_r4_never

theorem oldOpen_r4 : depth4ResidualAudit.open expectedRLE_r4 := by
  decide

theorem cylinderMass_r4 : cylinderMass cylinder_r4 = 1 := by decide

def source_r5 : ConjectureMachines.Machine 6 2 := BusyBeaver.M_1RB1RA_0LC0RA_1RC1LD_0LB1LE_1LF0RC_HHH0LD.machine
def original_r5 : Machine := toAgent8 source_r5
def expectedRLE_r5 : Machine := fun slot =>
  match slot.1.val, slot.2 with
  | 0, false => some ⟨true, true, 1⟩
  | 0, true => some ⟨true, true, 0⟩
  | 1, false => some ⟨false, false, 2⟩
  | 1, true => some ⟨false, true, 0⟩
  | 2, false => some ⟨true, true, 2⟩
  | 2, true => some ⟨true, false, 3⟩
  | 3, false => some ⟨false, false, 1⟩
  | 3, true => some ⟨true, false, 4⟩
  | 4, false => some ⟨true, false, 5⟩
  | 4, true => some ⟨false, true, 2⟩
  | 5, false => none
  | 5, true => some ⟨false, false, 3⟩
  | _, _ => none

theorem original_r5_eq_expectedRLE : original_r5 = expectedRLE_r5 := by
  funext slot
  rcases slot with ⟨q,b⟩
  fin_cases q <;> cases b <;> rfl

theorem original_r5_never : NeverHalts original_r5 :=
  upstream_is_not_halt_to_agent8 source_r5
    (by simpa [source_r5] using BusyBeaver.M_1RB1RA_0LC0RA_1RC1LD_0LB1LE_1LF0RC_HHH0LD.is_not_halt)

theorem literal_r5_never : NeverHalts expectedRLE_r5 := by
  rw [← original_r5_eq_expectedRLE]
  exact original_r5_never

def cylinder_r5 : PartialMachine := fun s => some (expectedRLE_r5 s)

theorem cover_r5 (bound : Nat) : Cover (DecidedBelow bound) cylinder_r5 := by
  apply Cover.leaf
  intro m hm
  have heq : m = expectedRLE_r5 := by
    funext slot
    exact hm slot (expectedRLE_r5 slot) rfl
  rw [heq]
  exact Or.inl literal_r5_never

theorem oldOpen_r5 : depth4ResidualAudit.open expectedRLE_r5 := by
  decide

theorem cylinderMass_r5 : cylinderMass cylinder_r5 = 1 := by decide

def source_r6 : ConjectureMachines.Machine 6 2 := BusyBeaver.M_1RB1RA_1RC1LB_0LD0RA_1RF1LE_HHH1LF_1LC0LF.machine
def original_r6 : Machine := toAgent8 source_r6
def expectedRLE_r6 : Machine := fun slot =>
  match slot.1.val, slot.2 with
  | 0, false => some ⟨true, true, 1⟩
  | 0, true => some ⟨true, true, 0⟩
  | 1, false => some ⟨true, true, 2⟩
  | 1, true => some ⟨true, false, 1⟩
  | 2, false => some ⟨false, false, 3⟩
  | 2, true => some ⟨false, true, 0⟩
  | 3, false => some ⟨true, true, 5⟩
  | 3, true => some ⟨true, false, 4⟩
  | 4, false => none
  | 4, true => some ⟨true, false, 5⟩
  | 5, false => some ⟨true, false, 2⟩
  | 5, true => some ⟨false, false, 5⟩
  | _, _ => none

theorem original_r6_eq_expectedRLE : original_r6 = expectedRLE_r6 := by
  funext slot
  rcases slot with ⟨q,b⟩
  fin_cases q <;> cases b <;> rfl

theorem original_r6_never : NeverHalts original_r6 :=
  upstream_is_not_halt_to_agent8 source_r6
    (by simpa [source_r6] using BusyBeaver.M_1RB1RA_1RC1LB_0LD0RA_1RF1LE_HHH1LF_1LC0LF.is_not_halt)

theorem literal_r6_never : NeverHalts expectedRLE_r6 := by
  rw [← original_r6_eq_expectedRLE]
  exact original_r6_never

def cylinder_r6 : PartialMachine := fun s => some (expectedRLE_r6 s)

theorem cover_r6 (bound : Nat) : Cover (DecidedBelow bound) cylinder_r6 := by
  apply Cover.leaf
  intro m hm
  have heq : m = expectedRLE_r6 := by
    funext slot
    exact hm slot (expectedRLE_r6 slot) rfl
  rw [heq]
  exact Or.inl literal_r6_never

theorem oldOpen_r6 : depth4ResidualAudit.open expectedRLE_r6 := by
  decide

theorem cylinderMass_r6 : cylinderMass cylinder_r6 = 1 := by decide

noncomputable def cryptids608GraftedAudit : FrontierAudit (DecidedBelow 6) emptyTable :=
  addCertificate
    (addCertificate
      (addCertificate
        (addCertificate
          (addCertificate
            (addCertificate depth4ResidualAudit cylinder_r1 (cover_r1 6))
            cylinder_r2 (cover_r2 6))
          cylinder_r3 (cover_r3 6))
        cylinder_r4 (cover_r4 6))
      cylinder_r5 (cover_r5 6))
    cylinder_r6 (cover_r6 6)

theorem cryptids608GraftedAudit_open_iff (m : Machine) :
    cryptids608GraftedAudit.open m ↔
      depth4ResidualAudit.open m ∧
      ¬ compatible cylinder_r1 m ∧ ¬ compatible cylinder_r2 m ∧
      ¬ compatible cylinder_r3 m ∧ ¬ compatible cylinder_r4 m ∧
      ¬ compatible cylinder_r5 m ∧ ¬ compatible cylinder_r6 m := by
  simp [cryptids608GraftedAudit, addCertificate_open_iff, empty_compatible, and_assoc]

theorem cryptids608GraftedAudit_exhaustive (m : Machine) :
    DecidedBelow 6 m ∨ cryptids608GraftedAudit.open m :=
  cryptids608GraftedAudit.exhaustive m (empty_compatible m)

theorem cryptids608GraftedAudit_mass :
    cryptids608GraftedAudit.report.1 + cryptids608GraftedAudit.report.2 = 25^12 := by
  have h := cryptids608GraftedAudit.report_conserves
  have hf : freeSlotCount emptyTable = 12 := by decide
  simpa [cylinderMass, hf] using h

theorem closes_r1 : ¬ cryptids608GraftedAudit.open expectedRLE_r1 := by
  have hiff := cryptids608GraftedAudit_open_iff expectedRLE_r1
  intro hopen
  have h := hiff.mp hopen
  have hc : compatible cylinder_r1 expectedRLE_r1 := by
    intro slot t ht
    exact Option.some.inj (by simpa [cylinder_r1] using ht)
  exact h.2.1 hc

theorem closes_r2 : ¬ cryptids608GraftedAudit.open expectedRLE_r2 := by
  have hiff := cryptids608GraftedAudit_open_iff expectedRLE_r2
  intro hopen
  have h := hiff.mp hopen
  have hc : compatible cylinder_r2 expectedRLE_r2 := by
    intro slot t ht
    exact Option.some.inj (by simpa [cylinder_r2] using ht)
  exact h.2.2.1 hc

theorem closes_r3 : ¬ cryptids608GraftedAudit.open expectedRLE_r3 := by
  have hiff := cryptids608GraftedAudit_open_iff expectedRLE_r3
  intro hopen
  have h := hiff.mp hopen
  have hc : compatible cylinder_r3 expectedRLE_r3 := by
    intro slot t ht
    exact Option.some.inj (by simpa [cylinder_r3] using ht)
  exact h.2.2.2.1 hc

theorem closes_r4 : ¬ cryptids608GraftedAudit.open expectedRLE_r4 := by
  have hiff := cryptids608GraftedAudit_open_iff expectedRLE_r4
  intro hopen
  have h := hiff.mp hopen
  have hc : compatible cylinder_r4 expectedRLE_r4 := by
    intro slot t ht
    exact Option.some.inj (by simpa [cylinder_r4] using ht)
  exact h.2.2.2.2.1 hc

theorem closes_r5 : ¬ cryptids608GraftedAudit.open expectedRLE_r5 := by
  have hiff := cryptids608GraftedAudit_open_iff expectedRLE_r5
  intro hopen
  have h := hiff.mp hopen
  have hc : compatible cylinder_r5 expectedRLE_r5 := by
    intro slot t ht
    exact Option.some.inj (by simpa [cylinder_r5] using ht)
  exact h.2.2.2.2.2.1 hc

theorem closes_r6 : ¬ cryptids608GraftedAudit.open expectedRLE_r6 := by
  have hiff := cryptids608GraftedAudit_open_iff expectedRLE_r6
  intro hopen
  have h := hiff.mp hopen
  have hc : compatible cylinder_r6 expectedRLE_r6 := by
    intro slot t ht
    exact Option.some.inj (by simpa [cylinder_r6] using ht)
  exact h.2.2.2.2.2.2 hc

#print axioms upstream_is_not_halt_to_agent8
#print axioms BusyBeaver.M_1RB0LC_1LC0RB_0LE0LD_1LCHHH_0RA1LF_1LA1LF.is_not_halt
#print axioms original_r1_eq_expectedRLE
#print axioms original_r1_never
#print axioms literal_r1_never
#print axioms oldOpen_r1
#print axioms closes_r1
#print axioms BusyBeaver.M_1RB0RA_0RC0LD_1LA1RF_1LE1LD_1LB1RE_HHH1RA.is_not_halt
#print axioms original_r2_eq_expectedRLE
#print axioms original_r2_never
#print axioms literal_r2_never
#print axioms oldOpen_r2
#print axioms closes_r2
#print axioms BusyBeaver.M_1RB0RA_0RC0LE_1LD1RF_1LB1RD_1LD1LE_HHH1RA.is_not_halt
#print axioms original_r3_eq_expectedRLE
#print axioms original_r3_never
#print axioms literal_r3_never
#print axioms oldOpen_r3
#print axioms closes_r3
#print axioms BusyBeaver.M_1RB0RA_1RC0LC_0LD1RF_1RA1LE_1LD0LB_0REHHH.is_not_halt
#print axioms original_r4_eq_expectedRLE
#print axioms original_r4_never
#print axioms literal_r4_never
#print axioms oldOpen_r4
#print axioms closes_r4
#print axioms BusyBeaver.M_1RB1RA_0LC0RA_1RC1LD_0LB1LE_1LF0RC_HHH0LD.is_not_halt
#print axioms original_r5_eq_expectedRLE
#print axioms original_r5_never
#print axioms literal_r5_never
#print axioms oldOpen_r5
#print axioms closes_r5
#print axioms BusyBeaver.M_1RB1RA_1RC1LB_0LD0RA_1RF1LE_HHH1LF_1LC0LF.is_not_halt
#print axioms original_r6_eq_expectedRLE
#print axioms original_r6_never
#print axioms literal_r6_never
#print axioms oldOpen_r6
#print axioms closes_r6
#print axioms cryptids608GraftedAudit
#print axioms cryptids608GraftedAudit_open_iff
#print axioms cryptids608GraftedAudit_exhaustive
#print axioms cryptids608GraftedAudit_mass

end BB6.Cryptids608
