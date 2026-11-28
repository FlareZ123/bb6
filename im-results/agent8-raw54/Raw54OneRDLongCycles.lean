import Raw54Base
import SideCycle
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option autoImplicit false
namespace BB6.Agent8Raw54.OneRDLongCycles
open BB6Coverage BB6Coverage.Agent50SideCycle

/-- Base-25 encoded table, A0,A1,...,F1; 24 denotes a hole. -/
def fromCode (c : Nat) : PartialMachine := fun s =>
  let digit := (c / 25 ^ (2*s.1.val + s.2.toNat)) % 25
  if digit == 24 then none
  else some (some ⟨digit / 12 == 1, (digit % 12) / 6 == 1, ⟨digit % 6, Nat.mod_lt _ (by decide)⟩⟩)

structure Candidate where
  code : Nat
  entry : Nat
  period : Nat
  right : Bool
  boundary : Int
  deriving DecidableEq

/-- Four untrusted candidate cycle witnesses, each kernel rechecked below. -/
def cases : List Candidate :=
  [⟨26212796693122469,1156,239,false,-2⟩,
   ⟨11907681947059394,1002,211,false,-1⟩,
   ⟨11907681947059719,921,219,false,6⟩,
   ⟨2370938783184719,922,219,false,6⟩]

def check (x : Candidate) : Bool :=
  decide (0 < x.period) && finiteSideCycleCheck (fromCode x.code)
    x.entry x.period x.right x.boundary

theorem checks : cases.all check = true := by decide +kernel

/-- Every total machine extending any listed partial table never halts. -/
theorem never (x : Candidate) (hx : x ∈ cases)
    (m : Machine) (hm : compatible (fromCode x.code) m) : NeverHalts m := by
  have h := List.all_eq_true.mp checks x hx
  have hc : 0 < x.period ∧ finiteSideCycleCheck (fromCode x.code) x.entry x.period x.right x.boundary = true := by
    simpa only [check, Bool.and_eq_true, decide_eq_true_eq] using h
  exact finiteSideCycleCheck_sound _ _ _ _ _ hc.1 hc.2 m hm

#print axioms checks
#print axioms never
end BB6.Agent8Raw54.OneRDLongCycles
