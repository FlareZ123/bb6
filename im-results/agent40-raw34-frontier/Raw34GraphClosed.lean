import GenericClosedGraph
set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace BB6.Agent40Raw34GraphClosed
open BB6Coverage

/-!
An original-source, *parametric* finite-control nonhalting criterion
specialized to the eight-hole Raw34 parent

  1RB---_1RC---_0RD---_1LC---_------_------

Starting on genuine blank tape, the first three steps reach state D.
Any nonempty set S of states containing D that is closed under both
symbols' nonhalting actions in a compatible *total* machine is therefore
a sufficient all-time nonhalting certificate. The set S need not
contain the initial states A or B. This captures all 12 possible graph
components containing C,D that respect the four fixed root transitions,
including new CDE/CDF/CDEF and BCDE/BCDF/BCDEF/ABCD/ABCDE/ABCDF cases.

The mathematical claim is all-time: no tape approximation, runtime
bound, or assumption of unreachable *tape* patterns is needed.
This source theorem does not itself assert a complete Raw34 Cover.
-/

def base : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0,false => some (some ⟨true,true,1⟩)
  | 1,false => some (some ⟨true,true,2⟩)
  | 2,false => some (some ⟨false,true,3⟩)
  | 3,false => some (some ⟨true,false,2⟩)
  | _,_ => none

def start3 : FinRayCfg := {state:=3,head:=3,ones:=[1,0]}

theorem root_first3 (m : Machine) (hm : compatible base m) :
    run m 3 blank = some (embedFinRay start3) := by
  have hr : finitePartialRun base 3 finiteBlank = some start3 := by rfl
  simpa only [embedFinRay_blank] using
    finitePartialRun_sound base m hm finiteBlank start3 3 hr

def totalAsPartial (m : Machine) : PartialMachine :=
  fun slot => some (m slot)

theorem total_compatible (m : Machine) :
    compatible (totalAsPartial m) m := by
  intro slot v hv
  exact Option.some.inj (by simpa [totalAsPartial] using hv)

def ClosedOnTotal (S : Fin 6 → Prop) (m : Machine) : Prop :=
  ∀ q b, S q → ∃ move : Move, m (q,b) = some move ∧ S move.next

theorem closure_as_partial (S : Fin 6 → Prop) (m : Machine)
    (hc : ClosedOnTotal S m) :
    BB6.Agent50GenericClosedGraph.Closed (totalAsPartial m) S := by
  intro q b hq
  obtain ⟨mv,hslot,hn⟩ := hc q b hq
  refine ⟨mv, ?_, hn⟩
  simp [totalAsPartial,hslot]

theorem never_of_closed_control (m : Machine)
    (hm : compatible base m)
    (S : Fin 6 → Prop)
    (hD : S 3)
    (hclosed : ClosedOnTotal S m) :
    NeverHalts m := by
  exact BB6.Agent50GenericClosedGraph.never_after
    (totalAsPartial m) S (closure_as_partial S m hclosed)
    m (total_compatible m) 3 (embedFinRay start3)
    (root_first3 m hm)
    (by simpa [start3,embedFinRay] using hD)

/-- The graph condition may be certified by a concrete bitmask of six states.
    The bound mask<64 is not required for soundness: high bits are ignored. -/
def maskStates (mask : Nat) (q : Fin 6) : Prop :=
  Nat.testBit mask q.val = true

theorem never_of_mask (m : Machine)
    (hm : compatible base m) (mask : Nat)
    (hD : maskStates mask 3)
    (hc : ClosedOnTotal (maskStates mask) m) :
    NeverHalts m :=
  never_of_closed_control m hm (maskStates mask) hD hc

#print axioms root_first3
#print axioms total_compatible
#print axioms closure_as_partial
#print axioms never_of_closed_control
#print axioms never_of_mask

end BB6.Agent40Raw34GraphClosed
