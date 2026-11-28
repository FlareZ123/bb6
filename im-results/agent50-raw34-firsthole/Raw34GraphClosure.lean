import GenericClosedGraph
import Raw34ElevenSideCycles
set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace BB6.Agent50Raw34Graph
open BB6Coverage

/-!
Raw34's first three ordinary blank-tape moves are fixed:
  A0=1RB, B0=1RC, C0=0RD.
The head is then in D. From that point, ANY all-symbol closed
control subset containing D proves nonhalting, regardless of tape
dynamics or assignments outside that subset.

This is a source-level semantic certificate; its use in exact
physical-table counting is separate finite combinatorics.
-/

def root : PartialMachine := BB6.Agent50Raw34Eleven.parent
def start3 : FinRayCfg := {state := 3, head := 3, ones := [1,0]}

/-- Three genuine ordinary blank transitions, independent of all eight
    remaining Raw34 instructions. -/
theorem first3 (m : Machine) (hm : compatible root m) :
    run m 3 blank = some (embedFinRay start3) := by
  have h : finitePartialRun root 3 finiteBlank = some start3 := by decide
  simpa only [embedFinRay_blank] using
    finitePartialRun_sound root m hm finiteBlank start3 3 h

/-- Graph-only sufficient condition: both symbols of every control
    state in S have an ordinary defined action whose successor is in S. -/
def GraphClosed (m : Machine) (S : Fin 6 → Prop) : Prop :=
  ∀ q b, S q →
    ∃ mv : Move, m (q,b) = some mv ∧ S mv.next

/-- Source-authentic Raw34 nonhalting of *every* complete transition
    table whose control graph has a closed all-symbol subset S with D∈S.
    No assumption is made about tape values or unvisited transition slots. -/
theorem never_of_graph_closure
    (m : Machine) (hm : compatible root m)
    (S : Fin 6 → Prop) (hD : S 3)
    (hc : GraphClosed m S) : NeverHalts m := by
  let p : PartialMachine := fun s => some (m s)
  have hp : compatible p m := by
    intro s v h
    exact Option.some.inj h
  have hs : BB6.Agent50GenericClosedGraph.Closed p S := by
    intro q b hq
    obtain ⟨mv, hmv, hn⟩ := hc q b hq
    exact ⟨mv, by simp [p, hmv], hn⟩
  have hz : S (embedFinRay start3).state := by
    simpa [start3, embedFinRay] using hD
  exact BB6.Agent50GenericClosedGraph.never_after
    p S hs m hp 3 (embedFinRay start3) (first3 m hm) hz

/-- A finite state-set formulation convenient for executable graph checks.
    There is no restriction to a particular family of state subsets. -/
theorem never_of_finset
    (m : Machine) (hm : compatible root m)
    (S : Finset (Fin 6)) (hD : (3 : Fin 6) ∈ S)
    (hc : ∀ q ∈ S, ∀ b, ∃ mv : Move,
      m (q,b) = some mv ∧ mv.next ∈ S) : NeverHalts m := by
  apply never_of_graph_closure m hm (fun q => q ∈ S) hD
  intro q b hq
  exact hc q hq b

#print axioms first3
#print axioms never_of_graph_closure
#print axioms never_of_finset
end BB6.Agent50Raw34Graph
