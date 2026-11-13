import Low43Physical
import PhysicalNoFatalConverse

set_option maxHeartbeats 30000000
set_option maxRecDepth 65536

namespace BB429Low43PhysicalNoFatal

open BB6Coverage BB6Bubble BB429PhysicalFrontier BB429JPhysical
open BB429FinishScanEDelta BB429PhysicalBridge
open BB429Low43Physical BB429PhysicalNoFatalConverse

/-- The uniform physical low43 entry to its blank-right C/0 checkpoint
    is C/01-free at every primitive prefix. This follows from the
    endpoint-only physical converse, without a guarded source execution. -/
theorem low43_C0_record_all_prefix_c01_free (v k : Nat) :
    ∃ cC : Config,
      run target429 (4*v*v+18*v+22)
        {state:=A,head:=0,tape:=jTape (v+2*k+2) (2*v+1)} = some cC ∧
      cC.head=2*(v:Int)+6 ∧
      Represents (low43_C0_zipper v k) cC ∧
      cC.state.val=2 ∧
      cC.tape cC.head=false ∧
      cC.tape (cC.head+1)=false ∧
      (∀ t : Nat, t ≤ 4*v*v+18*v+22 →
        ∃ d : Config,
          run target429 t
            {state:=A,head:=0,tape:=jTape (v+2*k+2) (2*v+1)} = some d ∧
          ¬ physicalC01 d) := by
  obtain ⟨cC, hrun, hhead, hrep, hstate, hcur, hright, _⟩ :=
    low43_C0_record v k
  refine ⟨cC, hrun, hhead, hrep, hstate, hcur, hright, ?_⟩
  exact physical_run_prefix_c01_free_of_c0_blank_right
    (4*v*v+18*v+22)
    {state:=A,head:=0,tape:=jTape (v+2*k+2) (2*v+1)}
    cC hrun hstate hcur hright

#print axioms low43_C0_record_all_prefix_c01_free

end BB429Low43PhysicalNoFatal
