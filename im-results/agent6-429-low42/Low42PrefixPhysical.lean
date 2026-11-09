import Low42Max
import Low42Physical
import W4HeadPrefix
import Lean.Elab.Tactic.Omega

set_option maxHeartbeats 30000000
set_option maxRecDepth 8192

namespace BB429Low42PrefixPhysical
open BB6Bubble BB429JPhysical BB429Low42 BB429Low42Physical BB429Low42Max
open BB429OddExcursion BB429SourceE1Delta BB429W4HeadMax BB429W4HeadPrefix
open BB429PhysicalBridge BB429DeltaPhysicalBridge

/-- Every primitive prefix of the prepared low4k2 return after its
    j-bubble section is bounded by the sharp frontier head 2j+10. -/
theorem continuation_all_prefixes_right_bound (j k t : Nat)
    (ht : t ≤ 20*j+18*k+79) :
    ∃ c', BB6Coverage.run BB429PhysicalFrontier.target429 t
      {state:=BB6Bubble.A,head:=2*(j:Int),
       tape:=negFill (jTape (j+2*k+1) (2*j)) j} = some c' ∧
      c'.head ≤ 2*(j:Int)+10 := by
  let T := 20*j+18*k+79
  let source := stage42 j k
  let physical : BB6Coverage.Config :=
    {state:=BB6Bubble.A,head:=2*(j:Int),
     tape:=negFill (jTape (j+2*k+1) (2*j)) j}
  have hrep : Represents source physical := stage_represented j k
  have hlen : t+(T-t)=T := by dsimp [T]; omega
  have hfull := low42_source_max_all j k
  change runWithMax T source = some
    (BB429FinishScanEDelta.junc 0 0 (4*j+4*k+12),
    -((4*j+4*k+5:Nat):Int),10) at hfull
  rw [←hlen] at hfull
  cases hpre : runWithMax t source with
  | none =>
    rw [runWithMax_add,hpre] at hfull
    simp at hfull
  | some p =>
    have hbound := runWithMax_prefix_le t (T-t) source p hpre
      (BB429FinishScanEDelta.junc 0 0 (4*j+4*k+12),
        -((4*j+4*k+5:Nat):Int),10) hfull
    have hd : runWithDelta t source = some (p.1,p.2.1) := by
      rw [←runWithMax_toDelta]
      rw [hpre]
      rfl
    obtain ⟨c',hrun,hrep',hhead⟩ :=
      source_runWithDelta_rep t source physical hrep p.1 p.2.1 hd
    refine ⟨c',hrun,?_⟩
    change c'.head = 2*(j:Int) + p.2.1 at hhead
    have hbound10 : p.2.1 ≤ (10:Int) := by
      simpa only [Prod.snd] using hbound
    omega

#print axioms continuation_all_prefixes_right_bound
end BB429Low42PrefixPhysical
