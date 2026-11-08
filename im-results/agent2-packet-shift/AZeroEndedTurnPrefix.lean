import Lean.Elab.Tactic.Omega
import EAltMarkerAll
import MarkerZeroSource

namespace BB6.Agent2AZeroEndedTurnPrefix
open CryptidBoundary
set_option maxHeartbeats 10000000

/-- A universal primitive original-machine scan reducing a zero-ended
    alternating exceptional A terminal to an A/0 empty-right-tape section.
    Any left list L and any trailing suffix ys are preserved symbolically.
    This is an enabling macro for the remaining p=2 Z marker problem. -/
theorem scan_zero_ended (r : Nat) (L ys : List Bool) :
    run (2*r+9)
      (⟨L,false,[true,true] ++
        (oppairs (r+1) ++ (false :: ys)),0⟩ : Cfg) =
      (⟨oppairs (r+1) ++ ([false,true,true] ++ L),
        false,ys,0⟩ : Cfg) := by
  let U : List Bool := [false,true,true] ++ L
  have hw : true :: (oppairs r ++ (false::ys)) =
      pairs (r+1) ++ ys := by
    have h := BB6.Agent2MarkerZero.one_marker r
    simpa [BB6.Agent2MarkerZero.marker,List.append_assoc] using
      congrArg (fun xs : List Bool => xs ++ ys) h
  have hfront : run 7
      (⟨L,false,[true,true] ++
        (oppairs (r+1) ++ (false::ys)),0⟩ : Cfg) =
      (⟨U,false,pairs (r+1) ++ ys,0⟩ : Cfg) := by
    have hf := BB6.Agent2EAltTurn.front_seven L
      (oppairs r ++ (false::ys))
    calc
      run 7
        (⟨L,false,[true,true] ++
          (oppairs (r+1) ++ (false::ys)),0⟩ : Cfg) =
        run 7 (⟨L,false,[true,true,false,true] ++
          (oppairs r ++ (false::ys)),0⟩ : Cfg) := by rfl
      _ = (⟨U,false,true :: (oppairs r ++ (false::ys)),0⟩ : Cfg) := by
        simpa only [U] using hf
      _ = (⟨U,false,pairs (r+1) ++ ys,0⟩ : Cfg) := by rw [hw]
  have hscan := BB6.Agent2EAltTurn.a_scan (r+1) U ys
  have ht : 2*r+9 = 7+2*(r+1) := by omega
  rw [ht,run_add,hfront]
  exact hscan

#print axioms scan_zero_ended
end BB6.Agent2AZeroEndedTurnPrefix
