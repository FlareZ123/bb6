import Lean.Elab.Tactic.Omega
import MarkerZeroSource
import MarkerTowerSource
import EAltMarkerAll

namespace BB6.Agent2EAltPacketCompose
open CryptidBoundary BB6.Agent31PacketSource
open BB6.BoundaryPadding
open BB6.Agent2BoundaryBZero
set_option maxHeartbeats 10000000
set_option maxRecDepth 8192

/-- Output of the full variable-marker E turn is precisely a Z marker
    packet, including its explicit final tape zero. -/
private theorem outputShape (k q r : Nat) :
    (⟨[],false,List.replicate (8*k+3) true ++
      BB6.Agent2EAltTurn.outputWord q r [],5⟩ : Cfg) =
      packet (8*k+5) 0 (2*q+6) (BB6.Agent2MarkerZero.marker (r+2)) := by
  have hpair : pairs (r+3) =
      true :: BB6.Agent2MarkerZero.marker (r+2) := by
    simpa only [show r+3=(r+2)+1 by omega] using
      (BB6.Agent2MarkerZero.one_marker (r+2)).symm
  have hones : [true,true,true] ++
      (List.replicate (2*(q+1)) true ++ [true]) =
      List.replicate (2*q+6) true := by
    change List.replicate 3 true ++
      (List.replicate (2*(q+1)) true ++
        List.replicate 1 true) =
      List.replicate (2*q+6) true
    rw [←List.append_assoc,List.replicate_append_replicate,
        List.replicate_append_replicate]
    congr 1 <;> omega
  have htail : [true,true,true] ++
      (List.replicate (2*(q+1)) true ++ pairs (r+3)) =
      List.replicate (2*q+6) true ++
        BB6.Agent2MarkerZero.marker (r+2) := by
    rw [hpair]
    calc
      _ = ([true,true,true] ++
          (List.replicate (2*(q+1)) true ++ [true])) ++
            BB6.Agent2MarkerZero.marker (r+2) := by
              simp [List.append_assoc]
      _ = _ := by rw [hones]
  have hprefix : List.replicate (8*k+3) true ++ [true,true] =
      List.replicate (8*k+5) true := by
    change List.replicate (8*k+3) true ++
      List.replicate 2 true = List.replicate (8*k+5) true
    rw [List.replicate_append_replicate]
    congr 1 <;> omega
  simp only [BB6.Agent2EAltTurn.outputWord,packet,word,
    List.replicate_zero,List.nil_append,List.append_nil]
  change
    (⟨[],false,List.replicate (8*k+3) true ++
      ([true,true] ++ ([false,true,true,true] ++
         (List.replicate (2*(q+1)) true ++ pairs (r+3)))),5⟩ : Cfg) =
    (⟨[],false,List.replicate (8*k+5) true ++
      (false :: (List.replicate (2*q+6) true ++
        BB6.Agent2MarkerZero.marker (r+2))),5⟩ : Cfg)
  rw [←List.append_assoc,hprefix]
  change
    (⟨[],false,List.replicate (8*k+5) true ++
      (false :: ([true,true,true] ++
         (List.replicate (2*(q+1)) true ++ pairs (r+3)))),5⟩ : Cfg) = _
  rw [htail]

private theorem inputShape (k q r : Nat) :
    packet (3*k+4) q 2 (BB6.Agent2MarkerTower.marker (r+1)) =
      init (List.replicate (3*k+2) true ++
        false :: (pairs q ++
          ([true,true] ++
            (oppairs (r+1) ++ [true,true])))) := by
  have hn : List.replicate (3*k+4) true =
      true :: true :: List.replicate (3*k+2) true := by
    rw [show 3*k+4=2+(3*k+2) by omega,
      ←List.replicate_append_replicate]
    rfl
  have hp : List.replicate 2 true = [true,true] := rfl
  have hw : oppairs q ++
       (false :: (List.replicate 2 true ++
          BB6.Agent2MarkerTower.marker (r+1))) =
      false :: (pairs q ++
        ([true,true] ++ (oppairs (r+1) ++ [true,true]))) := by
    rw [hp]
    change oppairs q ++
      (false :: ([true,true] ++
         (oppairs (r+1) ++ [true,true]))) = _
    calc
      _ = (oppairs q ++ [false]) ++
        ([true,true] ++ (oppairs (r+1) ++ [true,true])) := by
          simp [List.append_assoc]
      _ = _ := by
        rw [BB6.Agent2MarkerZero.oppairs_false]
        rfl
  simp only [packet,word,init,List.cons_append]
  rw [hn,hw]
  rfl

/-- Exact raw all-k,q,r E,p=2 exceptional marker return with a
    quantified zero-terminating alternating marker endpoint. -/
theorem e_two_to_zero (k q r : Nat) :
    run (12*k*k+49*k+68+4*q+6*r)
      (packet (3*k+4) q 2 (BB6.Agent2MarkerTower.marker (r+1))) =
      packet (8*k+5) 0 (2*q+6) (BB6.Agent2MarkerZero.marker (r+2)) := by
  rw [inputShape]
  have hSource := BB6.Agent2EAltTurn.full_E_many k q r []
  simp only [List.append_nil] at hSource
  exact hSource.trans (outputShape k q r)

/-- All E,p=2 with q≡2 mod3 and any positive 11-marker depth reach L.
    Source-based synthesis, not a blank-tape theorem. -/
theorem e_two_q2_regular (k u r : Nat) :
    ∃ T a pairsCount b,
      ObsEq
        (run T
          (packet (3*k+4) (3*u+2) 2
            (BB6.Agent2MarkerTower.marker (r+1))))
        (regularSection a pairsCount b) := by
  let c : BB6.Agent31PacketRank.Packet := ⟨8*k+5,0,2*(3*u+2)+6⟩
  have ha : c.a ≥ 4 := by dsimp [c]; omega
  have hp : c.p % 3 = 1 := by dsimp [c]; omega
  obtain ⟨T,a,z,b,h⟩ := BB6.Agent2MarkerZero.all_p1_regular (r+2) c ha hp
  refine ⟨12*k*k+49*k+68+4*(3*u+2)+6*r+T,a,z,b,?_⟩
  rw [run_add,e_two_to_zero]
  exact h

#print axioms e_two_to_zero
#print axioms e_two_q2_regular
end BB6.Agent2EAltPacketCompose
