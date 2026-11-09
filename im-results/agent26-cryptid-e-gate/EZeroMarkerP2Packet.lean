import Lean.Elab.Tactic.Omega
import EZeroMarkerP2Source
import MarkerZeroSource

namespace BB6.Agent26EZTwoPacket
open CryptidBoundary BB6.Agent31PacketSource
open BB6.BoundaryPadding BB6.Padding
open BB6.Agent2BoundaryBZero BB6.Agent2MarkerZero

set_option maxRecDepth 8192
set_option maxHeartbeats 10000000

private def inputWord (k q m : Nat) : List Bool :=
  List.replicate (3*k+2) true ++
    false::(pairs (q+1) ++ ([true,true,false] ++ pairs m))

private theorem inputShape (k q m : Nat) :
    packet (3*k+4) (q+1) 2 (marker m) =
    init (inputWord k q m) := by
  have hn : List.replicate (3*k+4) true =
      true::true::List.replicate (3*k+2) true := by
    rw [show 3*k+4=2+(3*k+2) by omega,
      ← List.replicate_append_replicate]
    rfl
  have hm : marker m = false::pairs m := oppairs_false m
  have hw : oppairs (q+1) ++
      (false::(List.replicate 2 true ++ marker m)) =
      false::(pairs (q+1) ++ ([true,true,false] ++ pairs m)) := by
    rw [hm]
    calc
      _ = (oppairs (q+1) ++ [false]) ++
          ([true,true,false] ++ pairs m) := by
            simp [List.append_assoc]
      _ = _ := by
        rw [oppairs_false]
        rfl
  simp only [packet,word,init,inputWord,List.cons_append]
  rw [hn,hw]
  rfl

private theorem paddedShape (k q m : Nat) :
    inputWord k q m ++ [false] =
      List.replicate (3*k+2) true ++
        false::(pairs (q+1) ++
          ([true,true,false] ++ (pairs m ++ [false]))) := by
  simp [inputWord,List.append_assoc]

/-- For every E index 3k+4, every positive E-pair count and every
    zero-marker depth, the exact source return produces another packet
    with a two-block-zero marker. The one implicit blank is transported
    by the original source's proven physical tape bisimulation. -/
theorem e_two_Z_packet (k q m : Nat) :
    ObsEq
      (run (12*k*k+49*k+64+4*q+4*m)
        (packet (3*k+4) (q+1) 2 (marker m)))
      (packet (8*k+5) 0 (2*(q+1)+2)
        (false::List.replicate (2*m+6) true)) := by
  let xs := inputWord k q m
  have hin : packet (3*k+4) (q+1) 2 (marker m) = init xs :=
    inputShape k q m
  have hpad : ObsEq
      (run (12*k*k+49*k+64+4*q+4*m)
        (packet (3*k+4) (q+1) 2 (marker m)))
      (run (12*k*k+49*k+64+4*q+4*m) (init (xs ++ [false]))) := by
    rw [hin]
    exact source_init_pad _ 1 xs
  have hraw : run (12*k*k+49*k+64+4*q+4*m)
        (init (xs ++ [false])) =
      (⟨[],false,List.replicate (8*k+5) true ++
        (false::List.replicate (2*(q+1)+2) true ++
          (false::List.replicate (2*m+6) true)),5⟩ : Cfg) := by
    rw [show xs ++ [false] =
      List.replicate (3*k+2) true ++
        false::(pairs (q+1) ++
          ([true,true,false] ++ (pairs m ++ [false]))) from
            paddedShape k q m]
    simpa only [List.append_nil] using
      (BB6.Agent26EZTwo.full_E_Z_p2_all k q m [])
  have hout :
      (⟨[],false,List.replicate (8*k+5) true ++
        (false::List.replicate (2*(q+1)+2) true ++
          (false::List.replicate (2*m+6) true)),5⟩ : Cfg) =
      packet (8*k+5) 0 (2*(q+1)+2)
        (false::List.replicate (2*m+6) true) := by
    rfl
  apply cfgEq_trans hpad
  rw [hraw,hout]
  exact cfgEq_refl _

#print axioms e_two_Z_packet
end BB6.Agent26EZTwoPacket
