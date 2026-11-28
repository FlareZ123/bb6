import Q0148SourceHopSection
import Lean.Elab.Tactic.Omega

/-!
# Terminal gap-two carry in q0-148: exact source step to gap one

When the original far-left gap reaches exactly two As (after m-1
ordinary marker hops), the final markedHopN uses U(M A) = (A A,T).
The residue 1101 followed by blank 0 is exactly one 11010 marker M.
The resulting source tape is again canonical, now with far-left gap
ONE, not a spurious halt or ill-defined transition.
-/

namespace BB6.Agent39Q0148Carry
open BB6.Agent5Q0148BoundarySweep
open BB6Coverage
open BB6Coverage.Agent31Pump

set_option maxHeartbeats 0
set_option maxRecDepth 20000

/-- At an exceptional last marker, the previous A A carry exactly
    closes every older gap. There is no dangling A at the far edge. -/
theorem gapChainOut_close_two (rs : List Nat) :
    gapChainOut rs ++ [.alternating,.alternating] =
      [.alternating,.alternating] ++ gapChain rs := by
  induction rs with
  | nil => rfl
  | cons r rs ih =>
      simp only [gapChainOut,gapChain]
      rw [List.append_assoc,ih]
      simp only [← aRun_two_snoc r,List.append_assoc,List.cons_append,List.nil_append]

/-- The exceptional gap-two terminal marked-hop word is exactly
    canonical: the last M has no following As (new far-left gap=1). -/
theorem final_two_hop_chunks (j : Nat) (rs : List Nat) :
    (aRun j ++ gapChainOut rs ++ [.alternating,.alternating]) ++
       [.separatedMarker] =
      aRun (j+2) ++ gapChain rs ++ [.separatedMarker] := by
  rw [List.append_assoc (aRun j) (gapChainOut rs),gapChainOut_close_two]
  simp only [← aRun_two_snoc j,List.append_assoc]

/-- Exact terminal bitword: final T residue plus two fresh blank
    zeros contributes precisely one M and one residual zero. -/
theorem final_two_hop_bits (n j : Nat) (rs : List Nat)
    (L : List Bool) :
    inputBits
      (aRun (n+2) ++ [.separatedMarker] ++ aRun j ++
        gapChainOut rs ++ [.alternating,.alternating]) ++
        carryBits .elevenZeroOne ++ [false,false] ++ L =
    inputBits
      (aRun (n+2) ++ [.separatedMarker] ++ aRun (j+2) ++
        gapChain rs ++ [.separatedMarker]) ++ [false] ++ L := by
  have h := absorb_t_two_blanks
    (aRun (n+2) ++ [.separatedMarker] ++ aRun j ++
        gapChainOut rs ++ [.alternating,.alternating]) L
  rw [h]
  have hc := final_two_hop_chunks j rs
  simpa only [List.append_assoc,List.cons_append,List.nil_append] using
    congrArg
      (fun cs : List LeftChunk =>
        inputBits (aRun (n+2) ++ (.separatedMarker :: cs)) ++
        [false] ++ L) hc

/-- An original qE source step with old far-left gap exactly TWO.
    The returned qE has far-left gap ONE, and all old earlier gaps
    remain well-formed. This is the terminal low-branch exception
    required by the boundary-recurrence proof. -/
theorem final_two_hop_source (n j : Nat) (rs : List Nat)
    (L R : List Bool) :
    let cs := aRun (j+2) ++ gapChain rs ++
       [.separatedMarker,.alternating]
    run0 p ((4 + 4 * scanCost cs) + (13 + 2*n))
      ⟨4,[true,false] ++ inputBits cs ++
         [false,false,false] ++ L,
         [false,true,false] ++ rep [true,false] n ++
           [true,true,false] ++ R⟩ =
    some ⟨4,[true,false] ++ inputBits
      (aRun (n+2) ++ [.separatedMarker] ++ aRun (j+2) ++
        gapChain rs ++ [.separatedMarker]) ++
      [false] ++ L,[false] ++ R⟩ := by
  dsimp only
  have h := marked_hop_source n j
      (gapChain rs ++ [.separatedMarker,.alternating])
      ([false,false] ++ L) R
  have hb := final_two_hop_bits n j rs L
  simp only [gapChain_end_two,Prod.fst,Prod.snd] at h
  simp only [List.append_assoc] at h hb ⊢
  rw [hb] at h
  exact h

/-- Just before the gap-two exception, an ordinary source step with
    last old gap exactly THREE creates the required short M A tail. -/
theorem prepare_two_hop_source (n j : Nat) (rs : List Nat)
    (L R : List Bool) :
    let cs := aRun (j+2) ++ gapChain (rs ++ [0])
    run0 p ((4 + 4 * scanCost cs) + (13 + 2*n))
      ⟨4,[true,false] ++ inputBits cs ++
         [false,false,false] ++ L,
         [false,true,false] ++ rep [true,false] n ++
           [true,true,false] ++ R⟩ =
    some ⟨4,[true,false] ++ inputBits
      (aRun (n+2) ++ gapChain (j :: rs) ++
        [.separatedMarker,.alternating]) ++
      [false] ++ L,[false] ++ R⟩ := by
  have h := ordinary_hop_source n j rs 0 L R
  simpa [gapChain,aRun,List.append_assoc] using h

#print axioms gapChainOut_close_two
#print axioms final_two_hop_chunks
#print axioms final_two_hop_bits
#print axioms final_two_hop_source
#print axioms prepare_two_hop_source

end BB6.Agent39Q0148Carry
