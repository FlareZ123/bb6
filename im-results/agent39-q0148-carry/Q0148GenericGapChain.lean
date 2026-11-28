import Q0148OddGapHopNormal
import Q0148MarkedHopCarry
import Lean.Elab.Tactic.Omega

/-!
# Arbitrarily many already-crossed q0-148 markers: exact U carry

A source qE marked-hop checkpoint has a left chunk word consisting
of A^j followed by a chain of markers M and their post-marker A-runs.
All ordinary old gaps >=3 have post-marker runs A^(r+2), r>=0.
For ANY NUMBER of these gaps, U passes through the whole chain and
remains U, preserving the chain apart from a two-token carry at every
marker. The two exceptional terminal gaps 1,2 have exact residues S,T.
Consequently markedHopN has a uniform source-normalized conclusion
independent of the number or sizes of crossed marker groups.
-/

namespace BB6.Agent39Q0148Carry
open BB6.Agent5Q0148BoundarySweep
open BB6Coverage
open BB6Coverage.Agent31Pump

set_option maxHeartbeats 0
set_option maxRecDepth 20000

/-- Arbitrary positive A-run length (not just even length):
    S A^(r+2) -> M A^r, carry U. -/
theorem s_any_posttwo (r : Nat) :
    carryFold .eleven (aRun (r+2)) =
      (.separatedMarker :: aRun r, .one) := by
  have hr : r+2 = 2+r := by omega
  rw [hr,aRun_add,fold_append]
  simp [aRun,carryFold,carryStep,u_run_copy]

/-- The central ordinary-gap carry identity, with no parity condition:
    U (M A^(r+2)) = A A M A^r, carry U.
    This is valid for EVERY r>=0; the remaining old gap is >=3. -/
theorem u_marker_any_posttwo (r : Nat) :
    carryFold .one (.separatedMarker :: aRun (r+2)) =
      ([.alternating,.alternating,.separatedMarker] ++ aRun r, .one) := by
  have h := fold_append .one [.separatedMarker] (aRun (r+2))
  simpa [carryFold,carryStep,s_any_posttwo,List.append_assoc] using h

/-- The prior marker chain, ordered from the current active head
    towards the leftmost boundary; each r encodes old gap r+3. -/
def gapChain : List Nat → List LeftChunk
  | [] => []
  | r::rs => (.separatedMarker :: aRun (r+2)) ++ gapChain rs

/-- Exact emitted words for the U-processed marker chain, before
    flattening the A A carry across successive markers. -/
def gapChainOut : List Nat → List LeftChunk
  | [] => []
  | r::rs =>
      ([.alternating,.alternating,.separatedMarker] ++ aRun r) ++
        gapChainOut rs

/-- Uniform transducer normalization for ARBITRARILY MANY previously
    processed marker gaps, each >=3, and arbitrary gap sizes. -/
theorem gapChain_u (rs : List Nat) :
    carryFold .one (gapChain rs) = (gapChainOut rs, .one) := by
  induction rs with
  | nil => rfl
  | cons r rs ih =>
      simp only [gapChain,gapChainOut,fold_append]
      rw [u_marker_any_posttwo,ih]
      simp only [List.append_assoc]

/-- First exceptional leftmost gap of length two: final M A has
    output A A and *T* residue, independently of earlier large gaps. -/
theorem gapChain_end_two (rs : List Nat) :
    carryFold .one
       (gapChain rs ++ [.separatedMarker,.alternating]) =
    (gapChainOut rs ++ [.alternating,.alternating], .elevenZeroOne) := by
  rw [fold_append,gapChain_u]
  rfl

/-- Exceptional leftmost gap of length one: final M has output
    A A and S residue, independent of all earlier gap sizes. -/
theorem gapChain_end_one (rs : List Nat) :
    carryFold .one (gapChain rs ++ [.separatedMarker]) =
    (gapChainOut rs ++ [.alternating,.alternating], .eleven) := by
  rw [fold_append,gapChain_u]
  rfl

/-- The bitwise terminal U residue followed by two blanks is exactly
    an A token and one residual blank for the next marked hop. -/
theorem absorb_u_two_blanks (cs : List LeftChunk) (L : List Bool) :
    inputBits cs ++ carryBits .one ++ [false,false] ++ L =
    inputBits (cs ++ [.alternating]) ++ [false] ++ L := by
  simp [inputBits_append,inputBits,chunkBits,carryBits,List.append_assoc]

/-- The terminal T residue followed by two blanks is precisely
    an M token plus one residual blank. -/
theorem absorb_t_two_blanks (cs : List LeftChunk) (L : List Bool) :
    inputBits cs ++ carryBits .elevenZeroOne ++ [false,false] ++ L =
    inputBits (cs ++ [.separatedMarker]) ++ [false] ++ L := by
  simp [inputBits_append,inputBits,chunkBits,carryBits,List.append_assoc]

/-- A qE marked hop, away from the short leftmost exceptional gap,
    is a source-certified positive run with unchanged carry U.
    This can be iterated over arbitrary marker chains; no F1. -/
theorem gapChain_marked_hop_source (n j : Nat) (rs : List Nat)
    (L R : List Bool) :
    let cs := aRun (j+2) ++ gapChain rs
    run0 p ((4 + 4 * scanCost cs) + (13 + 2*n))
      ⟨4,[true,false] ++ inputBits cs ++ [false] ++ L,
        [false,true,false] ++ rep [true,false] n ++
          [true,true,false] ++ R⟩ =
    some ⟨4,[true,false] ++ inputBits
      (aRun (n+2) ++ [.separatedMarker] ++ aRun j ++
        gapChainOut rs) ++ [true] ++ L,
      [false] ++ R⟩ := by
  dsimp only
  have h := marked_hop_source n j (gapChain rs) L R
  simpa [gapChain_u,carryBits,List.append_assoc] using h

#print axioms s_any_posttwo
#print axioms u_marker_any_posttwo
#print axioms gapChain_u
#print axioms gapChain_end_two
#print axioms gapChain_end_one
#print axioms absorb_u_two_blanks
#print axioms absorb_t_two_blanks
#print axioms gapChain_marked_hop_source

end BB6.Agent39Q0148Carry
