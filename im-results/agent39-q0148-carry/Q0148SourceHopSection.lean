import Q0148GenericGapChain
import Lean.Elab.Tactic.Omega

/-!
# Exact source-level qE-to-qE vector-splice across an arbitrary old gap chain

This turns Agent5's original-table markedHopN gadget into the
UNBOUNDED ordinary marked-hop update of the gap-vector mechanism.
Each previously crossed gap except the far-left one is preserved,
the newly crossed active group freezes at j+3, the far-left gap
decreases by one, and the new active head is n+2 A tokens into
the following group. A separate first-hop lemma handles no prior
markers. The *final exceptional* low-gap step, and connecting the
right-hand suffix list to the next hop, remain necessary to prove the
entire boundary recurrence/nonhalting theorem.
-/

namespace BB6.Agent39Q0148Carry
open BB6.Agent5Q0148BoundarySweep
open BB6Coverage
open BB6Coverage.Agent31Pump

set_option maxHeartbeats 0
set_option maxRecDepth 20000

theorem aRun_snoc (n : Nat) :
    aRun n ++ [.alternating] = aRun (n+1) := by
  simpa [aRun] using (aRun_add n 1).symm

theorem aRun_two_snoc (n : Nat) :
    aRun n ++ [.alternating,.alternating] = aRun (n+2) := by
  simpa [aRun] using (aRun_add n 2).symm

/-- The two initial A carries at each marker pass to the previous
    gap, so in the complete word EVERY gap except the far-left one
    is unchanged. Only the far-left gap loses one A after the
    dangling U bit is paired with a blank zero. -/
theorem gapChainOut_snoc (rs : List Nat) (z : Nat) :
    gapChainOut (rs ++ [z]) ++ [.alternating] =
      [.alternating,.alternating] ++ gapChain rs ++
        [.separatedMarker] ++ aRun (z+1) := by
  induction rs with
  | nil =>
      simp [gapChainOut,gapChain,aRun_snoc,List.append_assoc]
  | cons r rs ih =>
      simp only [List.cons_append,gapChainOut,gapChain]
      rw [List.append_assoc, ih]
      simp only [← aRun_two_snoc r, List.append_assoc, List.cons_append, List.nil_append]

/-- Uniform exact canonical chunk-splice for an arbitrary chain of
    old groups with lengths >=3: first return group has j+3 As,
    all intervening old gaps are preserved, and last old gap r+3
    decreases to r+2. -/
theorem ordinary_hop_chunks (j : Nat) (rs : List Nat) (z : Nat) :
    (aRun j ++ gapChainOut (rs ++ [z])) ++ [.alternating] =
      aRun (j+2) ++ gapChain rs ++
        [.separatedMarker] ++ aRun (z+1) := by
  rw [List.append_assoc,gapChainOut_snoc]
  rw [← aRun_two_snoc j]
  simp only [List.append_assoc]

/-- Raw-bit version for precisely two untouched zeros at the far
    left: dangling U bit plus the first zero form the final A,
    and the second zero supplies the next exact-source frame. -/
theorem ordinary_hop_bits (n j : Nat) (rs : List Nat) (z : Nat)
    (L : List Bool) :
    inputBits
      (aRun (n+2) ++ [.separatedMarker] ++ aRun j ++
        gapChainOut (rs ++ [z])) ++ carryBits .one ++
        [false,false] ++ L =
    inputBits
      (aRun (n+2) ++ [.separatedMarker] ++ aRun (j+2) ++
        gapChain rs ++ [.separatedMarker] ++ aRun (z+1)) ++
        [false] ++ L := by
  have h := absorb_u_two_blanks
    (aRun (n+2) ++ [.separatedMarker] ++ aRun j ++
        gapChainOut (rs ++ [z])) L
  rw [h]
  have hc := ordinary_hop_chunks j rs z
  simpa only [List.append_assoc, List.cons_append, List.nil_append] using
    congrArg
      (fun cs : List LeftChunk =>
        inputBits (aRun (n+2) ++ (.separatedMarker :: cs)) ++
          [false] ++ L) hc

/-- The first marked hop, with no previously crossed marker groups.
    Its source output freezes g0 at j+2 and creates the next active
    head at index n+2, with no finite bound on j or n. -/
theorem first_hop_source (n j : Nat) (L R : List Bool) :
    let cs := aRun (j+2)
    run0 p ((4 + 4 * scanCost cs) + (13 + 2*n))
      ⟨4,[true,false] ++ inputBits cs ++
         [false,false,false] ++ L,
         [false,true,false] ++ rep [true,false] n ++
           [true,true,false] ++ R⟩ =
    some ⟨4,[true,false] ++ inputBits
      (aRun (n+2) ++ [.separatedMarker] ++ aRun (j+1)) ++
      [false] ++ L,[false] ++ R⟩ := by
  dsimp only
  have h := marked_hop_source n j [] ([false,false] ++ L) R
  have hb := absorb_u_two_blanks
    (aRun (n+2) ++ [.separatedMarker] ++ aRun j) L
  simp only [List.append_nil,carryFold,carryBits] at h
  have hb' : inputBits (aRun (n+2) ++ [.separatedMarker] ++ aRun j ++ [.alternating]) =
      inputBits (aRun (n+2) ++ [.separatedMarker] ++ aRun (j+1)) := by
    simp only [List.append_assoc,aRun_snoc]
  rw [hb'] at hb
  simp only [carryBits] at hb
  -- normalize association without unfolding inputBits
  simp only [List.append_assoc] at h hb ⊢
  rw [hb] at h
  exact h

/-- The completely general nonterminal E1 marker-hop source step:
    arbitrary old group sizes >=3, arbitrarily many old groups.
    Its output keeps exact tape geometry and remaining right suffix. -/
theorem ordinary_hop_source (n j : Nat) (rs : List Nat) (z : Nat)
    (L R : List Bool) :
    let cs := aRun (j+2) ++ gapChain (rs ++ [z])
    run0 p ((4 + 4 * scanCost cs) + (13 + 2*n))
      ⟨4,[true,false] ++ inputBits cs ++
         [false,false,false] ++ L,
         [false,true,false] ++ rep [true,false] n ++
           [true,true,false] ++ R⟩ =
    some ⟨4,[true,false] ++ inputBits
      (aRun (n+2) ++ [.separatedMarker] ++ aRun (j+2) ++
        gapChain rs ++ [.separatedMarker] ++ aRun (z+1)) ++
      [false] ++ L,[false] ++ R⟩ := by
  dsimp only
  have h := gapChain_marked_hop_source n j (rs ++ [z])
      ([false,false] ++ L) R
  have hb := ordinary_hop_bits n j rs z L
  simp only [carryBits,List.append_assoc] at hb h ⊢
  rw [hb] at h
  exact h

#print axioms aRun_snoc
#print axioms aRun_two_snoc
#print axioms gapChainOut_snoc
#print axioms ordinary_hop_chunks
#print axioms ordinary_hop_bits
#print axioms first_hop_source
#print axioms ordinary_hop_source

end BB6.Agent39Q0148Carry
