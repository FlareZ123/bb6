import Q0148EvenCarryOutput

/-!
# Source-level decoding of every parameterized marked E1 hop

The old left chunk word is A^(j+2) ++ tail. The exact original-source
markedHopN source gadget then becomes a new left chunk word plus the
three-state carry of tail. The theorem is UNBOUNDED in n, j and tail.
It is a local marked hop, not yet the complete far-right boundary
return, which requires induction over all remaining markers.
-/

namespace BB6.Agent39Q0148Carry
open BB6.Agent5Q0148BoundarySweep
open BB6Coverage
open BB6Coverage.Agent31Pump

set_option maxHeartbeats 0
set_option maxRecDepth 20000

/-- Shifting a leading 1 across n copies of 01 changes them to 10. -/
theorem stagger01 (n : Nat) :
    [true] ++ rep [false,true] n =
      rep [true,false] n ++ [true] := by
  induction n with
  | zero => rfl
  | succ n ih =>
      simpa [rep, List.append_assoc] using
        congrArg (fun x : List Bool => [true,false] ++ x) ih

theorem rightSubst_aRun (n : Nat) :
    rightSubst (aRun n) = rep [false,true] n := by
  induction n with
  | zero => rfl
  | succ n ih =>
      simp [aRun, rightSubst, toRight, rightOutput, rep, ih]

theorem input_aRun (n : Nat) :
    inputBits (aRun n) = rep [true,false] n := by
  induction n with
  | zero => rfl
  | succ n ih =>
      simp [aRun, inputBits, chunkBits, rep, ih]

/-- Literal 11010 marker after the staggered run. -/
theorem marker_phase (j : Nat) :
    [true,true] ++ rep [false,true] (j+2) =
      [true,true,false,true,false] ++ rep [true,false] j ++ [true] := by
  have h := congrArg
      (fun z : List Bool => [true,true,false,true,false] ++ z)
      (stagger01 j)
  have he : [true,true] ++ rep [false,true] (j+2) =
      [true,true,false,true,false,true] ++ rep [false,true] j := by
    rw [show j+2=(j+1)+1 by omega]
    simp [rep,List.append_assoc]
  calc
    [true,true] ++ rep [false,true] (j+2) =
      [true,true,false,true,false,true] ++ rep [false,true] j := he
    _ = ([true,true,false,true,false] ++ [true]) ++ rep [false,true] j := by
          rfl
    _ = [true,true,false,true,false] ++
          ([true] ++ rep [false,true] j) := by
          simp [List.append_assoc]
    _ = [true,true,false,true,false] ++
          (rep [true,false] j ++ [true]) := h
    _ = [true,true,false,true,false] ++ rep [true,false] j ++ [true] := by
          simp [List.append_assoc]

/-- The source right-continuation head prefix is a canonical left
    chunk word A^(n+2) M A^j followed by a dangling one bit.
    This is an exact two-parameter equality for all n,j. -/
theorem marked_phase (n j : Nat) :
    [true] ++ rep [false,true] (n+1) ++
      [false,true,true] ++ rep [false,true] (j+2) =
    rep [true,false] (n+2) ++
      [true,true,false,true,false] ++ rep [true,false] j ++ [true] := by
  have h1 := stagger01 (n+1)
  have h2 := marker_phase j
  have hr : rep [true,false] (n+2) =
       rep [true,false] (n+1) ++ [true,false] := by
    calc
      rep [true,false] (n+2) =
          [true,false] ++ rep [true,false] (n+1) := by
            rw [show n+2=(n+1)+1 by omega]
            rfl
      _ = rep [true,false] (n+1) ++ [true,false] :=
        (rep_snoc [true,false] (n+1)).symm
  calc
    [true] ++ rep [false,true] (n+1) ++
      [false,true,true] ++ rep [false,true] (j+2) =
        rep [true,false] (n+1) ++ [true,false] ++
          ([true,true] ++ rep [false,true] (j+2)) := by
            have ht := congrArg
              (fun w : List Bool =>
                w ++ [false,true,true] ++ rep [false,true] (j+2)) h1
            simpa [List.append_assoc] using ht
    _ = rep [true,false] (n+1) ++ [true,false] ++
          ([true,true,false,true,false] ++ rep [true,false] j ++ [true]) := by
            have ht := congrArg
              (fun w : List Bool =>
                rep [true,false] (n+1) ++ [true,false] ++ w) h2
            simpa [List.append_assoc] using ht
    _ = rep [true,false] (n+2) ++
        [true,true,false,true,false] ++ rep [true,false] j ++ [true] := by
          rw [hr]
          simp only [List.append_assoc]

/-- The complete source marked-hop left tape factors through exactly
    the existing U-state carry transducer. No assumption on tail.
    The small terminal residue is retained explicitly. -/
theorem marked_hop_bitword (n j : Nat) (tail : List LeftChunk)
    (L : List Bool) :
    [true,false,true] ++ rep [false,true] (n+1) ++
      [false,true,true] ++
      rightSubst (aRun (j+2) ++ tail) ++ L =
    [true,false] ++ inputBits
      (aRun (n+2) ++ [.separatedMarker] ++ aRun j ++
        (carryFold .one tail).1) ++
      carryBits (carryFold .one tail).2 ++ L := by
  let f := carryFold .one tail
  have hcarry : [true] ++ rightSubst tail =
      inputBits f.1 ++ carryBits f.2 := by
    simpa [f,carryBits] using carryFoldBits .one tail
  have hchunks :
      inputBits (aRun (n+2) ++ [.separatedMarker] ++ aRun j ++ f.1) =
        rep [true,false] (n+2) ++ [true,true,false,true,false] ++
          rep [true,false] j ++ inputBits f.1 := by
    rw [inputBits_append, inputBits_append, inputBits_append]
    simp [input_aRun, inputBits, chunkBits]
  have hphase := marked_phase n j
  have hp := congrArg
    (fun z : List Bool =>
      [true,false] ++ z ++ rightSubst tail ++ L) hphase
  have hc := congrArg
    (fun z : List Bool =>
      [true,false] ++ rep [true,false] (n+2) ++
        [true,true,false,true,false] ++ rep [true,false] j ++
        z ++ L) hcarry
  calc
    [true,false,true] ++ rep [false,true] (n+1) ++
      [false,true,true] ++ rightSubst (aRun (j+2) ++ tail) ++ L =
      [true,false] ++
        ([true] ++ rep [false,true] (n+1) ++
          [false,true,true] ++ rep [false,true] (j+2)) ++
        rightSubst tail ++ L := by
          simp [rightSubst_append,rightSubst_aRun,
            List.append_assoc]
    _ = [true,false] ++
        (rep [true,false] (n+2) ++ [true,true,false,true,false] ++
          rep [true,false] j ++ [true]) ++
        rightSubst tail ++ L := hp
    _ = [true,false] ++ rep [true,false] (n+2) ++
        [true,true,false,true,false] ++ rep [true,false] j ++
          (inputBits f.1 ++ carryBits f.2) ++ L := by
            simpa only [List.append_assoc] using hc
    _ = [true,false] ++ inputBits
        (aRun (n+2) ++ [.separatedMarker] ++ aRun j ++ f.1) ++
          carryBits f.2 ++ L := by
            rw [← hchunks]
            simp only [List.append_assoc]

/-- Original open-table source theorem: the exact markedHopN execution
    rewrites A^(j+2) ++ tail into A^(n+2) M A^j ++ carryFold_U(tail),
    with its residual carry bits explicit. Hence all marked hops can
    be handled by the SAME finite transducer used at the blank edge. -/
theorem marked_hop_source (n j : Nat) (tail : List LeftChunk)
    (L R : List Bool) :
    let cs := aRun (j+2) ++ tail
    let f := carryFold .one tail
    run0 p ((4 + 4 * scanCost cs) + (13 + 2*n))
      ⟨4,[true,false] ++ inputBits cs ++ [false] ++ L,
        [false,true,false] ++ rep [true,false] n ++
          [true,true,false] ++ R⟩ =
    some ⟨4,
      [true,false] ++ inputBits
        (aRun (n+2) ++ [.separatedMarker] ++ aRun j ++ f.1) ++
          carryBits f.2 ++ L,
      [false] ++ R⟩ := by
  dsimp only
  have h := markedHopN (aRun (j+2) ++ tail) n L R
  have hb := marked_hop_bitword n j tail L
  have hseq := outputRightChunks_rightSeq (aRun (j+2) ++ tail)
  rw [hseq] at h
  rw [hb] at h
  simpa only [List.append_assoc] using h

#print axioms stagger01
#print axioms rightSubst_aRun
#print axioms input_aRun
#print axioms marker_phase
#print axioms marked_phase
#print axioms marked_hop_bitword
#print axioms marked_hop_source

end BB6.Agent39Q0148Carry
