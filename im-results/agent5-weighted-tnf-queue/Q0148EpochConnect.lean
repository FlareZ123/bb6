import Q0148BoundaryAlgebra
import Q0148ResetToTrain

namespace BB6.Agent5Q0148EpochConnect
open BB6Coverage BB6Coverage.Agent31Pump BB6Coverage.Agent13PackedZipper
open BB6.Agent5PackedSweep BB6.Agent5Q0148BoundarySweep BB6.Agent5Q0148GapInvariant
open BB6.Agent5Q0148PackedBoundary BB6.Agent5Q0148BoundaryAlgebra BB6.Agent39Q0148Carry

set_option maxHeartbeats 400000
set_option maxRecDepth 100000

theorem aRun_eq_rep (n : Nat) : aRun n = List.replicate n .alternating := by
  induction n with
  | zero => rfl
  | succ n ih => simp [aRun,List.replicate_succ,ih]

theorem evenBlocks_eq_blocks (xs : List Nat) : evenBlocks xs = blocks xs := by
  induction xs with
  | nil => rfl
  | cons x xs ih => simp [evenBlocks,blocks,aRun_eq_rep,ih,List.append_assoc]

theorem gapChain_eq_priorChunks (xs : List Nat) : gapChain xs = priorChunks xs := by
  induction xs with
  | nil => rfl
  | cons x xs ih => simp [gapChain,priorChunks,aRun_eq_rep,ih]

theorem twoPad_eq_rep (n : Nat) : twoPad n = List.replicate (2*n) false := by
  induction n with
  | zero => rfl
  | succ n ih => simp [twoPad,ih,Nat.mul_succ,List.replicate_succ]

theorem leftPad_eq_rep (n : Nat) : leftPad n = List.replicate (2*n+1) false := by
  simp [leftPad,twoPad_eq_rep,List.replicate_succ]

def resetA1Frame (us : List Nat) (n : Nat) : Z0 :=
  ⟨4,[true,false] ++ inputBits (a1Input us.reverse n) ++
    [false,false,false,false] ++ leftPad (a1FutureMarkers us).length,
    [false,true,false,false,false]⟩

def resetA3Frame (us : List Nat) (n : Nat) : Z0 :=
  ⟨4,[true,false] ++ inputBits (a3Input (us.reverse ++ [n])) ++
    [false,false,false,false,false,false,false,false] ++ leftPad (a3FutureMarkers us).length,
    [false,true,false,false,false,false,false,false]⟩

def rightTail (g : GapState) : List Bool := if g.b=0 then [true,false] else [true,false,false]

theorem resetA1Packed (g : GapState) (hg : valid g) (hb : g.b = 0) :
    encode0 (resetA1Frame (resetUs g) (resetN g)) = boundary g := by
  have h := reset_blocks g hg
  have hc : a1Input (resetUs g).reverse (resetN g) = boundaryChunks g := by
    simp [a1Input,evenBlocks_eq_blocks,h,boundaryChunks,hb]
  rw [resetA1Frame,hc,leftPad_eq_rep]
  have hp := padded_boundary g ((2*(a1FutureMarkers (resetUs g)).length+1)+4) 2
  simpa only [List.replicate_succ,List.replicate_zero,List.append_assoc,List.cons_append,List.nil_append] using hp

theorem resetA3Packed (g : GapState) (hg : valid g) (hb : g.b = 1) :
    encode0 (resetA3Frame (resetUs g) (resetN g)) = boundary g := by
  have h := reset_blocks g hg
  have hc : a3Input ((resetUs g).reverse ++ [resetN g]) = boundaryChunks g := by
    simp [a3Input,evenBlocks_eq_blocks,h,boundaryChunks,hb,aRun_eq_rep]
  rw [resetA3Frame,hc,leftPad_eq_rep]
  have hp := padded_boundary g ((2*(a3FutureMarkers (resetUs g)).length+1)+8) 5
  simpa only [List.replicate_succ,List.replicate_zero,List.append_assoc,List.cons_append,List.nil_append] using hp

theorem future_a1 (g : GapState) (hb : g.b = 0) :
    a1FutureMarkers (resetUs g) = future g.b g.xs := by
  rw [reset_future]; simp [a1FutureMarkers,hb]

theorem future_a3 (g : GapState) (hb : g.b = 1) :
    a3FutureMarkers (resetUs g) = future g.b g.xs := by
  rw [reset_future]; simp [a3FutureMarkers,hb]

def Reset1 : Prop := ∀ us n, ∃ k, 0 < k ∧
    run0 p k (resetA1Frame us n) =
      some (firstMarkerState (2*n+1) (a1FutureMarkers us) [] [true,false])

def Reset3 : Prop := ∀ us n, ∃ k, 0 < k ∧
    run0 p k (resetA3Frame us n) =
      some (firstMarkerState (2*n+1) (a3FutureMarkers us) [] [true,false,false])

theorem packedReset (h1 : Reset1) (h3 : Reset3) (g : GapState) (hg : valid g) :
    ∃ k, 0 < k ∧ runP p k (boundary g) =
      some (encode0 (firstMarkerState (2*resetN g+1) (future g.b g.xs) [] (rightTail g))) := by
  by_cases hb : g.b=0
  · obtain ⟨k,hk,hs⟩ := h1 (resetUs g) (resetN g)
    have hp := packed_of_run0 hs
    rw [resetA1Packed g hg hb, future_a1 g hb] at hp
    exact ⟨k,hk,by simpa [rightTail,hb] using hp⟩
  · have hb' : g.b=1 := by have := hg.1; omega
    obtain ⟨k,hk,hs⟩ := h3 (resetUs g) (resetN g)
    have hp := packed_of_run0 hs
    rw [resetA3Packed g hg hb',future_a3 g hb'] at hp
    exact ⟨k,hk,by simpa [rightTail,hb] using hp⟩

def params (g : GapState) : List Nat := g.xs.reverse.map (fun u => 2*(u-1))

theorem future_reverse (g : GapState) : (future g.b g.xs).reverse = 0 :: params (next g) := by
  rw [future_eq]
  simp [params,next,List.reverse_append,List.map_reverse]

theorem highPacked (g : GapState) (hg : valid g) (hb : g.b=1)
    (ix : HopIndex) (hj : ix.j=0) (hp : ix.prior=params g) (hf : ix.far=0) (R : List Bool)
    (hR : R=[true,false] ∨ R=[true,false,false]) :
    encode0 (markerState ix [] [] R) = boundary g := by
  have he : aRun (ix.j+2) ++ gapChain (ix.prior++[ix.far]) = boundaryChunks g := by
    rw [hj,hp,hf,gapChain_eq_priorChunks,priorChunks_append,boundary_splice g hg]
    simp [params,hb,aRun_eq_rep,priorChunks,List.append_assoc]
  unfold markerState
  rw [he]
  rcases hR with rfl | rfl
  · simpa [leftPad,twoPad,rightMarkers,List.append_assoc] using padded_boundary g 1 0
  · simpa [leftPad,twoPad,rightMarkers,List.append_assoc] using padded_boundary g 1 1

theorem lowPacked (g : GapState) (hg : valid g) (hb : g.b=0)
    (R : List Bool) (hR : R=[true,false] ∨ R=[true,false,false]) :
    encode0 (lowTerminal 0 (params g) [] R) = boundary g := by
  have he : aRun (0+2) ++ gapChain (params g) ++ [.separatedMarker] = boundaryChunks g := by
    rw [gapChain_eq_priorChunks,boundary_splice g hg]
    simp [params,hb,aRun_eq_rep,List.append_assoc]
  unfold lowTerminal
  rw [he]
  rcases hR with rfl | rfl
  · simpa [leftPad,twoPad,List.append_assoc] using padded_boundary g 1 0
  · simpa [leftPad,twoPad,List.append_assoc] using padded_boundary g 1 1

theorem rightTail_form (g : GapState) : rightTail g=[true,false] ∨ rightTail g=[true,false,false] := by
  by_cases h : g.b=0 <;> simp [rightTail,h]

-- Endpoint identities for arbitrary source marker list.
theorem end_order (ix : HopIndex) (ns : List Nat) :
    (trainEnd ix ns).j :: (trainEnd ix ns).prior = (ix.j::ns).reverse ++ ix.prior := by
  induction ns generalizing ix with
  | nil => simp [trainEnd]
  | cons n ns ih => simpa [trainEnd,nextIndex,List.reverse_cons,List.append_assoc] using ih (nextIndex ix n)

theorem end_far (ix : HopIndex) (ns : List Nat) : (trainEnd ix ns).far = ix.far-ns.length := by
  induction ns generalizing ix with
  | nil => rfl
  | cons n ns ih => simpa [trainEnd,nextIndex,Nat.sub_sub,List.length_cons,Nat.add_comm] using ih (nextIndex ix n)

def HighTrain : Prop := ∀ n ns R, ∃ k,
    run0 p k (firstMarkerState (ns.length+1) (n::ns) [] R) =
      some (markerState (trainEnd (firstIndex (ns.length+1) n) ns) [] [] R)

def LowTrain : Prop := ∀ n mid u v R, ∃ k,
    run0 p k (firstMarkerState (mid.length+1) (n::(mid++[u,v])) [] R) =
      some (lowTerminal v (u::(trainEnd (firstIndex (mid.length+1) n) mid).j::
        (trainEnd (firstIndex (mid.length+1) n) mid).prior) [] R)

theorem packedEpoch (r1 : Reset1) (r3 : Reset3) (high : HighTrain) (low : LowTrain)
    (g : GapState) (hg : valid g) :
    ∃ k, 0 < k ∧ runP p k (boundary g) = some (boundary (next g)) := by
  obtain ⟨k,hk,hreset⟩ := packedReset r1 r3 g hg
  obtain ⟨n,mid,u,hlist⟩ := future_split g hg
  have hrev := future_reverse g
  rw [hlist] at hrev
  have hn := next_valid g hg
  have htail := rightTail_form g
  have hh := future_height g.b g.r g.xs hg
  rcases hh with ⟨hb,hh⟩ | ⟨hb,hh⟩
  · let ns := mid++[u,0]
    have hj : 2*resetN g+1=ns.length+1 := by
      rw [hlist] at hh
      simpa [resetN,ns,Nat.add_comm] using hh
    rw [hlist,hj] at hreset
    obtain ⟨t,ht⟩ := high n ns (rightTail g)
    have hpt := packed_of_run0 ht
    let ix := trainEnd (firstIndex (ns.length+1) n) ns
    have he : ix.j::ix.prior = 0::params (next g) := by
      have ho := end_order (firstIndex (ns.length+1) n) ns
      simpa [ix,firstIndex,ns,hrev] using ho
    have hj' : ix.j=0 := (List.cons.inj he).1
    have hp : ix.prior=params (next g) := (List.cons.inj he).2
    have hf : ix.far=0 := by simp [ix,end_far,firstIndex]
    have hout := highPacked (next g) hn hb ix hj' hp hf _ htail
    rw [show trainEnd (firstIndex (ns.length+1) n) ns = ix from rfl,hout] at hpt
    exact ⟨k+t,by omega,joinP hreset hpt⟩
  · have hj : 2*resetN g+1=mid.length+1 := by
      rw [hlist] at hh
      simp [List.length_append] at hh
      unfold resetN
      omega
    rw [hlist,hj] at hreset
    obtain ⟨t,ht⟩ := low n mid u 0 (rightTail g)
    have hpt := packed_of_run0 ht
    let ix := trainEnd (firstIndex (mid.length+1) n) mid
    have ho : ix.j::ix.prior = (n::mid).reverse := by
      simpa [ix,firstIndex] using end_order (firstIndex (mid.length+1) n) mid
    have hp : u::ix.j::ix.prior=params (next g) := by
      rw [ho]
      simpa [List.reverse_append,List.reverse_cons,List.append_assoc] using hrev
    have hout := lowPacked (next g) hn hb _ htail
    rw [show trainEnd (firstIndex (mid.length+1) n) mid = ix from rfl,hp,hout] at hpt
    exact ⟨k+t,by omega,joinP hreset hpt⟩

theorem cover_of_source_train (r1 : Reset1) (r3 : Reset3) (high : HighTrain) (low : LowTrain) :
    Cover NeverHalts p := cover_of_epoch (packedEpoch r1 r3 high low)

#print axioms cover_of_source_train
end BB6.Agent5Q0148EpochConnect
