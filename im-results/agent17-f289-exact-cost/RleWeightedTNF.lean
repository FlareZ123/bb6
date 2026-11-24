import RleCoverageGraft
import FirstHolePath

set_option maxRecDepth 12000
set_option maxHeartbeats 0

namespace BB6.Agent17.F289Coverage
open BB6Coverage BB6.Agent13BlankDelay BB6.Agent47WeightedHalt BB6.Agent8TNFPath

/-- For a literal single-halt machine, the huge exact halting witness
identifies the authentic last hole without evaluating its raw execution. -/
theorem singleHalt_lastHole_witness (m : Machine) (hole : Slot) (n : Nat)
    (honly : ∀ s, m s = none ↔ s = hole)
    (hscore : HaltsAfter m n) :
    ∃ c, knownRun (forgetHaltRows m) n = some c ∧
      readSlot c = hole ∧
      (forgetHaltRows m) (readSlot c) = none ∧
      (∀ s, s ≠ readSlot c → ∃ mv, (forgetHaltRows m) s = some (some mv)) := by
  have hd : HaltsAfter (weightedTNFDefaultCompletion (forgetHaltRows m)) n := by
    rw [forgetHaltRows_defaultCompletion]
    exact hscore
  obtain ⟨c, hr, hu⟩ := (weightedTNF_halt_iff_firstHole (forgetHaltRows m)
    (forgetHaltRows_noAssignedHalt m) n).mp hd
  have hslot : readSlot c = hole := by
    apply (honly (readSlot c)).mp
    cases hs : m (readSlot c) with
    | none => rfl
    | some mv => simp [forgetHaltRows, hs] at hu
  refine ⟨c, hr, hslot, hu, ?_⟩
  intro s hne
  cases hs : m s with
  | none => exact False.elim (hne (((honly s).mp hs).trans hslot.symm))
  | some mv => exact ⟨mv, by simp [forgetHaltRows, hs]⟩

/-- A proof of the actual lastHole constructor, with its weight evaluated
on the fully specified halt child. There is no long raw-run reduction. -/
theorem singleHalt_lastHole (B : Nat) (m : Machine) (hole : Slot) (n : Nat)
    (hroot : m initialSlot = some ⟨true, true, 1⟩)
    (honly : ∀ s, m s = none ↔ s = hole)
    (hscore : HaltsAfter m n)
    (hweight : ∀ d ∈ possibleDelays (refine (forgetHaltRows m) hole none) 0,
      d + n + 1 ≤ B) :
    Nonempty (WeightedTNFCertificate B (forgetHaltRows m) 6) := by
  obtain ⟨c, hr, hslot, hu, hrest⟩ := singleHalt_lastHole_witness m hole n honly hscore
  refine ⟨.lastHole (forgetHaltRows_root m hroot) (forgetHaltRows_tnfSupport m)
    (by decide) hr hu hrest ?_⟩
  simpa only [hslot] using hweight

/-- The same proof provides a directly composable data-level TNF leaf. -/
def singleHalt_weightedLeaf (B : Nat) (m : Machine) (hole : Slot) (n : Nat)
    (hroot : m initialSlot = some ⟨true, true, 1⟩)
    (honly : ∀ s, m s = none ↔ s = hole)
    (hscore : HaltsAfter m n)
    (hweight : ∀ d ∈ possibleDelays (refine (forgetHaltRows m) hole none) 0,
      d + n + 1 ≤ B) :
    WeightedTNFCertificate B (forgetHaltRows m) 6 :=
  .weightedLeaf (forgetHaltRows_root m hroot) (forgetHaltRows_tnfSupport m)
    (forgetHaltRows_noAssignedHalt m) (by
      obtain ⟨cert⟩ := singleHalt_lastHole B m hole n hroot honly hscore hweight
      exact cert.sound)

def path_1 : List (Nat × Slot) :=
  [(1,(1,false)),(2,(2,false)),(3,(3,true)),(4,(4,true)),(5,(5,false)),
   (8,(2,true)),(9,(1,true)),(18,(0,true)),(19,(4,false)),(21,(3,false))]

def path_2 : List (Nat × Slot) :=
  [(1,(1,false)),(2,(2,false)),(3,(3,false)),(4,(4,false)),(6,(2,true)),
   (7,(0,true)),(8,(5,false)),(11,(1,true)),(12,(4,true)),(23,(3,true))]

theorem path_1_checked :
    pathCheck expectedRLE_1 BB6.CoverageAdapter.firstOneCylinder 2 path_1 = true := by decide

theorem path_2_checked :
    pathCheck expectedRLE_2 BB6.CoverageAdapter.firstOneCylinder 2 path_2 = true := by decide

theorem path_1_reachable : FirstHolePath (forgetHaltRows expectedRLE_1) 6 :=
  checked_from_root _ _ path_1_checked

theorem path_2_reachable : FirstHolePath (forgetHaltRows expectedRLE_2) 6 :=
  checked_from_root _ _ path_2_checked

theorem only_halt_1 (s : Slot) : expectedRLE_1 s = none ↔ s = (5,true) := by
  rcases s with ⟨q,b⟩
  have h : ∀ q : Fin 6, ∀ b : Bool, expectedRLE_1 (q,b) = none ↔ (q,b) = (5,true) := by decide
  exact h q b

theorem only_halt_2 (s : Slot) : expectedRLE_2 s = none ↔ s = (5,true) := by
  rcases s with ⟨q,b⟩
  have h : ∀ q : Fin 6, ∀ b : Bool, expectedRLE_2 (q,b) = none ↔ (q,b) = (5,true) := by decide
  exact h q b

theorem possible_delays_1 :
    possibleDelays (refine (forgetHaltRows expectedRLE_1) (5,true) none) 0 = [0,1,2] := by decide

theorem possible_delays_2 :
    possibleDelays (refine (forgetHaltRows expectedRLE_2) (5,true) none) 0 = [0] := by decide

def f289_1_weighted_leaf (B : Nat)
    (hB : 932242535661307148726923126800831715518673957231 ≤ B) :
    WeightedTNFCertificate B (forgetHaltRows expectedRLE_1) 6 := by
  apply singleHalt_weightedLeaf B expectedRLE_1 (5,true)
    932242535661307148726923126800831715518673957228 rfl only_halt_1 literal_score_1
  intro d hd
  rw [possible_delays_1] at hd
  simp at hd
  omega

def f289_2_weighted_leaf (B : Nat)
    (hB : 111579188581812927653348117002306046024821208051411619955580898884568782 ≤ B) :
    WeightedTNFCertificate B (forgetHaltRows expectedRLE_2) 6 := by
  apply singleHalt_weightedLeaf B expectedRLE_2 (5,true)
    111579188581812927653348117002306046024821208051411619955580898884568781 rfl only_halt_2 literal_score_2
  intro d hd
  rw [possible_delays_2] at hd
  simp at hd
  omega

/-- Exact minimum acceptable weighted bounds, including the realizable
incoming zero-prefix delays and the final halt query. -/
theorem f289_1_weighted_iff (B : Nat) :
    (∀ m, compatible (forgetHaltRows expectedRLE_1) m → WeightedBound B m) ↔
      932242535661307148726923126800831715518673957231 ≤ B := by
  constructor
  · intro h
    have hc := weightedTNFDefaultCompletion_compatible (forgetHaltRows expectedRLE_1)
    rw [forgetHaltRows_defaultCompletion] at hc
    have hd : 2 ∈ delays (zeroNext expectedRLE_1) 0 := by decide
    have hb := h expectedRLE_1 hc _ 2 literal_score_1 hd
    omega
  · intro hb
    exact (f289_1_weighted_leaf B hb).sound

theorem f289_2_weighted_iff (B : Nat) :
    (∀ m, compatible (forgetHaltRows expectedRLE_2) m → WeightedBound B m) ↔
      111579188581812927653348117002306046024821208051411619955580898884568782 ≤ B := by
  constructor
  · intro h
    have hc := weightedTNFDefaultCompletion_compatible (forgetHaltRows expectedRLE_2)
    rw [forgetHaltRows_defaultCompletion] at hc
    have hd : 0 ∈ delays (zeroNext expectedRLE_2) 0 := by decide
    have hb := h expectedRLE_2 hc _ 0 literal_score_2 hd
    omega
  · intro hb
    exact (f289_2_weighted_leaf B hb).sound

#print axioms singleHalt_lastHole_witness
#print axioms singleHalt_lastHole
#print axioms singleHalt_weightedLeaf
#print axioms path_1_reachable
#print axioms path_2_reachable
#print axioms possible_delays_1
#print axioms possible_delays_2
#print axioms f289_1_weighted_leaf
#print axioms f289_2_weighted_leaf
#print axioms f289_1_weighted_iff
#print axioms f289_2_weighted_iff
end BB6.Agent17.F289Coverage
