import Raw108LERead
import TNFPilot
set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace BB6.Agent10Raw108LEFast
open BB6Coverage BB6.Agent13BlankDelay BB6.Agent8TNFPath
open BB6Coverage.Agent10ZipAudit
open BB6.Agent50TNFPilot

abbrev leParent : PartialMachine :=
  refine (refine (pathEnd root 2 (path.take 4)).1 (4,true) (some ⟨true,false,1⟩))
    (1,true) (some ⟨false,false,4⟩)

def longestLE : Machine := weightedTNFDefaultCompletion (refine (table false) (5,true) none)

theorem longestLE_compatible : compatible leParent longestLE := by
  have h : ∀ q : Fin 6, ∀ b : Bool,
      leParent (q,b) = none ∨
      leParent (q,b) = some (longestLE (q,b)) := by decide
  intro s v hv
  rcases s with ⟨q,b⟩
  rcases h q b with hn | he
  · rw [hn] at hv; contradiction
  · rw [he] at hv; exact Option.some.inj hv

theorem longestLE_halts : HaltsAfter longestLE 192167 := by
  have hr : (knownRun (table false) 192167).map readSlot = some (5,true) :=
    (zipRead_eq _ _).symm.trans readA
  have hh : table false (5,true) = none := by decide
  have hm : compatible (refine (table false) (5,true) none) longestLE :=
    weightedTNFDefaultCompletion_compatible _
  cases hc : knownRun (table false) 192167 with
  | none => simp [hc] at hr
  | some c =>
    have hs : readSlot c = (5,true) := by simpa [hc] using hr
    exact first_hole_halts (table false) 192167 c hc
      (by simpa only [hs] using hh) longestLE (by simpa only [hs] using hm)

theorem longestLE_delays : delays (zeroNext longestLE) 0 = [0,1] := by decide

/-- The ordinary halter plus its admissible one-step blank delay forces the
    exact candidate weighted cutoff, rather than the unweighted cutoff. -/
theorem raw108LE_lower (B : Nat)
    (h : ∀ m, compatible leParent m → WeightedBound B m) : 192169 ≤ B := by
  have hd : 1 ∈ delays (zeroNext longestLE) 0 := by rw [longestLE_delays]; simp
  exact h longestLE longestLE_compatible 192167 1 longestLE_halts hd

#print axioms longestLE_halts
#print axioms longestLE_delays
#print axioms raw108LE_lower
end BB6.Agent10Raw108LEFast
