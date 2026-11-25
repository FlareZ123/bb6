import Raw108LongRead
import TNFPilot
set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace BB6.Agent10Raw108Long
open BB6Coverage BB6.Agent13BlankDelay BB6.Agent8TNFPath
open BB6Coverage.Agent10ZipAudit
open BB6.Agent50TNFPilot

abbrev raw108Parent : PartialMachine :=
  refine (pathEnd root 2 (path.take 4)).1 (4,true) (some ⟨true,false,1⟩)

def longest : Machine :=
  weightedTNFDefaultCompletion (refine (table kid22) (2,true) none)

theorem longest_compatible : compatible raw108Parent longest := by
  have h : ∀ q : Fin 6, ∀ b : Bool,
      raw108Parent (q,b) = none ∨
      raw108Parent (q,b) = some (longest (q,b)) := by decide
  intro s v hv
  rcases s with ⟨q,b⟩
  rcases h q b with hn | he
  · rw [hn] at hv; contradiction
  · rw [he] at hv; exact Option.some.inj hv

theorem longest_halts : HaltsAfter longest 4136174 := by
  have hr : (knownRun (table kid22) 4136174).map readSlot = some (2,true) :=
    (zipRead_eq _ _).symm.trans read_kid22
  have hh : table kid22 (2,true) = none := by decide
  have hm : compatible (refine (table kid22) (2,true) none) longest :=
    weightedTNFDefaultCompletion_compatible _
  cases hc : knownRun (table kid22) 4136174 with
  | none => simp [hc] at hr
  | some c =>
    have hs : readSlot c = (2,true) := by simpa [hc] using hr
    exact first_hole_halts (table kid22) 4136174 c hc
      (by simpa only [hs] using hh) longest (by simpa only [hs] using hm)

theorem longest_delays : delays (zeroNext longest) 0 = [0] := by decide

/-- Every weighted universal bound for raw108 is at least the actually
    attained score of the longest presently known halting continuation. -/
theorem raw108_lower (B : Nat)
    (h : ∀ m, compatible raw108Parent m → WeightedBound B m) :
    4136175 ≤ B := by
  have hd : 0 ∈ delays (zeroNext longest) 0 := by rw [longest_delays]; simp
  exact h longest longest_compatible 4136174 0 longest_halts hd

#print axioms longest_halts
#print axioms raw108_lower
end BB6.Agent10Raw108Long
