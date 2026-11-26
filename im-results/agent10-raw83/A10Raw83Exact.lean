import A10Raw83Data
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace BB6.Agent10Raw83
open BB6Coverage BB6.Agent13BlankDelay BB6.Agent8TNFPath
open BB6Coverage.Agent10ZipAudit BB6.Agent50TNFPilot

def witnessPartial : PartialMachine :=
  refine (refine (refine parent (0,true) (some ⟨false,false,4⟩))
    (4,false) (some ⟨false,true,5⟩))
    (5,false) (some ⟨false,false,1⟩)

def longest : Machine :=
  weightedTNFDefaultCompletion (refine witnessPartial (2,true) none)

theorem longest_compatible : compatible parent longest := by
  have h : ∀ q : Fin 6, ∀ b : Bool,
      parent (q,b) = none ∨ parent (q,b) = some (longest (q,b)) := by decide
  intro s v hv
  rcases s with ⟨q,b⟩
  rcases h q b with hn | he
  · rw [hn] at hv; contradiction
  · rw [he] at hv; exact Option.some.inj hv

theorem longest_halts : HaltsAfter longest 513 := by
  have hz : zipRead witnessPartial 513 = some (2,true) := by rfl
  have hr : (knownRun witnessPartial 513).map readSlot = some (2,true) :=
    (zipRead_eq _ _).symm.trans hz
  have hh : witnessPartial (2,true) = none := by decide
  have hm : compatible (refine witnessPartial (2,true) none) longest :=
    weightedTNFDefaultCompletion_compatible _
  cases hc : knownRun witnessPartial 513 with
  | none => simp [hc] at hr
  | some c =>
    have hs : readSlot c = (2,true) := by simpa [hc] using hr
    exact first_hole_halts witnessPartial 513 c hc
      (by simpa only [hs] using hh) longest (by simpa only [hs] using hm)

theorem longest_delays : delays (zeroNext longest) 0 = [0] := by decide

theorem exact_bound (B : Nat) :
    (∀ m, compatible parent m → WeightedBound B m) ↔ 514 ≤ B := by
  constructor
  · intro h
    have hd : 0 ∈ delays (zeroNext longest) 0 := by rw [longest_delays]; simp
    exact h longest longest_compatible 513 0 longest_halts hd
  · intro h m hm n d hn hd
    exact Nat.le_trans (all_completions m hm n d hn hd) h

#print axioms longest_halts
#print axioms exact_bound
end BB6.Agent10Raw83
