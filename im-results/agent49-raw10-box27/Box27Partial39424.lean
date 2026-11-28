import Box27D0FastPumps
import Box27D0D1FAR
import Box27D0D1FARExt
import Box27D0E0FAR
import Box27D0D1E0FAR
import Box27D17Parent

set_option maxRecDepth 100000
set_option maxHeartbeats 0

/-!
An exact *source-relative* 39.424%-of-Box27 partial classification,
composed from five explicit disjoint/overlapping but harmless witness sets.
No double-counting: 4928 distinct allowed (D0,D1,E0) triples are
certified at uniform weighted upper bound 255. Each triple leaves five
original slots unrestricted (A1,B1,E1,F0,F1), hence represents 25^5
complete machines. Total mass = 48,125,000,000 of the original
122,070,312,500 complete six-state two-symbol Box27 machines.
The E0=24,D0=14,D1=17 witness attains 255, proving sharpness.
This is NOT a global six-state Busy Beaver bound.
-/
namespace BB6.Agent49.Box27Partial39424
open BB6Coverage BB6.Agent13BlankDelay BB6.Agent49Box BB6.Agent49BoxBridge
open BB6.Agent13.Box17 (decode)
open BB6.Agent49

def sourceD0 : List (Fin 25) :=
  [0,2,3,4,5,6,7,9,10,12,14,16,17,18,19,20,21,22,23,24]

def covered (d0 d1 e0 : Fin 25) : Bool :=
  decide (d0 ∈ Box27D0FastPumps.fastCodes ∨
    (d0,d1) ∈ Box27D0D1FAR.pairs ∨
    (d0,d1) ∈ Box27D0D1FARExt.pairs ∨
    (d0,e0) ∈ Box27D0E0FAR.pairs ∨
    (d0,d1,e0) ∈ Box27D0D1E0FAR.keys ∨
    (d0=14 ∧ d1=17))

/-- Exact finite cardinality of disjoint covered (D0,D1,E0) triples. -/
theorem coveredTriples :
    (sourceD0.flatMap (fun d0 =>
      (List.finRange 25).flatMap (fun d1 =>
        (List.finRange 25).filter (covered d0 d1)))).length = 4928 := by decide

theorem coveredMass : 4928 * 25^5 = 48125000000 := by decide
theorem sourceMass : 20 * 25^7 = 122070312500 := by decide

theorem sourceD0eq :
    raw10Remainder[27]! (3,false) = sourceD0.map decode := by decide

theorem sourcePair (m : Machine) (hm : Fits raw10Remainder[27]! m) :
    ∃ d0 : Fin 25, d0 ∈ sourceD0 ∧ m (3,false) = decode d0 := by
  have hd := hm (3,false)
  rw [sourceD0eq] at hd
  obtain ⟨d0,hd0,hval⟩ := List.mem_map.mp hd
  exact ⟨d0,hd0,hval.symm⟩

/-- Unified bound for all 4928 triples, on the authentic original box. -/
theorem bound255 (m : Machine)
    (hm : Fits raw10Remainder[27]! m)
    (d0 d1 e0 : Fin 25)
    (hd0 : m (3,false) = decode d0)
    (hd1 : m (3,true) = decode d1)
    (he0 : m (4,false) = decode e0)
    (hc : covered d0 d1 e0 = true) : WeightedBound 255 m := by
  have h : d0 ∈ Box27D0FastPumps.fastCodes ∨
      (d0,d1) ∈ Box27D0D1FAR.pairs ∨
      (d0,d1) ∈ Box27D0D1FARExt.pairs ∨
      (d0,e0) ∈ Box27D0E0FAR.pairs ∨
      (d0,d1,e0) ∈ Box27D0D1E0FAR.keys ∨
      (d0=14 ∧ d1=17) := of_decide_eq_true hc
  rcases h with hs|hp|hx|he|ht|⟨ha,hb⟩
  · exact Box27D0FastPumps.source_fast_bound m hm d0 hd0 hs
  · exact Box27D0D1FAR.source_bound 255 m hm d0 d1 hd0 hd1 hp
  · exact Box27D0D1FARExt.source_bound 255 m hm d0 d1 hd0 hd1 hx
  · exact Box27D0E0FAR.source_bound 255 m hm d0 e0 hd0 he0 he
  · exact Box27D0D1E0FAR.source_bound 255 m hm d0 d1 e0 hd0 hd1 he0 ht
  · subst d0
    subst d1
    exact Box27D17Parent.bound255 m hm hd0 hd1

theorem attainer_covered : covered 14 17 24 = true := by decide

/-- The exact optimum over the 48.125-billion-table union is weighted 255. -/
theorem exact_weighted (B : Nat) :
    (∀ m, Fits raw10Remainder[27]! m →
      ∀ d0 d1 e0 : Fin 25,
        m (3,false) = decode d0 →
        m (3,true) = decode d1 →
        m (4,false) = decode e0 →
        covered d0 d1 e0 = true → WeightedBound B m) ↔
      255 ≤ B := by
  constructor
  · intro h
    have hd : 0 ∈ BB6.Agent13BlankDelay.delays
        (BB6.Agent13BlankDelay.zeroNext Box27Slice24.attainer) 0 := by decide
    have hh := h Box27Slice24.attainer Box27D17Parent.attainer_fits
      14 17 24 Box27D17Parent.attainer_d0 Box27D17Parent.attainer_d1
      (by decide) attainer_covered 254 0 Box27Slice24.attainer_halts hd
    omega
  · intro h m hm d0 d1 e0 hd0 hd1 he0 hc k d hk hd
    have hb := bound255 m hm d0 d1 e0 hd0 hd1 he0 hc k d hk hd
    omega

#print axioms coveredTriples
#print axioms coveredMass
#print axioms sourceMass
#print axioms sourcePair
#print axioms bound255
#print axioms exact_weighted
end BB6.Agent49.Box27Partial39424
