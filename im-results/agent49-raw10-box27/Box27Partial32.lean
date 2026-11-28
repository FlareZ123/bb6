import Box27D0FastPumps
import Box27D0D1FAR
import Box27D17Parent

set_option maxRecDepth 100000
set_option maxHeartbeats 0

/-!
A disjoint source-domain cut of exactly 160 of the 500
(D0,D1) rows of the authentic Raw10 Box27.

  * D0 in {0,5,7,9,10}: all 25 values of D1 (125 pairs);
  * 34 further explicit D0/D1 pairs: all nonhalting;
  * D0=14,D1=17: all 25 E0 codes, sharp weighted maximum 255.

There are six other unconstrained slots for each pair; hence 160 * 25^6
= 39,062,500,000 represented ordinary complete machine tables,
exactly 32% of the 20 * 25^7 parent mass.

The mathematical claim below is a parent-relative conditional bound;
it is not the global BB(6) upper bound.
-/
namespace BB6.Agent49.Box27Partial32
open BB6Coverage BB6.Agent49Box BB6.Agent49BoxBridge
open BB6.Agent13.Box17 (decode)
open BB6.Agent49

def sourceD0 : List (Fin 25) :=
  [0,2,3,4,5,6,7,9,10,12,14,16,17,18,19,20,21,22,23,24]

def covered (d0 d1 : Fin 25) : Bool :=
  decide (d0 ∈ Box27D0FastPumps.fastCodes ∨
    (d0,d1) ∈ Box27D0D1FAR.pairs ∨ (d0=14 ∧ d1=17))

/-- The exact 160 distinct, source-admissible transition pairs. -/
theorem coveredPairs :
    (sourceD0.flatMap (fun d0 =>
      (List.finRange 25).filter (covered d0))).length = 160 := by decide

/-- Every listed fixed-D0 transition really lies in original Box27. -/
theorem sourceD0eq :
    raw10Remainder[27]! (3,false) = sourceD0.map decode := by decide

theorem sourcePair (m : Machine) (hm : Fits raw10Remainder[27]! m) :
    ∃ d0 : Fin 25, d0 ∈ sourceD0 ∧ m (3,false) = decode d0 := by
  have hd := hm (3,false)
  rw [sourceD0eq] at hd
  obtain ⟨d0,hd0,hval⟩ := List.mem_map.mp hd
  exact ⟨d0,hd0,hval.symm⟩

/-- All 160 certified (D0,D1) pairs have a uniform weighted 255 bound. -/
theorem bound255 (m : Machine) (hm : Fits raw10Remainder[27]! m)
    (d0 d1 : Fin 25)
    (hd0 : m (3,false) = decode d0)
    (hd1 : m (3,true) = decode d1)
    (hc : covered d0 d1 = true) : WeightedBound 255 m := by
  have h : d0 ∈ Box27D0FastPumps.fastCodes ∨
      (d0,d1) ∈ Box27D0D1FAR.pairs ∨ (d0=14 ∧ d1=17) :=
    of_decide_eq_true hc
  rcases h with hs|hp|⟨ha,hb⟩
  · exact Box27D0FastPumps.source_fast_bound m hm d0 hd0 hs
  · exact Box27D0D1FAR.source_bound 255 m hm d0 d1 hd0 hd1 hp
  · subst d0
    subst d1
    exact Box27D17Parent.bound255 m hm hd0 hd1

/-- The fixed-D0/D1 E0=24 witness certifies optimality of 255
    on the new 32%-of-Box27 cut. -/
theorem attainer_covered :
    covered 14 17 = true := by decide

theorem sharp (B : Nat) :
    (∀ m, Fits raw10Remainder[27]! m →
      ∀ d0 d1 : Fin 25,
        m (3,false) = decode d0 →
        m (3,true) = decode d1 →
        covered d0 d1 = true → WeightedBound B m) ↔
      255 ≤ B := by
  constructor
  · intro h
    have hd : 0 ∈ BB6.Agent13BlankDelay.delays
        (BB6.Agent13BlankDelay.zeroNext Box27Slice24.attainer) 0 := by decide
    have hh := h Box27Slice24.attainer Box27D17Parent.attainer_fits
      14 17 Box27D17Parent.attainer_d0 Box27D17Parent.attainer_d1
      attainer_covered 254 0 Box27Slice24.attainer_halts hd
    omega
  · intro h m hm d0 d1 hd0 hd1 hc k d hk hd
    have hb := bound255 m hm d0 d1 hd0 hd1 hc k d hk hd
    omega

#print axioms coveredPairs
#print axioms sourceD0eq
#print axioms sourcePair
#print axioms bound255
#print axioms sharp
end BB6.Agent49.Box27Partial32
