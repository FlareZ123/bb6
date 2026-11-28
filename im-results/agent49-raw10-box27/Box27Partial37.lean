import Box27D0FastPumps
import Box27D0D1FAR
import Box27D0D1FARExt
import Box27D17Parent

set_option maxRecDepth 100000
set_option maxHeartbeats 0

/-!
A source-relative cut proving a sharp weighted 255 bound for
187 disjoint (D0,D1) pairs out of 20*25 = 500 possible pairs
in exact Raw10 Box27 (37.4% by full-table counting).

  6 whole D0 codes {0,5,6,7,9,10} (150 pairs);
  27 non-overlapping ordinary FAR pairs from a list of 34
    (the other 7 have already been consumed by D0=6);
  9 additional small learned stack relations;
  1 whole D0=14,D1=17 slice with exact weighted maximum 255.

All six other transitions are unrestricted within each fixed pair.
The 187 original-code pairs represent 187 * 25^6 = 45,654,296,875
complete Turing tables. This is a source-local bound, not BB(6).
-/
namespace BB6.Agent49.Box27Partial37
open BB6Coverage BB6.Agent49Box BB6.Agent49BoxBridge
open BB6.Agent13.Box17 (decode)
open BB6.Agent49

def sourceD0 : List (Fin 25) :=
  [0,2,3,4,5,6,7,9,10,12,14,16,17,18,19,20,21,22,23,24]

def covered (d0 d1 : Fin 25) : Bool :=
  decide (d0 ∈ Box27D0FastPumps.fastCodes ∨
    (d0,d1) ∈ Box27D0D1FAR.pairs ∨
    (d0,d1) ∈ Box27D0D1FARExt.pairs ∨
    (d0=14 ∧ d1=17))

theorem coveredPairs :
    (sourceD0.flatMap (fun d0 =>
      (List.finRange 25).filter (covered d0))).length = 187 := by decide

theorem coveredMass : 187 * 25^6 = 45654296875 := by decide
theorem sourceMass : 20 * 25^7 = 122070312500 := by decide

theorem sourceD0eq :
    raw10Remainder[27]! (3,false) = sourceD0.map decode := by decide

theorem sourcePair (m : Machine) (hm : Fits raw10Remainder[27]! m) :
    ∃ d0 : Fin 25, d0 ∈ sourceD0 ∧ m (3,false) = decode d0 := by
  have hd := hm (3,false)
  rw [sourceD0eq] at hd
  obtain ⟨d0,hd0,hval⟩ := List.mem_map.mp hd
  exact ⟨d0,hd0,hval.symm⟩

theorem bound255 (m : Machine) (hm : Fits raw10Remainder[27]! m)
    (d0 d1 : Fin 25)
    (hd0 : m (3,false) = decode d0)
    (hd1 : m (3,true) = decode d1)
    (hc : covered d0 d1 = true) : WeightedBound 255 m := by
  have h : d0 ∈ Box27D0FastPumps.fastCodes ∨
      (d0,d1) ∈ Box27D0D1FAR.pairs ∨
      (d0,d1) ∈ Box27D0D1FARExt.pairs ∨
      (d0=14 ∧ d1=17) := of_decide_eq_true hc
  rcases h with hs|hp|hx|⟨ha,hb⟩
  · exact Box27D0FastPumps.source_fast_bound m hm d0 hd0 hs
  · exact Box27D0D1FAR.source_bound 255 m hm d0 d1 hd0 hd1 hp
  · exact Box27D0D1FARExt.source_bound 255 m hm d0 d1 hd0 hd1 hx
  · subst d0
    subst d1
    exact Box27D17Parent.bound255 m hm hd0 hd1

theorem attainer_covered :
    covered 14 17 = true := by decide

theorem exact_weighted (B : Nat) :
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
#print axioms coveredMass
#print axioms sourceMass
#print axioms sourcePair
#print axioms bound255
#print axioms exact_weighted
end BB6.Agent49.Box27Partial37
