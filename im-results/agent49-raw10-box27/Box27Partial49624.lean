import Box27Partial39424
import Box27D0B1FAR
import Box27D0F0FAR

set_option maxRecDepth 100000
set_option maxHeartbeats 0

/-!
Disjoint certified boxes covering 49.624% of authentic Raw10 Box27.

1. 4928 (D0,D1,E0) source triples, each with 25^5 completions;
2. 15 further (D0,B1) source pairs, each with 25^6 completions;
3. 36 further (D0,F0) source pairs, each with 25^6 completions.

No overlaps: the 15 B1 pairs fix D0 among {2,3,4}, the 36 F0 pairs
fix D0 among {21,22,23,24}, and the previous 4928 triples fix D0
outside those seven codes. Total 60,576,171,875 distinct original
six-state two-symbol Turing tables, each with WeightedBound 255.
The bound is attained by the exact E0=24 source witness.
This is a source-relative cut, not the global BB(6) maximum.
-/
namespace BB6.Agent49.Box27Partial49624
open BB6Coverage BB6.Agent13BlankDelay
open BB6.Agent49Box BB6.Agent49BoxBridge
open BB6.Agent13.Box17 (decode)
open BB6.Agent49

def b1D0 : List (Fin 25) := [2,3,4]
def f0D0 : List (Fin 25) := [21,22,23,24]

theorem b1Pairs :
    BB6.Agent49.Box27D0B1FAR.pairs.length = 15 := by decide
theorem f0Pairs :
    BB6.Agent49.Box27D0F0FAR.pairs.length = 36 := by decide

theorem b1Support :
    ∀ d0 b1 : Fin 25,
      (d0,b1) ∈ BB6.Agent49.Box27D0B1FAR.pairs → d0 ∈ b1D0 := by decide
theorem f0Support :
    ∀ d0 f0 : Fin 25,
      (d0,f0) ∈ BB6.Agent49.Box27D0F0FAR.pairs → d0 ∈ f0D0 := by decide

theorem oldDisjoint :
    ∀ d0 : Fin 25, d0 ∈ b1D0 ++ f0D0 →
      ∀ d1 e0 : Fin 25,
        BB6.Agent49.Box27Partial39424.covered d0 d1 e0 = false := by decide

theorem branchDisjoint :
    ∀ d0 b1 f0 : Fin 25,
      (d0,b1) ∈ BB6.Agent49.Box27D0B1FAR.pairs →
      (d0,f0) ∉ BB6.Agent49.Box27D0F0FAR.pairs := by decide

theorem coveredMass :
    4928 * 25^5 + 15 * 25^6 + 36 * 25^6 = 60576171875 := by decide

theorem parentMass : 20 * 25^7 = 122070312500 := by decide

def covered (d0 d1 e0 b1 f0 : Fin 25) : Bool :=
  decide (BB6.Agent49.Box27Partial39424.covered d0 d1 e0 = true ∨
    (d0,b1) ∈ BB6.Agent49.Box27D0B1FAR.pairs ∨
    (d0,f0) ∈ BB6.Agent49.Box27D0F0FAR.pairs)

theorem bound255 (m : Machine)
    (hm : Fits raw10Remainder[27]! m)
    (d0 d1 e0 b1 f0 : Fin 25)
    (hd0 : m (3,false) = decode d0)
    (hd1 : m (3,true) = decode d1)
    (he0 : m (4,false) = decode e0)
    (hb1 : m (1,true) = decode b1)
    (hf0 : m (5,false) = decode f0)
    (hc : covered d0 d1 e0 b1 f0 = true) : WeightedBound 255 m := by
  have h : BB6.Agent49.Box27Partial39424.covered d0 d1 e0 = true ∨
      (d0,b1) ∈ BB6.Agent49.Box27D0B1FAR.pairs ∨
      (d0,f0) ∈ BB6.Agent49.Box27D0F0FAR.pairs := of_decide_eq_true hc
  rcases h with ht|hb|hf
  · exact BB6.Agent49.Box27Partial39424.bound255 m hm d0 d1 e0 hd0 hd1 he0 ht
  · exact BB6.Agent49.Box27D0B1FAR.source_bound 255 m hm d0 b1 hd0 hb1 hb
  · exact BB6.Agent49.Box27D0F0FAR.source_bound 255 m hm d0 f0 hd0 hf0 hf

theorem attainer_covered : covered 14 17 24 18 3 = true := by decide

/-- The sharp weighted maximum on the 60.576-billion-table union is 255. -/
theorem exact_weighted (B : Nat) :
    (∀ m, Fits raw10Remainder[27]! m →
      ∀ d0 d1 e0 b1 f0 : Fin 25,
        m (3,false) = decode d0 →
        m (3,true) = decode d1 →
        m (4,false) = decode e0 →
        m (1,true) = decode b1 →
        m (5,false) = decode f0 →
        covered d0 d1 e0 b1 f0 = true → WeightedBound B m) ↔
      255 ≤ B := by
  constructor
  · intro h
    have hd : 0 ∈ BB6.Agent13BlankDelay.delays
        (BB6.Agent13BlankDelay.zeroNext Box27Slice24.attainer) 0 := by decide
    have hh := h Box27Slice24.attainer Box27D17Parent.attainer_fits
      14 17 24 18 3 Box27D17Parent.attainer_d0 Box27D17Parent.attainer_d1
      (by decide) (by decide) (by decide) attainer_covered
      254 0 Box27Slice24.attainer_halts hd
    omega
  · intro h m hm d0 d1 e0 b1 f0 hd0 hd1 he0 hb1 hf0 hc k d hk hd
    have hb := bound255 m hm d0 d1 e0 b1 f0 hd0 hd1 he0 hb1 hf0 hc k d hk hd
    omega

#print axioms b1Pairs
#print axioms f0Pairs
#print axioms b1Support
#print axioms f0Support
#print axioms oldDisjoint
#print axioms branchDisjoint
#print axioms coveredMass
#print axioms bound255
#print axioms exact_weighted
end BB6.Agent49.Box27Partial49624
