import Box27Partial49624
import Box27D0B1F0TripleFAR

set_option maxRecDepth 100000
set_option maxHeartbeats 0
/-!
Original Raw10 Box27: the first explicitly kernel-checkable source cut
crossing one half of the physical Box27 machine space.

Old 49.624% original-source cut:
  60,576,171,875 complete physical six-state two-symbol machines.
New 123 (D0,B1,F0) disjoint triple FARs:
  123*25^5 = 1,201,171,875 machines.
Combined exact total:
  61,777,343,750 of 122,070,312,500 = 50.608%.

The new 123 triples live entirely at D0 in {2,3,4,21,22,23,24};
the old 4928 (D0,D1,E0) triples do not touch those D0 choices.
By direct finite checked pair discrimination, none of the new triples
lies in an older 15 D0/B1 or 36 D0/F0 two-code cylinder. Consequently
all reported masses are disjoint. The weighted maximum 255 is sharp
from the original E0=24 witness. No global BB(6) bound follows.
-/
namespace BB6.Agent49.Box27Partial50608
open BB6Coverage BB6.Agent13BlankDelay
open BB6.Agent49Box BB6.Agent49BoxBridge
open BB6.Agent13.Box17 (decode)
open BB6.Agent49

def newD0 : List (Fin 25) := [2,3,4,21,22,23,24]

theorem newSupport :
    ∀ d0 b1 f0 : Fin 25,
      (d0,b1,f0) ∈ Box27D0B1F0TripleFAR.keys →
      d0 ∈ newD0 := by decide

theorem newOutsideOldTriples :
    ∀ d0 b1 f0 d1 e0 : Fin 25,
      (d0,b1,f0) ∈ Box27D0B1F0TripleFAR.keys →
      Box27Partial39424.covered d0 d1 e0 = false := by
  intro d0 b1 f0 d1 e0 h
  exact Box27Partial49624.oldDisjoint d0
    (by simpa [newD0,Box27Partial49624.b1D0,Box27Partial49624.f0D0] using
      newSupport d0 b1 f0 h) d1 e0

theorem newOutsideB1 :
    ∀ d0 b1 f0 : Fin 25,
      (d0,b1,f0) ∈ Box27D0B1F0TripleFAR.keys →
      (d0,b1) ∉ Box27D0B1FAR.pairs := by decide

theorem newOutsideF0 :
    ∀ d0 b1 f0 : Fin 25,
      (d0,b1,f0) ∈ Box27D0B1F0TripleFAR.keys →
      (d0,f0) ∉ Box27D0F0FAR.pairs := by decide

theorem coveredMass :
    60576171875 + 123*25^5 = 61777343750 := by decide

theorem sourceMass : 20*25^7 = 122070312500 := by decide

def covered (d0 d1 e0 b1 f0 : Fin 25) : Bool :=
  decide (Box27Partial49624.covered d0 d1 e0 b1 f0 = true ∨
    (d0,b1,f0) ∈ Box27D0B1F0TripleFAR.keys)

theorem bound255 (m : Machine)
    (hm : Fits raw10Remainder[27]! m)
    (d0 d1 e0 b1 f0 : Fin 25)
    (hd0 : m (3,false) = decode d0)
    (hd1 : m (3,true) = decode d1)
    (he0 : m (4,false) = decode e0)
    (hb1 : m (1,true) = decode b1)
    (hf0 : m (5,false) = decode f0)
    (hc : covered d0 d1 e0 b1 f0 = true) : WeightedBound 255 m := by
  have h : Box27Partial49624.covered d0 d1 e0 b1 f0 = true ∨
      (d0,b1,f0) ∈ Box27D0B1F0TripleFAR.keys := of_decide_eq_true hc
  rcases h with ho|hn
  · exact Box27Partial49624.bound255 m hm d0 d1 e0 b1 f0
      hd0 hd1 he0 hb1 hf0 ho
  · exact Box27D0B1F0TripleFAR.source_bound 255 m hm d0 b1 f0 hd0 hb1 hf0 hn

theorem attainer_covered : covered 14 17 24 18 3 = true := by decide

/-- Sharp exact weighted maximum for the explicit 50.608% source cut. -/
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
    exact Nat.le_trans (bound255 m hm d0 d1 e0 b1 f0
      hd0 hd1 he0 hb1 hf0 hc k d hk hd) h

#print axioms newSupport
#print axioms newOutsideOldTriples
#print axioms newOutsideB1
#print axioms newOutsideF0
#print axioms coveredMass
#print axioms bound255
#print axioms exact_weighted
end BB6.Agent49.Box27Partial50608
