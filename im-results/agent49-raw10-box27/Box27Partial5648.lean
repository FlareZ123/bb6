import Box27Partial50608
import Box27D0E0FARMore

set_option maxRecDepth 100000
set_option maxHeartbeats 0

/-!
56.48% (68,945,312,500) of all original Raw10 Box27 complete tables
have a sharp source-relative weighted upper bound 255. The machine
union is the 50.608% cut plus 32 large D0/E0 FAR cylinders.
The FAR cylinders overlap exactly 66 of the older 166 triple FARs;
we subtract them by checking the real original finite source domain,
rather than summing certificate masses blindly.

The new 32 D0/E0 pairs yield 800 (D0,D1,E0) triples, 66 overlap
previous covered triples, and hence 734 genuinely new triples.
Each new triple has 25^5 complete tables, so 734*25^5 =
7,167,968,750 new physical machines. All claims are source-relative
to raw10Remainder[27]!, not global BB(6).
-/
namespace BB6.Agent49.Box27Partial5648
open BB6Coverage BB6.Agent13BlankDelay
open BB6.Agent49Box BB6.Agent49BoxBridge
open BB6.Agent13.Box17 (decode)
open BB6.Agent49

def newD0 : List (Fin 25) := [17,18,19,20]

theorem newSupport :
    ∀ d0 e0 : Fin 25,
      (d0,e0) ∈ Box27D0E0FARMore.pairs → d0 ∈ newD0 := by decide

theorem noB1 (d0 e0 b1 : Fin 25)
    (h : (d0,e0) ∈ Box27D0E0FARMore.pairs) :
    (d0,b1) ∉ Box27D0B1FAR.pairs := by
  have hm : d0 ∈ newD0 := newSupport d0 e0 h
  have hdis : ∀ d : Fin 25, d ∈ newD0 →
      d ∉ Box27Partial49624.b1D0 := by decide
  intro hpair
  exact (hdis d0 hm) (Box27Partial49624.b1Support d0 b1 hpair)

theorem noF0 (d0 e0 f0 : Fin 25)
    (h : (d0,e0) ∈ Box27D0E0FARMore.pairs) :
    (d0,f0) ∉ Box27D0F0FAR.pairs := by
  have hm : d0 ∈ newD0 := newSupport d0 e0 h
  have hdis : ∀ d : Fin 25, d ∈ newD0 →
      d ∉ Box27Partial49624.f0D0 := by decide
  intro hpair
  exact (hdis d0 hm) (Box27Partial49624.f0Support d0 f0 hpair)

theorem noOldB1F0Triple (d0 e0 b1 f0 : Fin 25)
    (h : (d0,e0) ∈ Box27D0E0FARMore.pairs) :
    (d0,b1,f0) ∉ Box27D0B1F0TripleFAR.keys := by
  have hm : d0 ∈ newD0 := newSupport d0 e0 h
  have hdis : ∀ d : Fin 25, d ∈ newD0 →
      d ∉ Box27Partial50608.newD0 := by decide
  intro hpair
  exact (hdis d0 hm) (Box27Partial50608.newSupport d0 b1 f0 hpair)

/-- On these new pair cylinders all previous B1/F0-based classes
    vanish, leaving exactly the original (D0,D1,E0) coverage test. -/
theorem oldEquivalent (d0 d1 e0 b1 f0 : Fin 25)
    (h : (d0,e0) ∈ Box27D0E0FARMore.pairs) :
    (Box27Partial50608.covered d0 d1 e0 b1 f0 = true ↔
     Box27Partial39424.covered d0 d1 e0 = true) := by
  have hb := noB1 d0 e0 b1 h
  have hf := noF0 d0 e0 f0 h
  have ht := noOldB1F0Triple d0 e0 b1 f0 h
  simp [Box27Partial50608.covered,Box27Partial49624.covered,hb,hf,ht]

/-- Enumerate only genuinely new original (D0,D1,E0) triples,
    rather than multiply possibly overlapping coverage claims. -/
def newTriples : List (Fin 25 × Fin 25 × Fin 25) :=
  Box27D0E0FARMore.pairs.flatMap fun (d0,e0) =>
    (List.finRange 25).filterMap fun d1 =>
      if Box27Partial39424.covered d0 d1 e0 = true
      then none else some (d0,d1,e0)

theorem newCount : newTriples.length = 734 := by decide
theorem newNodup : newTriples.Nodup := by decide

theorem newMass : 734*25^5 = 7167968750 := by decide
theorem totalMass : 61777343750 + 734*25^5 = 68945312500 := by decide
theorem sourceMass : 20*25^7 = 122070312500 := by decide

def covered (d0 d1 e0 b1 f0 : Fin 25) : Bool :=
  decide (Box27Partial50608.covered d0 d1 e0 b1 f0 = true ∨
    (d0,e0) ∈ Box27D0E0FARMore.pairs)

theorem bound255 (m : Machine)
    (hm : Fits raw10Remainder[27]! m)
    (d0 d1 e0 b1 f0 : Fin 25)
    (hd0 : m (3,false) = decode d0)
    (hd1 : m (3,true) = decode d1)
    (he0 : m (4,false) = decode e0)
    (hb1 : m (1,true) = decode b1)
    (hf0 : m (5,false) = decode f0)
    (hc : covered d0 d1 e0 b1 f0 = true) : WeightedBound 255 m := by
  have h : Box27Partial50608.covered d0 d1 e0 b1 f0 = true ∨
      (d0,e0) ∈ Box27D0E0FARMore.pairs := of_decide_eq_true hc
  rcases h with ho|hn
  · exact Box27Partial50608.bound255 m hm d0 d1 e0 b1 f0
      hd0 hd1 he0 hb1 hf0 ho
  · exact Box27D0E0FARMore.source_bound 255 m hm d0 e0 hd0 he0 hn

theorem attainer_covered : covered 14 17 24 18 3 = true := by decide

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
#print axioms noB1
#print axioms noF0
#print axioms noOldB1F0Triple
#print axioms oldEquivalent
#print axioms newCount
#print axioms newNodup
#print axioms newMass
#print axioms totalMass
#print axioms bound255
#print axioms exact_weighted
end BB6.Agent49.Box27Partial5648
