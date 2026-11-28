import Box27Partial5648
import Box27ResidualB1D1
import Box27ResidualB1E0
import Box27ResidualD1F0
import Box27ResidualE0F0

set_option maxRecDepth 100000
set_option maxHeartbeats 0

/-!
The first formal source-relative 64.52%-of-Box27 classification.

A1,E1,F1 are always free. We represent a partial source cylinder by
the four other variable slots D1,E0,B1,F0, all Option (Fin 25), plus
its fixed D0. A pair of cylinders cannot overlap if their D0 values
differ or one jointly fixed slot has different prescribed values.
The executable kernel-checkable Pairwise and across-old disjointness
lemmas certify that the 1005 newly accepted candidate FAR cylinders
are mutually disjoint and avoid every existing 56.48% source cylinder.

Thus exactly 1005*25^5 = 9,814,453,125 extra full six-state tables,
and 78,759,765,625 physical tables in the sharp weighted255 union,
out of the 122,070,312,500-table Raw10 Box27 source rectangle.
This is not a proof of a global Busy Beaver upper bound.
-/
namespace BB6.Agent49.Box27Partial6452
open BB6Coverage BB6.Agent13BlankDelay
open BB6.Agent49Box BB6.Agent49BoxBridge
open BB6.Agent13.Box17 (decode)
open BB6.Agent49

structure Cube where
  d0 : Fin 25
  d1 : Option (Fin 25)
  e0 : Option (Fin 25)
  b1 : Option (Fin 25)
  f0 : Option (Fin 25)
  deriving DecidableEq

def optConflict (a b : Option (Fin 25)) : Bool :=
  match a,b with
  | some x,some y => decide (x ≠ y)
  | _,_ => false

def separated (a b : Cube) : Bool :=
  decide (a.d0 ≠ b.d0) ||
    optConflict a.d1 b.d1 || optConflict a.e0 b.e0 ||
    optConflict a.b1 b.b1 || optConflict a.f0 b.f0

def oldCells : List Cube :=
  (Box27D0FastPumps.fastCodes.map fun d => ⟨d,none,none,none,none⟩) ++
  (Box27D0D1FAR.pairs.map fun (d,x) => ⟨d,some x,none,none,none⟩) ++
  (Box27D0D1FARExt.pairs.map fun (d,x) => ⟨d,some x,none,none,none⟩) ++
  [⟨14,some 17,none,none,none⟩] ++
  (Box27D0E0FAR.pairs.map fun (d,x) => ⟨d,none,some x,none,none⟩) ++
  (Box27D0E0FARMore.pairs.map fun (d,x) => ⟨d,none,some x,none,none⟩) ++
  (Box27D0B1FAR.pairs.map fun (d,x) => ⟨d,none,none,some x,none⟩) ++
  (Box27D0F0FAR.pairs.map fun (d,x) => ⟨d,none,none,none,some x⟩) ++
  (Box27D0D1E0FAR.keys.map fun (d,x,y) => ⟨d,some x,some y,none,none⟩) ++
  (Box27D0B1F0TripleFAR.keys.map fun (d,x,y) => ⟨d,none,none,some x,some y⟩)

def newCells : List Cube :=
  (Box27ResidualB1D1.cases.map fun c =>
    ⟨c.d0,some c.y,none,some c.x,none⟩) ++
  (Box27ResidualB1E0.cases.map fun c =>
    ⟨c.d0,none,some c.y,some c.x,none⟩) ++
  (Box27ResidualD1F0.cases.map fun c =>
    ⟨c.d0,some c.x,none,none,some c.y⟩) ++
  (Box27ResidualE0F0.cases.map fun c =>
    ⟨c.d0,none,some c.x,none,some c.y⟩)

/-- Disjointness audit against *every* prior source cylinder. -/
theorem newOutsideOld :
    newCells.all (fun x => oldCells.all (separated x)) = true := by decide

/-- The 1005 newly constructed cylinders are also mutually disjoint. -/
theorem newPairwise :
    newCells.Pairwise (fun x y => separated x y = true) := by decide

theorem newCount : newCells.length = 1005 := by decide

theorem newMass : 1005 * 25^5 = 9814453125 := by decide
theorem totalMass : 68945312500 + 1005*25^5 = 78759765625 := by decide
theorem sourceMass : 20*25^7 = 122070312500 := by decide

def covered (d0 d1 e0 b1 f0 : Fin 25) : Bool :=
  decide (Box27Partial5648.covered d0 d1 e0 b1 f0 = true ∨
    (d0,b1,d1) ∈ Box27ResidualB1D1.keys ∨
    (d0,b1,e0) ∈ Box27ResidualB1E0.keys ∨
    (d0,d1,f0) ∈ Box27ResidualD1F0.keys ∨
    (d0,e0,f0) ∈ Box27ResidualE0F0.keys)

theorem bound255 (m : Machine)
    (hm : Fits raw10Remainder[27]! m)
    (d0 d1 e0 b1 f0 : Fin 25)
    (hd0 : m (3,false) = decode d0)
    (hd1 : m (3,true) = decode d1)
    (he0 : m (4,false) = decode e0)
    (hb1 : m (1,true) = decode b1)
    (hf0 : m (5,false) = decode f0)
    (hc : covered d0 d1 e0 b1 f0 = true) : WeightedBound 255 m := by
  have h : Box27Partial5648.covered d0 d1 e0 b1 f0 = true ∨
      (d0,b1,d1) ∈ Box27ResidualB1D1.keys ∨
      (d0,b1,e0) ∈ Box27ResidualB1E0.keys ∨
      (d0,d1,f0) ∈ Box27ResidualD1F0.keys ∨
      (d0,e0,f0) ∈ Box27ResidualE0F0.keys := of_decide_eq_true hc
  rcases h with ho|hbd|hbe|hdf|hef
  · exact Box27Partial5648.bound255 m hm d0 d1 e0 b1 f0
      hd0 hd1 he0 hb1 hf0 ho
  · exact Box27ResidualB1D1.source_bound 255 m hm d0 b1 d1 hd0 hb1 hd1 hbd
  · exact Box27ResidualB1E0.source_bound 255 m hm d0 b1 e0 hd0 hb1 he0 hbe
  · exact Box27ResidualD1F0.source_bound 255 m hm d0 d1 f0 hd0 hd1 hf0 hdf
  · exact Box27ResidualE0F0.source_bound 255 m hm d0 e0 f0 hd0 he0 hf0 hef

theorem attainer_covered : covered 14 17 24 18 3 = true := by decide

/-- Exact sharp weighted optimum over the finite disjoint 64.52% union. -/
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

#print axioms newOutsideOld
#print axioms newPairwise
#print axioms newCount
#print axioms totalMass
#print axioms bound255
#print axioms exact_weighted
end BB6.Agent49.Box27Partial6452
