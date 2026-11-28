import Agent46Raw13Base
import D3LocalPumps
import D3LocalF0Variants
import D3LocalRD
import D3LocalRD0LA
import D3SiblingSource

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace BB6.Agent19D3Local
open BB6Coverage BB6.Agent13BlankDelay BB6.Agent8TNFPath
open BB6.Agent50TNFPilot BB6.Agent31ThreeHole BB6.Agent46CanonicalCut
open BB6.Agent10ZipAudit BB6.Agent46Raw13

def p1 : PartialMachine := refine raw13 (0,true) (some ⟨false,false,2⟩)
def p2 : PartialMachine := refine p1 (2,true) (some ⟨false,false,3⟩)
def parent : PartialMachine := refine p2 (3,false) (some ⟨false,true,1⟩)

theorem parent_support : TNFSupport parent 4 := by
  have h1 : TNFSupport p1 3 := refine_support raw13 (0,true) ⟨false,false,2⟩ 3 3 raw13_support (by decide) (by decide) (by decide)
  have h2 : TNFSupport p2 4 := refine_support p1 (2,true) ⟨false,false,3⟩ 3 4 h1 (by decide) (by decide) (by decide)
  exact refine_support p2 (3,false) ⟨false,true,1⟩ 4 4 h2 (by decide) (by decide) (by decide)

theorem parent_nohalt : weightedTNFNoAssignedHalt parent :=
  weightedTNFNoAssignedHalt_refine _ _ _
    (weightedTNFNoAssignedHalt_refine _ _ _
      (weightedTNFNoAssignedHalt_refine _ _ _ raw13_nohalt))

/-- Only the authentic D3 path is split; sibling cylinders with independently
checked proofs are closed and every other sibling is retained. -/
def cut : Cut :=
  .split 11 (1,true) (byCutMove [
    .closed (.cycle 8 4 false (0)),
    .closed (.cycle 6 7 false (1)),
    .closed (.cycle 4 8 false (1)),
    .unresolved,
    .unresolved,
    .unresolved,
    .closed (.proven BB6Coverage.Agent31Pump.D3Affine.p2 BB6Coverage.Agent31Pump.D3Affine.never2),
    .unresolved,
    .unresolved,
    .unresolved,
    .unresolved,
    .unresolved,
    .closed (.cycle 8 4 false (0)),
    .unresolved,
    .unresolved,
    .unresolved,
    .unresolved,
    .unresolved,
    .unresolved,
    .unresolved,
    .closed (.cycle 2 10 false (2)),
    .unresolved,
    .split 12 (4,false) (byCutMove [
    .closed (.cycle 3 10 false (1)),
    .closed (.cycle 11 2 true (-1)),
    .unresolved,
    .unresolved,
    .unresolved,
    .unresolved,
    .closed (.cycle 2 12 false (2)),
    .unresolved,
    .unresolved,
    .unresolved,
    .unresolved,
    .unresolved,
    .closed (.cycle 3 10 false (1)),
    .unresolved,
    .unresolved,
    .unresolved,
    .unresolved,
    .unresolved,
    .unresolved,
    .split 14 (4,true) (byCutMove [
    .unresolved,
    .unresolved,
    .unresolved,
    .unresolved,
    .closed (.cycle 1 19 false (2)),
    .unresolved,
    .unresolved,
    .unresolved,
    .unresolved,
    .unresolved,
    .unresolved,
    .unresolved,
    .unresolved,
    .closed (.cycle 13 2 true (1)),
    .unresolved,
    .unresolved,
    .closed (.cycle 16 5 false (0)),
    .unresolved,
    .unresolved,
    .unresolved,
    .unresolved,
    .unresolved,
    .unresolved,
    .split 15 (5,false) (byCutMove [
    .split 18 (3,true) (byCutMove [
      .closed (.cycle 0 39 false (3)),
      .closed (.proven BB6Coverage.Agent31Pump.D3F0.v0LA BB6Coverage.Agent31Pump.D3F0.never_v0LA),
      .closed (.cycle 44 18 false (-2)),
      .closed (.cycle 18 18 false (2)),
      .closed (.cycle 1 43 false (3)),
      .closed (.last 19 (5,true)),
      .closed (.cycle 2 26 false (3)),
      .closed (.cycle 2 20 false (3)),
      .closed (.cycle 21 11 true (1)),
      .closed (.cycle 17 19 true (0)),
      .closed (.cycle 2 26 false (3)),
      .closed (.last 49 (5,true)),
      .closed (.cycle 3 16 false (3)),
      .closed (.cycle 23 3 false (-1)),
      .closed (.cycle 19 8 false (-1)),
      .closed (.last 24 (5,true)),
      .closed (.last 20 (5,true)),
      .closed (.last 19 (5,true)),
      .closed (.cycle 17 10 true (0)),
      .closed (.last 43 (5,true)),
      .closed (.cycle 34 46 false (4)),
      .closed (.proven BB6Coverage.Agent31Pump.D3RD0LA.p BB6Coverage.Agent31Pump.D3RD0LA.never),
      .closed (.cycle 17 10 true (0)),
      .closed (.cycle 51 22 false (-1))
    ]),
    .unresolved,
    .unresolved,
    .unresolved,
    .closed (.cycle 14 2 true (2)),
    .split 16 (5,true) (byCutMove [
      .closed (.last 19 (3,true)),
      .closed (.last 23 (3,true)),
      .closed (.last 18 (3,true)),
      .closed (.last 17 (3,true)),
      .closed (.cycle 1 29 false (3)),
      .closed (.cycle 21 1 false (-3)),
      .closed (.last 29 (3,true)),
      .closed (.last 23 (3,true)),
      .closed (.last 25 (3,true)),
      .closed (.last 31 (3,true)),
      .closed (.last 29 (3,true)),
      .closed (.cycle 29 1 false (-1)),
      .closed (.last 19 (3,true)),
      .closed (.cycle 13 4 true (1)),
      .closed (.last 18 (3,true)),
      .closed (.last 17 (3,true)),
      .closed (.cycle 16 2 true (1)),
      .closed (.cycle 21 1 false (-3)),
      .closed (.last 22 (3,true)),
      .closed (.last 21 (3,true)),
      .closed (.last 20 (3,true)),
      .closed (.last 24 (3,true)),
      .closed (.last 22 (3,true)),
      .closed (.cycle 15 2 true (2))
    ]),
    .unresolved,
    .unresolved,
    .unresolved,
    .unresolved,
    .unresolved,
    .closed (.cycle 15 1 true (3)),
    .unresolved,
    .closed (.cycle 13 3 true (1)),
    .unresolved,
    .unresolved,
    .split 17 (5,true) (byCutMove [
      .closed (.last 20 (3,true)),
      .closed (.last 24 (3,true)),
      .closed (.last 19 (3,true)),
      .closed (.last 18 (3,true)),
      .closed (.cycle 14 4 true (2)),
      .closed (.last 31 (3,true)),
      .closed (.last 30 (3,true)),
      .closed (.last 24 (3,true)),
      .closed (.last 26 (3,true)),
      .closed (.last 32 (3,true)),
      .closed (.last 30 (3,true)),
      .closed (.last 26 (3,true)),
      .closed (.last 20 (3,true)),
      .closed (.cycle 13 5 true (1)),
      .closed (.last 19 (3,true)),
      .closed (.last 18 (3,true)),
      .closed (.cycle 16 2 true (2)),
      .closed (.cycle 19 8 false (1)),
      .closed (.last 23 (3,true)),
      .closed (.last 22 (3,true)),
      .closed (.last 21 (3,true)),
      .closed (.last 25 (3,true)),
      .closed (.last 23 (3,true)),
      .closed (.cycle 15 3 true (2))
    ]),
    .split 16 (5,true) (byCutMove [
      .closed (.last 19 (3,true)),
      .closed (.last 25 (3,true)),
      .closed (.last 18 (3,true)),
      .closed (.last 17 (3,true)),
      .closed (.last 32 (3,true)),
      .closed (.cycle 21 1 false (-3)),
      .closed (.last 21 (3,true)),
      .closed (.last 23 (3,true)),
      .closed (.last 25 (3,true)),
      .closed (.last 17 (3,true)),
      .closed (.cycle 14 3 true (2)),
      .closed (.cycle 70 1 false (8)),
      .closed (.last 19 (3,true)),
      .closed (.cycle 13 7 true (1)),
      .closed (.last 18 (3,true)),
      .closed (.last 17 (3,true)),
      .closed (.cycle 16 2 true (1)),
      .closed (.cycle 21 1 false (-3)),
      .closed (.last 19 (3,true)),
      .closed (.last 23 (3,true)),
      .closed (.last 18 (3,true)),
      .closed (.last 17 (3,true)),
      .closed (.cycle 14 3 true (2)),
      .closed (.cycle 15 3 true (2))
    ]),
    .unresolved,
    .unresolved,
    .unresolved,
    .split 23 (3,true) (byCutMove [
    .closed (.cycle 0 27 false (6)),
    .closed (.proven BB6Coverage.Agent31Pump.D3Affine.p0 BB6Coverage.Agent31Pump.D3Affine.never0),
    .closed (.cycle 20 18 false (4)),
    .closed (.cycle 20 18 false (4)),
    .closed (.cycle 20 12 true (0)),
    .closed (.last 24 (5,true)),
    .unresolved,
    .closed (.proven BB6Coverage.Agent31Pump.D3Affine.p1 BB6Coverage.Agent31Pump.D3Affine.never1),
    .closed (.cycle 28 11 true (4)),
    .closed (.cycle 26 19 true (3)),
    .closed (.proven BB6Coverage.Agent31Pump.D3RE.p BB6Coverage.Agent31Pump.D3RE.never),
    .closed (.cycle 28 9 true (6)),
    .closed (.cycle 22 9 false (2)),
    .closed (.cycle 13 48 true (0)),
    .closed (.cycle 42 18 false (2)),
    .closed (.last 30 (5,true)),
    .closed (.last 25 (5,true)),
    .closed (.last 24 (5,true)),
    .closed (.cycle 26 10 true (3)),
    .closed (.last 53 (5,true)),
    .closed (.proven BB6Coverage.Agent31Pump.D3Counter.p BB6Coverage.Agent31Pump.D3Counter.never),
    .closed (.proven BB6Coverage.Agent31Pump.D3RD.p BB6Coverage.Agent31Pump.D3RD.never),
    .closed (.cycle 26 10 true (3)),
    .closed (.cycle 28 9 true (6))
  ]),
    .unresolved,
    .closed (.cycle 15 1 true (3))
  ])
  ]),
    .unresolved,
    .unresolved,
    .unresolved,
    .unresolved
  ]),
    .unresolved
  ])

def remaining : List (List Move × PartialMachine) := residuals parent 4 cut

theorem checked : check 21269 parent 4 cut = true := by decide

theorem remaining_count : remaining.length = 68 := by decide

theorem remaining_mass : openMass 6 4 cut = 171737550 := by decide

def d3Leaf : PartialMachine := fun s => match s.1.val,s.2 with
  | 0,false => some (some ⟨true,true,1⟩)
  | 0,true => some (some ⟨false,false,2⟩)
  | 1,false => some (some ⟨true,true,2⟩)
  | 1,true => some (some ⟨true,true,4⟩)
  | 2,false => some (some ⟨true,false,0⟩)
  | 2,true => some (some ⟨false,false,3⟩)
  | 3,false => some (some ⟨false,true,1⟩)
  | 3,true => some (some ⟨false,true,0⟩)
  | 4,false => some (some ⟨true,true,1⟩)
  | 4,true => some (some ⟨true,true,5⟩)
  | 5,false => some (some ⟨true,true,3⟩)
  | 5,true => none
  | _,_ => none

def otherRemaining : List (List Move × PartialMachine) :=
  remaining.filter (fun e => !tableOK e.2 d3Leaf)

theorem d3_count : (remaining.filter (fun e => tableOK e.2 d3Leaf)).length = 1 := by decide
theorem other_count : otherRemaining.length = 67 := by decide

theorem local_sound (m : Machine) (hm : TNFQuotientCompatible parent m) :
    WeightedBound 21269 m ∨ ∃ e ∈ remaining, TNFQuotientCompatible e.2 m :=
  BB6.Agent46CanonicalCut.sound 21269 parent 4 cut (by decide)
    parent_support (by decide) parent_nohalt checked m hm

/-- The D3 leaf must be proved separately at the actual global target;
    its other siblings are all explicit and cannot silently disappear. -/
theorem local_finish (B : Nat) (hB : 21269 ≤ B)
    (hD3 : Cover (WeightedBound B) d3Leaf)
    (hs : ∀ e ∈ otherRemaining, Cover (WeightedBound B) e.2)
    (m : Machine) (hm : TNFQuotientCompatible parent m) : WeightedBound B m := by
  rcases local_sound m hm with hb | ⟨e,he,hq⟩
  · exact fun k d hk hd => Nat.le_trans (hb k d hk hd) hB
  · cases ht : tableOK e.2 d3Leaf with
    | true =>
      have heq := tableOK_sound e.2 d3Leaf ht
      exact safe_quotient (by decide) hD3.sound m (heq ▸ hq)
    | false =>
      have hm' : e ∈ otherRemaining := List.mem_filter.mpr ⟨he,by simp [ht]⟩
      have hf : e.2 initialSlot = some (some ⟨true,true,1⟩) := by
        -- Discharge this finite invariant once, uniformly over the explicit roster.
        have hall : remaining.all (fun x => decide (x.2 initialSlot = some (some ⟨true,true,1⟩))) = true := by decide
        exact of_decide_eq_true (List.all_eq_true.mp hall e he)
      exact safe_quotient hf (hs e hm').sound m hq

abbrev Entry := List Move × PartialMachine

def graftEntry (e : Entry) : List Entry :=
  if tableOK e.2 parent then remaining.map (fun f => (e.1 ++ f.1,f.2)) else [e]

theorem graft_sound {rs : List Entry} {C : Nat}
    (hroot : ∀ m, compatible root m → WeightedBound C m ∨
      ∃ e ∈ rs, TNFQuotientCompatible e.2 m)
    (m : Machine) (hm : compatible root m) :
    WeightedBound (max C 21269) m ∨ ∃ e ∈ rs.flatMap graftEntry, TNFQuotientCompatible e.2 m := by
  rcases hroot m hm with hb | ⟨e,he,hq⟩
  · exact Or.inl (fun k d hk hd => Nat.le_trans (hb k d hk hd) (Nat.le_max_left _ _))
  · cases ht : tableOK e.2 parent with
    | false => exact Or.inr ⟨e,List.mem_flatMap.mpr ⟨e,he,by simp [graftEntry,ht]⟩,hq⟩
    | true =>
      have hEq := tableOK_sound e.2 parent ht
      rcases local_sound m (hEq ▸ hq) with hb | ⟨f,hf,hfq⟩
      · exact Or.inl (fun k d hk hd => Nat.le_trans (hb k d hk hd) (Nat.le_max_right _ _))
      · exact Or.inr ⟨(e.1 ++ f.1,f.2),List.mem_flatMap.mpr ⟨e,he,by
          simp only [graftEntry,ht,ite_true]
          exact List.mem_map.mpr ⟨f,hf,rfl⟩⟩,hfq⟩

#print axioms checked
#print axioms remaining_count
#print axioms remaining_mass
#print axioms d3_count
#print axioms local_sound
#print axioms local_finish
#print axioms graft_sound
end BB6.Agent19D3Local
