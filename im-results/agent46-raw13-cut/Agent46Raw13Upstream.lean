import Agent46Raw13Data
import WeightedNonhaltLeafAdapter

set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace BB6.Agent46Raw13Upstream
open BB6Coverage BB6.Agent13BlankDelay BB6.Agent50TNFPilot BB6.Agent31ThreeHole
open BB6.Agent46CanonicalCut BB6.Agent46Raw13 BB6.Agent47WeightedHalt

def candidate1 : Machine := fun s => ([some ⟨true, true, 1⟩, some ⟨true, false, 3⟩, some ⟨true, true, 2⟩, some ⟨false, true, 1⟩, some ⟨true, false, 0⟩, some ⟨false, true, 4⟩, some ⟨true, false, 2⟩, some ⟨true, false, 4⟩, some ⟨true, false, 5⟩, some ⟨false, false, 0⟩, some ⟨false, true, 4⟩, none] : List (Option Move))[2*s.1.val+s.2.toNat]?.getD none
def p1_1 : PartialMachine := refine raw13 (0, true) (some ⟨true, false, 3⟩)
theorem p1_1_support : TNFSupport p1_1 4 := refine_support raw13 (0, true) ⟨true, false, 3⟩ 3 4 raw13_support (by decide) (by decide) (by decide)
theorem p1_1_nohalt : weightedTNFNoAssignedHalt p1_1 := weightedTNFNoAssignedHalt_refine _ _ _ raw13_nohalt
def p1_2 : PartialMachine := refine p1_1 (3, true) (some ⟨true, false, 4⟩)
theorem p1_2_support : TNFSupport p1_2 5 := refine_support p1_1 (3, true) ⟨true, false, 4⟩ 4 5 p1_1_support (by decide) (by decide) (by decide)
theorem p1_2_nohalt : weightedTNFNoAssignedHalt p1_2 := weightedTNFNoAssignedHalt_refine _ _ _ p1_1_nohalt
def p1_3 : PartialMachine := refine p1_2 (4, false) (some ⟨true, false, 5⟩)
theorem p1_3_support : TNFSupport p1_3 6 := refine_support p1_2 (4, false) ⟨true, false, 5⟩ 5 6 p1_2_support (by decide) (by decide) (by decide)
theorem p1_3_nohalt : weightedTNFNoAssignedHalt p1_3 := weightedTNFNoAssignedHalt_refine _ _ _ p1_2_nohalt
abbrev parent1 := p1_3
def cut1 : Cut :=
  .split 6 (5, false) (byCutMove [
.unresolved,
.unresolved,
.unresolved,
.unresolved,
.closed (.cycle 5 2 false (-1)),
.closed (.cycle 6 1 false (-2)),
.unresolved,
.unresolved,
.unresolved,
.closed (.cycle 4 3 false (0)),
.split 7 (4, true) (byCutMove [
.split 10 (2, true) (byCutMove [
.closed (.cycle 3 8 false (1)),
.unresolved,
.unresolved,
.closed (.cycle 7 5 false (0)),
.unresolved,
.unresolved,
.unresolved,
.unresolved,
.unresolved,
.unresolved,
.split 38 (3, false) (byCutMove [
.closed (.cycle 119 51 false (2)),
.closed (.cycle 37 4 false (-3)),
.unresolved,
.closed (.cycle 38 1 false (-4)),
.closed (.cycle 17 40 false (4)),
.closed (.cycle 131 55 false (2)),
.closed (.cycle 37 2 true (-4)),
.unresolved,
.unresolved,
.closed (.cycle 131 55 false (2)),
.closed (.cycle 117 41 false (0)),
.unresolved,
.unresolved,
.closed (.cycle 117 41 false (0)),
.split 41 (1, true) (byCutMove [
.closed (.cycle 37 5 false (-3)),
.closed (.cycle 37 8 false (-3)),
.closed (.cycle 26 19 false (1)),
.closed (.cycle 17 38 false (4)),
.closed (.cycle 162 44 false (-8)),
.closed (.last 42 (5, true)),
.closed (.cycle 26 19 false (1)),
.unresolved,
.closed (.last 50 (5, true)),
.closed (.last 44 (5, true)),
.closed (.cycle 127 25 false (-5)),
.closed (.last 42 (5, true)),
.closed (.cycle 37 5 false (-3)),
.closed (.cycle 26 34 false (1)),
.closed (.cycle 26 17 false (1)),
.closed (.cycle 17 36 false (4)),
.closed (.cycle 79 64 false (2)),
.closed (.last 42 (5, true)),
.closed (.cycle 81 66 false (2)),
.closed (.cycle 115 19 false (-5)),
.closed (.cycle 29 13 false (1)),
.closed (.cycle 35 7 false (-1)),
.closed (.cycle 26 21 false (1)),
.closed (.last 42 (5, true))]),
.closed (.cycle 38 1 false (-4)),
.closed (.cycle 26 15 false (1)),
.closed (.cycle 125 53 false (2)),
.closed (.cycle 26 17 false (1)),
.unresolved,
.closed (.cycle 170 51 false (1)),
.closed (.cycle 125 53 false (2)),
.closed (.cycle 36 3 false (-2)),
.unresolved]),
.unresolved,
.closed (.cycle 3 8 false (1)),
.unresolved,
.unresolved,
.closed (.cycle 7 5 false (0)),
.unresolved,
.unresolved,
.unresolved,
.unresolved,
.unresolved,
.closed (.cycle 3 10 false (1)),
.closed (.cycle 7 7 false (1)),
.unresolved]),
.unresolved,
.unresolved,
.unresolved,
.closed (.cycle 5 3 false (-1)),
.closed (.cycle 5 4 true (-2)),
.unresolved,
.unresolved,
.unresolved,
.closed (.cycle 4 4 true (-2)),
.closed (.cycle 10 3 true (2)),
.unresolved,
.unresolved,
.unresolved,
.unresolved,
.unresolved,
.closed (.cycle 5 3 false (-1)),
.closed (.cycle 6 2 true (-2)),
.closed (.cycle 3 5 false (1)),
.unresolved,
.unresolved,
.closed (.cycle 7 2 true (-1)),
.unresolved,
.unresolved]),
.unresolved,
.unresolved,
.unresolved,
.unresolved,
.unresolved,
.closed (.cycle 5 2 false (-1)),
.closed (.cycle 6 1 false (-2)),
.closed (.cycle 3 4 false (1)),
.unresolved,
.unresolved,
.unresolved,
.unresolved,
.unresolved])
theorem checked1 : check 21269 parent1 6 cut1 = true := by decide
def rs1 := (residuals parent1 6 cut1).filter (fun e => !(tableOK e.2 (forgetHaltRows candidate1)))
theorem sound1 (h : NeverHalts candidate1) (m : Machine) (hm : TNFQuotientCompatible parent1 m) :
    WeightedBound 21269 m ∨ ∃ e ∈ rs1, TNFQuotientCompatible e.2 m := by
  rcases sound 21269 parent1 6 cut1 (by decide) p1_3_support (by decide) p1_3_nohalt checked1 m hm with hb | ⟨e, he, hq⟩
  · exact Or.inl hb
  by_cases ht : tableOK e.2 (forgetHaltRows candidate1) = true
  · have hq' : TNFQuotientCompatible (forgetHaltRows candidate1) m := tableOK_sound _ _ ht ▸ hq
    exact Or.inl (safe_quotient (by decide) (fun m' hm' => weighted_never 21269 m' (forgetHaltRows_all_completions_neverHalt candidate1 h m' hm')) m hq')
  · exact Or.inr ⟨e, List.mem_filter.mpr ⟨he, by simp [ht]⟩, hq⟩
theorem count1 : rs1.length = 56 := by decide
theorem massBefore1 : openMass 6 6 cut1 = 172145025 := by decide
theorem targetMembership1 : ((residuals parent1 6 cut1).filter (fun e => tableOK e.2 (forgetHaltRows candidate1))).length = 1 := by decide
theorem member1 : (raw13Residuals.filter (fun e => tableOK e.2 parent1)).length = 1 := by decide

def candidate2 : Machine := fun s => ([some ⟨true, true, 1⟩, some ⟨true, false, 3⟩, some ⟨true, true, 2⟩, some ⟨false, true, 1⟩, some ⟨true, false, 0⟩, some ⟨true, true, 4⟩, some ⟨true, false, 5⟩, some ⟨false, false, 0⟩, some ⟨true, false, 0⟩, some ⟨false, true, 3⟩, some ⟨true, false, 2⟩, none] : List (Option Move))[2*s.1.val+s.2.toNat]?.getD none
def p2_1 : PartialMachine := refine raw13 (0, true) (some ⟨true, false, 3⟩)
theorem p2_1_support : TNFSupport p2_1 4 := refine_support raw13 (0, true) ⟨true, false, 3⟩ 3 4 raw13_support (by decide) (by decide) (by decide)
theorem p2_1_nohalt : weightedTNFNoAssignedHalt p2_1 := weightedTNFNoAssignedHalt_refine _ _ _ raw13_nohalt
def p2_2 : PartialMachine := refine p2_1 (3, true) (some ⟨false, false, 0⟩)
theorem p2_2_support : TNFSupport p2_2 4 := refine_support p2_1 (3, true) ⟨false, false, 0⟩ 4 4 p2_1_support (by decide) (by decide) (by decide)
theorem p2_2_nohalt : weightedTNFNoAssignedHalt p2_2 := weightedTNFNoAssignedHalt_refine _ _ _ p2_1_nohalt
def p2_3 : PartialMachine := refine p2_2 (2, true) (some ⟨true, true, 4⟩)
theorem p2_3_support : TNFSupport p2_3 5 := refine_support p2_2 (2, true) ⟨true, true, 4⟩ 4 5 p2_2_support (by decide) (by decide) (by decide)
theorem p2_3_nohalt : weightedTNFNoAssignedHalt p2_3 := weightedTNFNoAssignedHalt_refine _ _ _ p2_2_nohalt
abbrev parent2 := p2_3
def cut2 : Cut :=
  .split 8 (4, true) (byCutMove [
.unresolved,
.unresolved,
.unresolved,
.unresolved,
.unresolved,
.unresolved,
.closed (.cycle 0 9 true (-1)),
.unresolved,
.unresolved,
.split 9 (3, false) (byCutMove [
.unresolved,
.unresolved,
.unresolved,
.unresolved,
.unresolved,
.unresolved,
.closed (.cycle 0 10 true (-1)),
.unresolved,
.unresolved,
.closed (.cycle 9 1 true (3)),
.unresolved,
.unresolved,
.unresolved,
.unresolved,
.unresolved,
.unresolved,
.unresolved,
.split 10 (5, false) (byCutMove [
.closed (.cycle 5 11 false (3)),
.unresolved,
.unresolved,
.unresolved,
.unresolved,
.unresolved,
.unresolved,
.unresolved,
.unresolved,
.unresolved,
.closed (.cycle 8 3 true (2)),
.unresolved,
.unresolved,
.unresolved,
.split 26 (1, true) (byCutMove [
.closed (.cycle 21 6 false (-1)),
.closed (.cycle 21 9 false (-1)),
.unresolved,
.unresolved,
.closed (.cycle 22 6 false (-2)),
.unresolved,
.unresolved,
.split 32 (4, false) (byCutMove [
.unresolved,
.closed (.cycle 30 20 true (0)),
.closed (.cycle 31 2 true (1)),
.closed (.cycle 52 12 true (0)),
.unresolved,
.closed (.last 33 (5, true)),
.closed (.last 35 (5, true)),
.closed (.cycle 29 39 true (-2)),
.closed (.last 47 (5, true)),
.unresolved,
.closed (.last 133 (5, true)),
.closed (.last 33 (5, true)),
.unresolved,
.closed (.cycle 33 12 true (1)),
.unresolved,
.closed (.cycle 81 7 false (-3)),
.unresolved,
.closed (.last 33 (5, true)),
.unresolved,
.closed (.cycle 29 38 true (-1)),
.unresolved,
.closed (.last 64 (5, true)),
.closed (.cycle 12 21 true (-5)),
.closed (.last 33 (5, true))]),
.unresolved,
.unresolved,
.unresolved,
.unresolved,
.closed (.cycle 21 6 false (-1)),
.unresolved,
.unresolved,
.unresolved,
.closed (.cycle 11 20 false (4)),
.unresolved,
.closed (.cycle 19 8 false (1)),
.unresolved,
.closed (.cycle 11 16 false (4)),
.unresolved,
.unresolved,
.unresolved]),
.unresolved,
.unresolved,
.unresolved,
.closed (.cycle 3 15 false (3)),
.unresolved,
.unresolved,
.unresolved,
.closed (.cycle 8 3 true (2)),
.unresolved]),
.unresolved,
.closed (.cycle 1 9 true (-1)),
.closed (.cycle 7 6 true (1)),
.closed (.cycle 9 1 true (3)),
.unresolved,
.unresolved]),
.unresolved,
.unresolved,
.unresolved,
.unresolved,
.closed (.cycle 7 2 true (1)),
.unresolved,
.unresolved,
.unresolved,
.unresolved,
.unresolved,
.unresolved,
.unresolved,
.unresolved,
.unresolved])
theorem checked2 : check 21269 parent2 5 cut2 = true := by decide
def rs2 := (residuals parent2 5 cut2).filter (fun e => !(tableOK e.2 (forgetHaltRows candidate2)))
theorem sound2 (h : NeverHalts candidate2) (m : Machine) (hm : TNFQuotientCompatible parent2 m) :
    WeightedBound 21269 m ∨ ∃ e ∈ rs2, TNFQuotientCompatible e.2 m := by
  rcases sound 21269 parent2 5 cut2 (by decide) p2_3_support (by decide) p2_3_nohalt checked2 m hm with hb | ⟨e, he, hq⟩
  · exact Or.inl hb
  by_cases ht : tableOK e.2 (forgetHaltRows candidate2) = true
  · have hq' : TNFQuotientCompatible (forgetHaltRows candidate2) m := tableOK_sound _ _ ht ▸ hq
    exact Or.inl (safe_quotient (by decide) (fun m' hm' => weighted_never 21269 m' (forgetHaltRows_all_completions_neverHalt candidate2 h m' hm')) m hq')
  · exact Or.inr ⟨e, List.mem_filter.mpr ⟨he, by simp [ht]⟩, hq⟩
theorem count2 : rs2.length = 81 := by decide
theorem massBefore2 : openMass 6 5 cut2 = 212416450 := by decide
theorem targetMembership2 : ((residuals parent2 5 cut2).filter (fun e => tableOK e.2 (forgetHaltRows candidate2))).length = 1 := by decide
theorem member2 : (raw13Residuals.filter (fun e => tableOK e.2 parent2)).length = 1 := by decide

abbrev Entry := List Move × PartialMachine

def replace (p : PartialMachine) (rs : List Entry) (e : Entry) : List Entry :=
  if tableOK e.2 p then rs.map (fun r => (e.1 ++ r.1, r.2)) else [e]

theorem replace_sound (p : PartialMachine) (rs : List Entry) (roster : List Entry)
    (m : Machine) (hroster : WeightedBound 21269 m ∨ ∃ e ∈ roster, TNFQuotientCompatible e.2 m)
    (hlocal : TNFQuotientCompatible p m → WeightedBound 21269 m ∨ ∃ e ∈ rs, TNFQuotientCompatible e.2 m) :
    WeightedBound 21269 m ∨ ∃ e ∈ roster.flatMap (replace p rs), TNFQuotientCompatible e.2 m := by
  rcases hroster with hb | ⟨e, he, hq⟩
  · exact Or.inl hb
  by_cases ht : tableOK e.2 p = true
  · have hp := tableOK_sound e.2 p ht
    rcases hlocal (hp ▸ hq) with hb | ⟨r, hr, hq'⟩
    · exact Or.inl hb
    · refine Or.inr ⟨(e.1 ++ r.1, r.2), List.mem_flatMap.mpr ⟨e, he, ?_⟩, hq'⟩
      simp only [replace, ht, ite_true]
      exact List.mem_map.mpr ⟨r, hr, rfl⟩
  · exact Or.inr ⟨e, List.mem_flatMap.mpr ⟨e, he, by simp [replace, ht]⟩, hq⟩

def refined : List Entry :=
  (raw13Residuals.flatMap (replace parent1 rs1)).flatMap
    (replace parent2 rs2)

theorem refined_sound (h1 : NeverHalts candidate1) (h2 : NeverHalts candidate2)
    (m : Machine) (hm : TNFQuotientCompatible raw13 m) :
    WeightedBound 21269 m ∨ ∃ e ∈ refined, TNFQuotientCompatible e.2 m :=
  replace_sound _ _ _ m (replace_sound _ _ _ m (raw13_sound m hm) (sound1 h1 m)) (sound2 h2 m)

theorem refined_count : refined.length = 1843 := by decide

#print axioms checked1
#print axioms checked2
#print axioms sound1
#print axioms sound2
#print axioms member1
#print axioms member2
#print axioms refined_sound
#print axioms refined_count
end BB6.Agent46Raw13Upstream
