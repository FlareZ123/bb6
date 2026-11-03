import M8TraceBridge
import SectionMassStrict
import Lean.Elab.Tactic.Omega

set_option maxRecDepth 300000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
namespace BB6.Agent1M8
open BB6.Agent46

/-!
End-to-end kernel replay of the exact, unmodified Machine C section.
Every segment is checked by Lean's kernel using `by decide`, no native
evaluation axioms. Original-source equivalence is M8TraceBridge.
The first mass-exceeding section occurs at index 150052.
-/

def seg0 : List (Nat × (Nat × Nat)) := [
  (1000, (3550,1698)),
  (1000, (2877,5442)),
  (1000, (3310,8793)),
  (1000, (15703,6137)),
  (1000, (8598,13032)),
  (1000, (13092,14378)),
  (1000, (7565,20571)),
  (1000, (20715,17466)),
  (1000, (8900,26954)),
  (1000, (35261,17284))
]
theorem checked0 : chainCheck seg0 (some (5,1)) (1,524260) = true := by decide
theorem end0 : chainEnd seg0 (some (5,1)) = some (35261,17284) := by decide

def seg1 : List (Nat × (Nat × Nat)) := [
  (1000, (61062,7933)),
  (1000, (8319,37734)),
  (1000, (4973,42895)),
  (1000, (96355,725)),
  (1000, (85432,9688)),
  (1000, (88336,11706)),
  (1000, (63286,27854)),
  (1000, (52673,36830)),
  (1000, (31243,51189)),
  (1000, (70469,35079))
]
theorem checked1 : chainCheck seg1 (some (35261,17284)) (1,524260) = true := by decide
theorem end1 : chainEnd seg1 (some (35261,17284)) = some (70469,35079) := by decide

def seg2 : List (Nat × (Nat × Nat)) := [
  (1000, (115355,16088)),
  (1000, (95874,29222)),
  (1000, (139276,10886)),
  (1000, (100007,33998)),
  (1000, (147407,13801)),
  (1000, (61202,60414)),
  (1000, (94643,47174)),
  (1000, (4130,95920)),
  (1000, (182903,9960)),
  (1000, (44719,82534))
]
theorem checked2 : chainCheck seg2 (some (70469,35079)) (1,524260) = true := by decide
theorem end2 : chainEnd seg2 (some (70469,35079)) = some (44719,82534) := by decide

def seg3 : List (Nat × (Nat × Nat)) := [
  (1000, (177884,19459)),
  (1000, (21831,100981)),
  (1000, (204045,13374)),
  (1000, (54747,91502)),
  (1000, (84907,80021)),
  (1000, (242003,4997)),
  (1000, (218639,20161)),
  (1000, (7268,129402)),
  (1000, (120293,76286)),
  (1000, (177119,51358))
]
theorem checked3 : chainCheck seg3 (some (44719,82534)) (1,524260) = true := by decide
theorem end3 : chainEnd seg3 (some (44719,82534)) = some (177119,51358) := by decide

def seg4 : List (Nat × (Nat × Nat)) := [
  (1000, (197070,44974)),
  (1000, (137409,78378)),
  (1000, (261901,19758)),
  (1000, (288301,9998)),
  (1000, (309505,2902)),
  (1000, (179921,71194)),
  (1000, (274763,27285)),
  (1000, (294240,20982)),
  (1000, (292613,25342)),
  (1000, (343874,3270))
]
theorem checked4 : chainCheck seg4 (some (177119,51358)) (1,524260) = true := by decide
theorem end4 : chainEnd seg4 (some (177119,51358)) = some (343874,3270) := by decide

def seg5 : List (Nat × (Nat × Nat)) := [
  (1000, (348936,4278)),
  (1000, (233377,65622)),
  (1000, (23195,174216)),
  (1000, (306622,35857)),
  (1000, (276338,54502)),
  (1000, (155787,118261)),
  (1000, (188636,105326)),
  (1000, (21822,192209)),
  (1000, (250711,81224)),
  (1000, (146871,136665))
]
theorem checked5 : chainCheck seg5 (some (343874,3270)) (1,524260) = true := by decide
theorem end5 : chainEnd seg5 (some (343874,3270)) = some (146871,136665) := by decide

def seg6 : List (Nat × (Nat × Nat)) := [
  (1000, (390907,18117)),
  (1000, (189321,122395)),
  (1000, (244597,98254)),
  (1000, (317577,65276)),
  (1000, (401981,26391)),
  (1000, (243125,109355)),
  (1000, (70049,199318)),
  (1000, (212270,131694)),
  (1000, (396680,43079)),
  (1000, (150479,169633))
]
theorem checked6 : chainCheck seg6 (some (146871,136665)) (1,524260) = true := by decide
theorem end6 : chainEnd seg6 (some (146871,136665)) = some (150479,169633) := by decide

def seg7 : List (Nat × (Nat × Nat)) := [
  (1000, (156176,170352)),
  (1000, (138252,182820)),
  (1000, (285977,112444)),
  (1000, (471279,23218)),
  (1000, (379214,72824)),
  (1000, (250605,140627)),
  (1000, (527820,5476)),
  (1000, (285952,129931)),
  (1000, (300262,126270)),
  (1000, (322999,118334))
]
theorem checked7 : chainCheck seg7 (some (150479,169633)) (1,524260) = true := by decide
theorem end7 : chainEnd seg7 (some (150479,169633)) = some (322999,118334) := by decide

def seg8 : List (Nat × (Nat × Nat)) := [
  (1000, (305020,130819)),
  (1000, (188795,192421)),
  (1000, (433798,73457)),
  (1000, (180665,203534)),
  (1000, (276295,159177)),
  (1000, (502298,49542)),
  (1000, (422669,92804)),
  (1000, (333579,140921)),
  (1000, (414991,103688)),
  (1000, (264834,182166))
]
theorem checked8 : chainCheck seg8 (some (322999,118334)) (1,524260) = true := by decide
theorem end8 : chainEnd seg8 (some (322999,118334)) = some (264834,182166) := by decide

def seg9 : List (Nat × (Nat × Nat)) := [
  (1000, (487056,74582)),
  (1000, (602460,20275)),
  (1000, (414265,117799)),
  (1000, (510466,73128)),
  (1000, (92781,285523)),
  (1000, (379109,145820)),
  (1000, (551745,62927)),
  (1000, (70768,306968)),
  (1000, (303834,193890)),
  (1000, (16992,340790))
]
theorem checked9 : chainCheck seg9 (some (264834,182166)) (1,524260) = true := by decide
theorem end9 : chainEnd seg9 (some (264834,182166)) = some (16992,340790) := by decide

def seg10 : List (Nat × (Nat × Nat)) := [
  (1000, (486353,109599)),
  (1000, (696641,7898)),
  (1000, (479747,119914)),
  (1000, (76966,324893)),
  (1000, (8854,362440)),
  (1000, (32888,353872)),
  (1000, (317587,214964)),
  (1000, (621976,66331)),
  (1000, (573051,94244)),
  (1000, (86922,340861))
]
theorem checked10 : chainCheck seg10 (some (16992,340790)) (1,524260) = true := by decide
theorem end10 : chainEnd seg10 (some (16992,340790)) = some (86922,340861) := by decide

def seg11 : List (Nat × (Nat × Nat)) := [
  (1000, (375665,199958)),
  (1000, (243660,269498)),
  (1000, (96350,346734)),
  (1000, (340291,228181)),
  (1000, (24506,389518)),
  (1000, (103237,353666)),
  (1000, (347966,234821)),
  (1000, (301839,261314)),
  (1000, (518252,156627)),
  (1000, (66128,386240))
]
theorem checked11 : chainCheck seg11 (some (86922,340861)) (1,524260) = true := by decide
theorem end11 : chainEnd seg11 (some (86922,340861)) = some (66128,386240) := by decide

def seg12 : List (Nat × (Nat × Nat)) := [
  (1000, (378224,233767)),
  (1000, (273834,289342)),
  (1000, (322408,268471)),
  (1000, (438462,213950)),
  (1000, (680569,96506)),
  (1000, (540837,169884)),
  (1000, (553416,167027)),
  (1000, (289294,302642)),
  (1000, (216684,342510)),
  (1000, (644476,132087))
]
theorem checked12 : chainCheck seg12 (some (66128,386240)) (1,524260) = true := by decide
theorem end12 : chainEnd seg12 (some (66128,386240)) = some (644476,132087) := by decide

def seg13 : List (Nat × (Nat × Nat)) := [
  (1000, (467218,224288)),
  (1000, (896506,13150)),
  (1000, (570873,179348)),
  (1000, (594640,171074)),
  (1000, (424814,259490)),
  (1000, (681732,134474)),
  (1000, (287490,334933)),
  (1000, (721291,121426)),
  (1000, (855987,57509)),
  (1000, (635363,171285))
]
theorem checked13 : chainCheck seg13 (some (644476,132087)) (1,524260) = true := by decide
theorem end13 : chainEnd seg13 (some (644476,132087)) = some (635363,171285) := by decide

def seg14 : List (Nat × (Nat × Nat)) := [
  (1000, (176791,404086)),
  (1000, (844030,74034)),
  (1000, (424691,287109)),
  (1000, (458514,273762)),
  (1000, (927340,42870)),
  (1000, (546294,236830)),
  (1000, (914997,56010)),
  (1000, (960818,36562)),
  (1000, (932453,54222)),
  (1000, (231728,408206))
]
theorem checked14 : chainCheck seg14 (some (635363,171285)) (1,524260) = true := by decide
theorem end14 : chainEnd seg14 (some (635363,171285)) = some (231728,408206) := by decide

def seg15 : List (Nat × (Nat × Nat)) := [
  (52, (621619,213453))
]
theorem checked15 : chainCheck seg15 (some (231728,408206)) (1,524260) = true := by decide
theorem end15 : chainEnd seg15 (some (231728,408206)) = some (621619,213453) := by decide

def allSegments : List (Nat × (Nat × Nat)) :=
  seg0 ++ seg1 ++ seg2 ++ seg3 ++ seg4 ++ seg5 ++ seg6 ++ seg7 ++ seg8 ++ seg9 ++ seg10 ++ seg11 ++ seg12 ++ seg13 ++ seg14 ++ seg15

theorem chainCheckedAll : chainCheck allSegments (some (5,1)) (1,524260) = true := by
  simp only [allSegments,chainCheck_append,chainEnd_append,checked0,end0,checked1,end1,checked2,end2,checked3,end3,checked4,end4,checked5,end5,checked6,end6,checked7,end7,checked8,end8,checked9,end9,checked10,end10,checked11,end11,checked12,end12,checked13,end13,checked14,end14,checked15,end15,Bool.true_and,Bool.and_true]

theorem chainTotalAll : chainTotal allSegments = 150052 := by decide
theorem chainEndAll : chainEnd allSegments (some (5,1)) = some (621619,213453) := by decide

theorem certified_full_prefix :
    (∀ i, i < 150052 → runFast i (some (5,1)) ≠ some (1,524260)) ∧
    runFast 150052 (some (5,1)) = some (621619,213453) := by
  have h := chain_sound allSegments (some (5,1)) (1,524260) chainCheckedAll
  simpa only [chainTotalAll,chainEndAll] using h

theorem source_section_mass_mono (n a k x y : Nat)
    (h : BB6.Agent8Section.run secNext n (some (a,k)) = some (x,y)) :
    a+2*k ≤ x+2*y := by
  induction n generalizing a k with
  | zero =>
      simp only [BB6.Agent8Section.run,Option.some.injEq,Prod.mk.injEq] at h
      omega
  | succ n ih =>
      rw [BB6.Agent8Section.run_succ_head] at h
      cases hs : secNext (a,k) with
      | none => simp [hs,BB6.Agent8Section.run_none] at h
      | some p =>
          rcases p with ⟨b,c⟩
          have hh : BB6.Agent8Section.run secNext n (some (b,c)) = some (x,y) := by
            simpa [hs] using h
          have hstep := section_mass_strict a k b c hs
          have hrest := ih b c hh
          omega

/-- Genuine source-defined blank section can NEVER reach the m=8
    low stopping state (1,524260), at any section time. -/
theorem m8_gate_unreachable :
    ¬ ∃ n : Nat, BB6.Agent8Section.run secNext n (some (5,1)) =
        some (1,524260) := by
  rintro ⟨n,hn⟩
  by_cases hbefore : n < 150052
  · have hne := certified_full_prefix.1 n hbefore
    exact hne ((runFast_eq_source n (some (5,1))).trans hn)
  · have hindex : 150052 + (n-150052) = n := by omega
    have hend : BB6.Agent8Section.run secNext 150052 (some (5,1)) =
        some (621619,213453) := by
      rw [←runFast_eq_source]
      exact certified_full_prefix.2
    rw [←hindex,BB6.Agent8Section.run_add,hend] at hn
    have hmon := source_section_mass_mono
      (n-150052) 621619 213453 1 524260 hn
    omega

/-- The single certified live endpoint excludes ALL genuine immediate-stopping
    section states of smaller rank, for all times. The earlier-time case follows
    because a `none` edge prevents any later live return. The later-time case
    follows from the original strictly increasing source rank. -/
theorem all_terminal_below_rank_unreachable (a k : Nat)
    (hstop : secNext (a,k) = none)
    (hrank : a+2*k < 1048525) :
    ¬ ∃ n : Nat, BB6.Agent8Section.run secNext n (some (5,1)) =
        some (a,k) := by
  rintro ⟨n,hn⟩
  have hend : BB6.Agent8Section.run secNext 150052 (some (5,1)) =
      some (621619,213453) := by
    rw [←runFast_eq_source]
    exact certified_full_prefix.2
  by_cases hbefore : n < 150052
  · have hpositive : 0 < 150052-n := by omega
    have hterminal : BB6.Agent8Section.run secNext (150052-n) (some (a,k)) = none := by
      cases hdiff : 150052-n with
      | zero => omega
      | succ d =>
          rw [BB6.Agent8Section.run_succ_head]
          simpa [hstop] using BB6.Agent8Section.run_none secNext d
    have hindex : n+(150052-n)=150052 := by omega
    rw [←hindex,BB6.Agent8Section.run_add,hn,hterminal] at hend
    contradiction
  · have hindex : 150052+(n-150052)=n := by omega
    rw [←hindex,BB6.Agent8Section.run_add,hend] at hn
    have hmon := source_section_mass_mono
      (n-150052) 621619 213453 a k hn
    omega

#print axioms chainCheckedAll
#print axioms certified_full_prefix
#print axioms m8_gate_unreachable
#print axioms all_terminal_below_rank_unreachable
end BB6.Agent1M8
