import Raw124M448Safe
import Raw124M448Kid4
import Raw124M448Kid10
import Raw124M448Kid16
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace BB6.Agent4.Raw124M448
open BB6Coverage BB6.Agent13BlankDelay BB6.Agent50TNFPilot BB6.Agent31ThreeHole BB6.Agent10ZipAudit BB6Coverage.Agent10ZipAudit

theorem never4 (m : Machine) (hm : compatible (kid mv4) m) : NeverHalts m := by
  have he : kid mv4 = BB6.Agent4.Raw124M448Kid4.table := tableOK_sound _ _ (by decide)
  rw [he] at hm
  exact BB6.Agent4.Raw124M448Kid4.never m hm
theorem never10 (m : Machine) (hm : compatible (kid mv10) m) : NeverHalts m := by
  have he : kid mv10 = BB6.Agent4.Raw124M448Kid10.table := tableOK_sound _ _ (by decide)
  rw [he] at hm
  exact BB6.Agent4.Raw124M448Kid10.never m hm
theorem never16 (m : Machine) (hm : compatible (kid mv16) m) : NeverHalts m := by
  have he : kid mv16 = BB6.Agent4.Raw124M448Kid16.table := tableOK_sound _ _ (by decide)
  rw [he] at hm
  exact BB6.Agent4.Raw124M448Kid16.never m hm
def kids : Move → Audit := byMove [
.proven (kid mv0) never0,
.last 4136170 (2,true),
.last 91503 (2,true),
.proven (kid mv3) never3,
.proven (kid mv4) never4,
.last 4136170 (2,true),
.proven (kid mv6) never6,
.proven (kid mv7) never7,
.last 91503 (2,true),
.proven (kid mv9) never9,
.proven (kid mv10) never10,
.proven (kid mv11) never11,
.proven (kid mv12) never12,
.proven (kid mv13) never13,
.last 91503 (2,true),
.proven (kid mv15) never15,
.proven (kid mv16) never16,
.proven (kid mv17) never17,
.proven (kid mv18) never18,
.proven (kid mv19) never19,
.last 91503 (2,true),
.proven (kid mv21) never21,
.last 4136174 (2,true),
.proven (kid mv23) never23]
theorem child0 : zipCheck 4136175 (refine table (0,true) (some mv0)) (kids mv0) = true := by
  rw [kid_eq]
  rfl
theorem child1 : zipCheck 4136175 (refine table (0,true) (some mv1)) (kids mv1) = true := by
  rw [kid_eq]
  exact checked1
theorem child2 : zipCheck 4136175 (refine table (0,true) (some mv2)) (kids mv2) = true := by
  rw [kid_eq]
  exact checked2
theorem child3 : zipCheck 4136175 (refine table (0,true) (some mv3)) (kids mv3) = true := by
  rw [kid_eq]
  rfl
theorem child4 : zipCheck 4136175 (refine table (0,true) (some mv4)) (kids mv4) = true := by
  rw [kid_eq]
  rfl
theorem child5 : zipCheck 4136175 (refine table (0,true) (some mv5)) (kids mv5) = true := by
  rw [kid_eq]
  exact checked5
theorem child6 : zipCheck 4136175 (refine table (0,true) (some mv6)) (kids mv6) = true := by
  rw [kid_eq]
  rfl
theorem child7 : zipCheck 4136175 (refine table (0,true) (some mv7)) (kids mv7) = true := by
  rw [kid_eq]
  rfl
theorem child8 : zipCheck 4136175 (refine table (0,true) (some mv8)) (kids mv8) = true := by
  rw [kid_eq]
  exact checked8
theorem child9 : zipCheck 4136175 (refine table (0,true) (some mv9)) (kids mv9) = true := by
  rw [kid_eq]
  rfl
theorem child10 : zipCheck 4136175 (refine table (0,true) (some mv10)) (kids mv10) = true := by
  rw [kid_eq]
  rfl
theorem child11 : zipCheck 4136175 (refine table (0,true) (some mv11)) (kids mv11) = true := by
  rw [kid_eq]
  rfl
theorem child12 : zipCheck 4136175 (refine table (0,true) (some mv12)) (kids mv12) = true := by
  rw [kid_eq]
  rfl
theorem child13 : zipCheck 4136175 (refine table (0,true) (some mv13)) (kids mv13) = true := by
  rw [kid_eq]
  rfl
theorem child14 : zipCheck 4136175 (refine table (0,true) (some mv14)) (kids mv14) = true := by
  rw [kid_eq]
  exact checked14
theorem child15 : zipCheck 4136175 (refine table (0,true) (some mv15)) (kids mv15) = true := by
  rw [kid_eq]
  rfl
theorem child16 : zipCheck 4136175 (refine table (0,true) (some mv16)) (kids mv16) = true := by
  rw [kid_eq]
  rfl
theorem child17 : zipCheck 4136175 (refine table (0,true) (some mv17)) (kids mv17) = true := by
  rw [kid_eq]
  rfl
theorem child18 : zipCheck 4136175 (refine table (0,true) (some mv18)) (kids mv18) = true := by
  rw [kid_eq]
  rfl
theorem child19 : zipCheck 4136175 (refine table (0,true) (some mv19)) (kids mv19) = true := by
  rw [kid_eq]
  rfl
theorem child20 : zipCheck 4136175 (refine table (0,true) (some mv20)) (kids mv20) = true := by
  rw [kid_eq]
  exact checked20
theorem child21 : zipCheck 4136175 (refine table (0,true) (some mv21)) (kids mv21) = true := by
  rw [kid_eq]
  rfl
theorem child22 : zipCheck 4136175 (refine table (0,true) (some mv22)) (kids mv22) = true := by
  rw [kid_eq]
  exact checked22
theorem child23 : zipCheck 4136175 (refine table (0,true) (some mv23)) (kids mv23) = true := by
  rw [kid_eq]
  rfl
theorem all_kids : allMoves (fun mv => zipCheck 4136175 (refine table (0,true) (some mv)) (kids mv)) = true := by
  unfold allMoves
  apply List.all_eq_true.mpr
  intro q _
  apply List.all_eq_true.mpr
  intro w _
  apply List.all_eq_true.mpr
  intro r _
  have hq : q=0 ∨ q=1 ∨ q=2 ∨ q=3 ∨ q=4 ∨ q=5 := by omega
  rcases hq with rfl|rfl|rfl|rfl|rfl|rfl
  all_goals cases w <;> cases r
  · exact child0
  · exact child6
  · exact child12
  · exact child18
  · exact child1
  · exact child7
  · exact child13
  · exact child19
  · exact child2
  · exact child8
  · exact child14
  · exact child20
  · exact child3
  · exact child9
  · exact child15
  · exact child21
  · exact child4
  · exact child10
  · exact child16
  · exact child22
  · exact child5
  · exact child11
  · exact child17
  · exact child23
theorem root_ok : table initialSlot = some (some ⟨true,true,1⟩) := by decide
theorem no_assigned_halt : weightedTNFNoAssignedHalt table := by
  intro s; rcases s with ⟨q,b⟩
  have h : ∀ q : Fin 6, ∀ b : Bool, table (q,b) ≠ some none := by decide
  exact h q b
def audit : Audit := .split 91502 (0,true) kids
theorem checked : zipCheck 4136175 table audit = true := by
  have hh : table (0,true) = none := by decide
  have hw : weightOK table (0,true) 91502 4136175 = true := by decide
  unfold audit
  rw [zipCheck.eq_5]
  simp only [zipQueryOK,root_read,hh,hw,decide_true,Bool.and_self,all_kids]
theorem bound (m : Machine) (hm : compatible table m) : WeightedBound 4136175 m :=
  (certifiedZip 4136175 table audit root_ok no_assigned_halt checked).sound m hm
#print axioms bound
end BB6.Agent4.Raw124M448
