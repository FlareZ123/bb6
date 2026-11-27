import CanonicalPartial
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace BB6.Agent19Raw40.A0RC
open BB6Coverage BB6.Agent13BlankDelay BB6.Agent31ThreeHole BB6.Agent10ZipAudit BB6.Agent48PrefixAudit BB6.Agent47PartialAudit BB6.Agent19CanonicalPartial BB6.Agent47CanonicalFrontier BB6.Agent50TNFPilot

/-- The complete six-hole parent with A1 fixed to 0RC. -/
def p : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0,false => some (some ⟨true,true,1⟩)
  | 0,true => some (some ⟨false,true,2⟩)
  | 1,false => some (some ⟨true,true,2⟩)
  | 2,false => some (some ⟨false,true,3⟩)
  | 3,false => some (some ⟨true,false,3⟩)
  | 3,true => some (some ⟨true,false,0⟩)
  | _,_ => none

def tree : PartialAudit := .split 7 (2,true) (byPartialMove [
  .unresolved,
  .unresolved,
  .closed (.cycle 9 1 false (1)),
  .closed (.cycle 8 1 false (0)),
  .unresolved,
  .unresolved,
  .closed (.cycle 0 10 true (0)),
  .unresolved,
  .closed (.cycle 11 1 false (5)),
  .unresolved,
  .unresolved,
  .unresolved,
  .unresolved,
  .unresolved,
  .unresolved,
  .closed (.cycle 8 1 false (0)),
  .unresolved,
  .unresolved,
  .closed (.cycle 0 10 true (0)),
  .unresolved,
  .closed (.cycle 2 8 true (0)),
  .unresolved,
  .unresolved,
  .unresolved])

theorem root : p initialSlot = some (some ⟨true,true,1⟩) := by decide
theorem nohalt : weightedTNFNoAssignedHalt p := by
  intro s; rcases s with ⟨q,b⟩
  have hq : q = 0 ∨ q = 1 ∨ q = 2 ∨ q = 3 ∨ q = 4 ∨ q = 5 := by omega
  rcases hq with rfl|rfl|rfl|rfl|rfl|rfl <;> cases b <;> decide
theorem supported : TNFSupport p 4 := supportOK_sound _ _ (by decide)
theorem checked : canonicalCheck 888 p 4 tree = true := by decide

def remaining := canonicalResiduals p 4 tree

theorem count : remaining.length = 13 := by decide

def equalTable (p q : PartialMachine) : Bool :=
  (List.finRange 6).all fun s => [false,true].all fun b => decide (p (s,b)=q (s,b))
theorem equalTable_sound (p q : PartialMachine) (h : equalTable p q = true) : p = q := by
  funext s
  rcases s with ⟨q',b⟩
  have hq := List.all_eq_true.mp h q' (List.mem_finRange q')
  have hb : b ∈ [false,true] := by cases b <;> simp
  exact of_decide_eq_true (List.all_eq_true.mp hq b hb)

def child (mv : Move) : PartialMachine := refine p (2,true) (some mv)

/-- Each of the thirteen canonical unresolved children, paired with its bound. -/
def bounds : List (Move × Nat) := [
  (⟨false,false,0⟩,81),
  (⟨false,false,1⟩,340),
  (⟨false,false,4⟩,470),
  (⟨false,true,1⟩,131),
  (⟨false,true,3⟩,138),
  (⟨false,true,4⟩,146),
  (⟨true,false,0⟩,124),
  (⟨true,false,1⟩,90),
  (⟨true,false,2⟩,63),
  (⟨true,false,4⟩,354),
  (⟨true,true,1⟩,888),
  (⟨true,true,3⟩,75),
  (⟨true,true,4⟩,643)]

theorem partition : remaining.all (fun e => bounds.any (fun x => equalTable e.2 (child x.1))) = true := by decide
theorem boundOK : bounds.all (fun x => decide (x.2 ≤ 888)) = true := by decide

/-- A complete consumer of the thirteen five-hole child theorems. -/
theorem close (h : ∀ e ∈ bounds, ∀ m, TNFQuotientCompatible (child e.1) m → WeightedBound e.2 m) :
    ∀ m, TNFQuotientCompatible p m → WeightedBound 888 m := by
  intro m hm
  rcases canonicalSound 888 p 4 tree (by decide) supported root nohalt checked m hm with hb | ⟨e,he,hq⟩
  · exact hb
  · have hh := List.all_eq_true.mp partition e he
    obtain ⟨x,hx,heq⟩ := List.any_eq_true.mp hh
    have eq := equalTable_sound _ _ heq
    have hb := h x hx m (eq ▸ hq)
    have hb' : x.2 ≤ 888 := of_decide_eq_true (List.all_eq_true.mp boundOK x hx)
    intro k d hk hd
    exact Nat.le_trans (hb k d hk hd) hb'

#print axioms count
#print axioms close
end BB6.Agent19Raw40.A0RC
