import CanonicalPartial
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace BB6.Agent19Raw40.A0RD
open BB6Coverage BB6.Agent13BlankDelay BB6.Agent31ThreeHole BB6.Agent10ZipAudit BB6.Agent48PrefixAudit BB6.Agent47PartialAudit BB6.Agent19CanonicalPartial BB6.Agent47CanonicalFrontier BB6.Agent50TNFPilot

/-- The complete six-hole parent with A1 fixed to 0RD. -/
def p : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0,false => some (some ⟨true,true,1⟩)
  | 0,true => some (some ⟨false,true,3⟩)
  | 1,false => some (some ⟨true,true,2⟩)
  | 2,false => some (some ⟨false,true,3⟩)
  | 3,false => some (some ⟨true,false,3⟩)
  | 3,true => some (some ⟨true,false,0⟩)
  | _,_ => none

def tree : PartialAudit := .split 9 (1,true) (byPartialMove [
  .closed (.cycle 11 1 false (1)),
  .closed (.cycle 7 8 false (1)),
  .unresolved,
  .closed (.cycle 7 3 false (1)),
  .unresolved,
  .unresolved,
  .closed (.cycle 0 14 true (0)),
  .closed (.cycle 7 9 true (0)),
  .unresolved,
  .closed (.cycle 3 13 true (0)),
  .unresolved,
  .unresolved,
  .closed (.cycle 6 4 true (0)),
  .unresolved,
  .unresolved,
  .closed (.cycle 7 3 false (1)),
  .unresolved,
  .unresolved,
  .closed (.cycle 0 14 true (0)),
  .closed (.cycle 1 11 true (0)),
  .unresolved,
  .closed (.cycle 10 11 true (1)),
  .unresolved,
  .unresolved])

theorem root : p initialSlot = some (some ⟨true,true,1⟩) := by decide
theorem nohalt : weightedTNFNoAssignedHalt p := by
  intro s; rcases s with ⟨q,b⟩
  have hq : q = 0 ∨ q = 1 ∨ q = 2 ∨ q = 3 ∨ q = 4 ∨ q = 5 := by omega
  rcases hq with rfl|rfl|rfl|rfl|rfl|rfl <;> cases b <;> decide
theorem supported : TNFSupport p 4 := supportOK_sound _ _ (by decide)
theorem checked : canonicalCheck 1132 p 4 tree = true := by decide

def remaining := canonicalResiduals p 4 tree

theorem count : remaining.length = 9 := by decide

def equalTable (p q : PartialMachine) : Bool :=
  (List.finRange 6).all fun s => [false,true].all fun b => decide (p (s,b)=q (s,b))
theorem equalTable_sound (p q : PartialMachine) (h : equalTable p q = true) : p = q := by
  funext s
  rcases s with ⟨q',b⟩
  have hq := List.all_eq_true.mp h q' (List.mem_finRange q')
  have hb : b ∈ [false,true] := by cases b <;> simp
  exact of_decide_eq_true (List.all_eq_true.mp hq b hb)

def child (mv : Move) : PartialMachine := refine p (1,true) (some mv)

/-- Each of the nine canonical unresolved children, paired with its bound. -/
def bounds : List (Move × Nat) := [
  (⟨false,false,2⟩,106),
  (⟨false,false,4⟩,1132),
  (⟨false,true,2⟩,225),
  (⟨false,true,4⟩,214),
  (⟨true,false,1⟩,102),
  (⟨true,false,2⟩,47),
  (⟨true,false,4⟩,266),
  (⟨true,true,2⟩,64),
  (⟨true,true,4⟩,125)]

theorem partition : remaining.all (fun e => bounds.any (fun x => equalTable e.2 (child x.1))) = true := by decide
theorem boundOK : bounds.all (fun x => decide (x.2 ≤ 1132)) = true := by decide

/-- A complete consumer of the nine five-hole child theorems. -/
theorem close (h : ∀ e ∈ bounds, ∀ m, TNFQuotientCompatible (child e.1) m → WeightedBound e.2 m) :
    ∀ m, TNFQuotientCompatible p m → WeightedBound 1132 m := by
  intro m hm
  rcases canonicalSound 1132 p 4 tree (by decide) supported root nohalt checked m hm with hb | ⟨e,he,hq⟩
  · exact hb
  · have hh := List.all_eq_true.mp partition e he
    obtain ⟨x,hx,heq⟩ := List.any_eq_true.mp hh
    have eq := equalTable_sound _ _ heq
    have hb := h x hx m (eq ▸ hq)
    have hb' : x.2 ≤ 1132 := of_decide_eq_true (List.all_eq_true.mp boundOK x hx)
    intro k d hk hd
    exact Nat.le_trans (hb k d hk hd) hb'

#print axioms count
#print axioms close
end BB6.Agent19Raw40.A0RD
