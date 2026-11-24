import QueueCoverageContract

namespace BB6.Agent32QueueImplication
open BB6.Agent13QueueCoverage
universe u

/-- Backwards cylinder closure. No machine-level compatibility quotient is
needed: each node is either universally safe or must retain an unsafe child. -/
def LocalClosure {Node : Type u} (decide : Node → QueueDecision Node)
    (Safe : Node → Prop) : Prop :=
  ∀ x, match decide x with
  | .halt children => (∀ y, y ∈ children → Safe y) → Safe x
  | .nonhalt => Safe x
  | .unknown => True

theorem localClosure_classifier {Node : Type u}
    (decide : Node → QueueDecision Node) (Safe : Node → Prop)
    (h : LocalClosure decide Safe) :
    ClassifierSound decide (fun _ : Unit => False) (fun x _ => ¬ Safe x) := by
  classical
  intro x _ hb
  have hc := h x
  cases hd : decide x with
  | halt children =>
    rw [hd] at hc
    apply Or.inr
    apply Classical.byContradiction; intro hn
    apply hb
    apply hc
    intro y hy
    apply Classical.byContradiction; intro hny
    exact hn ⟨y, hy, hny⟩
  | nonhalt =>
    rw [hd] at hc
    exact hb hc
  | unknown => trivial

theorem q0_safe_of_chunk_holdouts {Node : Type u}
    (decide : Node → QueueDecision Node) (Safe : Node → Prop)
    (hsound : LocalClosure decide Safe) (root : Node)
    (ranges : List (Nat × Nat))
    (hpart : ChunkPartition (q0 decide root) ranges) (fuel : Nat)
    (hdrain : ∀ r, r ∈ ranges →
      (runUpdates decide fuel (chunkQueue (q0 decide root) r.1 r.2)).active = [])
    (hcert : ∀ r, r ∈ ranges → ∀ y,
      y ∈ (runUpdates decide fuel (chunkQueue (q0 decide root) r.1 r.2)).holdout → Safe y) :
    Safe root := by
  classical
  apply Classical.byContradiction; intro hb
  exact q0_rootGood_of_chunk_holdouts decide (fun _ : Unit => False)
    (fun x _ => ¬ Safe x) (localClosure_classifier decide Safe hsound)
    root ranges hpart fuel hdrain
    (fun r hr y hy _ hbad => hbad (hcert r hr y hy)) () hb

#print axioms localClosure_classifier
#print axioms q0_safe_of_chunk_holdouts
end BB6.Agent32QueueImplication
