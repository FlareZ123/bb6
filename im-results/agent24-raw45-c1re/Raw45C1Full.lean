import Raw45Le0Parent
import Raw45Re0Parent
import Raw45Le1Parent
import Raw45ReParent
import Raw45ReWitness
import Symmetry
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace BB6.Agent24Raw45.C1Full
open BB6Coverage BB6.Agent24Raw45.ReAudit

theorem widen {B C : Nat} {p : PartialMachine} (h : B≤C) (cv : Cover (DecidedBelow B) p) : Cover (DecidedBelow C) p :=
  .leaf p fun m hm => match cv.sound m hm with
  | Or.inl hn => Or.inl hn
  | Or.inr ⟨n,hn,hh⟩ => Or.inr ⟨n,Nat.le_trans hn h,hh⟩

def swap : Fin 6 → Fin 6 := fun q => if q=4 then 5 else if q=5 then 4 else q
theorem swap_inv (q : Fin 6) : swap (swap q) = q := by
  have h : ∀ q : Fin 6, swap (swap q) = q := by decide +kernel
  exact h q

def swapEF : StatePerm := ⟨swap,swap,swap_inv,swap_inv⟩
def swapPartial (p : PartialMachine) : PartialMachine := fun s => (p (swap s.1,s.2)).map (Option.map (renameMove swapEF))

private theorem swapMove_inv (mv : Move) : renameMove swapEF (renameMove swapEF mv) = mv := by
  cases mv with
  | mk w r q => simp [renameMove,swapEF,swap_inv]

private theorem swapCompatible (p : PartialMachine) (m : Machine) (hm : compatible (swapPartial p) m) :
    compatible p (renameTable swapEF m) := by
  intro s t ht
  rcases s with ⟨q,a⟩
  have h : swapPartial p (swap q,a) = some (t.map (renameMove swapEF)) := by
    simp [swapPartial,swap_inv,ht]
  have h' := hm _ _ h
  change (m (swap q,a)).map (renameMove swapEF) = t
  rw [h']
  cases t <;> simp [swapMove_inv]

private theorem swapDecided (B : Nat) (m : Machine) (h : DecidedBelow B (renameTable swapEF m)) : DecidedBelow B m := by
  rcases h with hn | ⟨n,hn,hh⟩
  · left
    intro n
    have hrun := rename_run swapEF m blank n
    change run (renameTable swapEF m) n blank = _ at hrun
    have hs := hn n
    rw [hrun] at hs
    cases he : run m n blank <;> simp [he] at hs ⊢
  · right
    refine ⟨n,hn,?_⟩
    have hiff := relabeled_A_haltsAt swapEF m n
    change HaltsAfter (renameTable swapEF m) n ↔ HaltsAfter m n at hiff
    exact hiff.mp hh

theorem swapCover {B : Nat} {p : PartialMachine} (h : Cover (DecidedBelow B) p) : Cover (DecidedBelow B) (swapPartial p) :=
  .leaf _ fun m hm => swapDecided B m (h.sound _ (swapCompatible p m hm))

def parent : PartialMachine := fun s => match s.1.val,s.2 with
  | 0,false => some (some ⟨true,true,1⟩)
  | 0,true => some (some ⟨true,false,1⟩)
  | 1,false => some (some ⟨true,true,2⟩)
  | 1,true => some (some ⟨false,false,0⟩)
  | 2,false => some (some ⟨false,true,3⟩)
  | 3,false => some (some ⟨true,false,3⟩)
  | 3,true => some (some ⟨true,true,1⟩)
  | _,_ => none

def audit : Audit 473 := .split 11 (2,true) (byMove [
  .cycle 7 5 false (1),
  .cycle 0 17 true (-1),
  .cycle 7 5 false (1),
  .cycle 6 9 false (3),
  .cycle 0 17 false (3),
  .cycle 10 11 true (0),
  .cycle 8 8 false (1),
  (.ngram ⟨0,0xf,0xf,#[(.branch (.branch .leaf .leaf) .empty),(.branch (.branch .leaf .leaf) .empty),(.branch (.branch .empty .leaf) (.branch .leaf .leaf)),(.branch (.branch .empty .leaf) (.branch .leaf .leaf)),(.branch (.branch .empty .leaf) (.branch .empty .leaf)),(.branch (.branch .empty .leaf) (.branch .empty .leaf)),(.branch .leaf (.branch .leaf .leaf)),(.branch .leaf (.branch .leaf .leaf)),.empty,.empty,.empty,.empty]⟩),
  .cycle 15 1 false (-1),
  .cycle 1 13 true (-1),
  .cycle 12 7 false (0),
  .cycle 1 13 true (-1),
  .cycle 1 15 true (-1),
  .cycle 3 9 false (3),
  .cycle 5 7 false (2),
  .cycle 4 16 false (2),
  .covered Raw45Le0Parent.parent (widen (by decide : 372≤473) Raw45Le0Parent.cover),
  .covered Raw45Re0Parent.parent (widen (by decide : 387≤473) Raw45Re0Parent.cover),
  .covered Raw45Le1Parent.parent (widen (by decide : 375≤473) Raw45Le1Parent.cover),
  .covered Raw45ReParent.parent (widen (by decide : 473≤473) Raw45ReParent.cover),
  .covered (swapPartial Raw45Le0Parent.parent) (swapCover (widen (by decide : 372≤473) Raw45Le0Parent.cover)),
  .covered (swapPartial Raw45Re0Parent.parent) (swapCover (widen (by decide : 387≤473) Raw45Re0Parent.cover)),
  .covered (swapPartial Raw45Le1Parent.parent) (swapCover (widen (by decide : 375≤473) Raw45Le1Parent.cover)),
  .covered (swapPartial Raw45ReParent.parent) (swapCover (widen (by decide : 473≤473) Raw45ReParent.cover))
])
theorem checked : check 473 parent audit = true := by decide +kernel
theorem cover : Cover (DecidedBelow 473) parent := sound _ _ _ checked

theorem exact_parent_max :
    (∀ m, compatible parent m → DecidedBelow 473 m) ∧
    (∃ m, compatible parent m ∧ HaltsAfter m 472) := by
  refine ⟨cover.sound,ReWitness.witness,?_,ReWitness.exact_halt⟩
  intro s t h
  have H : allSlots (fun s => if (parent s).isSome then decide (Raw45ReParent.parent s = parent s) else true) = true := by decide +kernel
  have hs := allSlots_sound _ H s
  simp only [h,Option.isSome_some,ite_true,decide_eq_true_eq] at hs
  exact ReWitness.parent_compatible s t hs
#print axioms cover
#print axioms exact_parent_max
end BB6.Agent24Raw45.C1Full
