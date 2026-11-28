import Box27SliceCore
import Box27Symmetry
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace BB6.Agent49.Box27OrbitTree
open BB6Coverage BB6.Agent13BlankDelay BB6.Agent49.Box27Slice BB6.Agent49.Box27Symmetry BB6.Agent16WeightedSymmetry
open BB6.Agent13.Box17 (decode slot Witness tableEq tableEq_sound)

def representative (v : Fin 25) : Bool := decide (v.val ≤ 20)
def reps : List (Fin 25) := (List.finRange 25).filter representative

theorem representative_or_renamed (v : Fin 25) : representative v = true ∨ representative (efCode v) = true := by revert v; decide

def canSplit (p : PartialMachine) (s : Fin 12) : Bool :=
  tableEq (renamePartial ef p) p && decide (ef.backward (slot s).1 = (slot s).1)

theorem split_ef_good (B : Nat) (p : PartialMachine) (s : Fin 12)
    (h : canSplit p s = true)
    (hgood : ∀ v : Fin 25, representative v = true → Good B (refine p (slot s) (decode v))) : Good B p := by
  have hc := Bool.and_eq_true_iff.mp h
  have heq := tableEq_sound _ _ hc.1
  have hs : ef.backward (slot s).1 = (slot s).1 := of_decide_eq_true hc.2
  intro m hm
  obtain ⟨v,hv⟩ := BB6.Agent49.Box27Slice.decode_surjective (m (slot s))
  rcases representative_or_renamed v with hr | hr
  · apply hgood v hr m
    rw [hv]
    exact compatible_refine p m (slot s) hm
  · apply (weightedBound_rename_iff B ef (by decide) m).mp
    apply hgood (efCode v) hr (renameTable ef m)
    have hp : compatible p (renameTable ef m) := heq ▸ rename_compatible ef hm
    have ht : renameTable ef m (slot s) = decode (efCode v) := by
      change (m (ef.backward (slot s).1,(slot s).2)).map (renameMove ef) = _
      rw [hs]
      have hpair : ((slot s).1,(slot s).2) = slot s := Prod.eta _
      rw [hpair,← hv,ef_code_decode]
    rw [← ht]
    exact compatible_refine p (renameTable ef m) (slot s) hp

inductive Tree where
  | terminal (w : Witness)
  | automata (c : BB6.Agent4Automata.Cert)
  | branch (s : Fin 12) (kids : List (Fin 25 × Tree))
  | orbit (s : Fin 12) (kids : List (Fin 25 × Tree))

def audit (B : Nat) (known : Array PartialMachine) : Nat → PartialMachine → Tree → Bool
  | _,p,.terminal w => BB6.Agent13.Box17.leafCheck B known p w
  | _,p,.automata c => BB6.Agent4Automata.check p c
  | 0,_,.branch _ _ | 0,_,.orbit _ _ => false
  | fuel+1,p,.branch s kids =>
    (kids.map Prod.fst == List.finRange 25) &&
    kids.all (fun (v,t) => audit B known fuel (refine p (slot s) (decode v)) t)
  | fuel+1,p,.orbit s kids =>
    canSplit p s && (kids.map Prod.fst == reps) &&
    kids.all (fun (v,t) => audit B known fuel (refine p (slot s) (decode v)) t)

theorem audit_sound (B : Nat) (known : Array PartialMachine)
    (hknown : ∀ (i : Nat) (q : PartialMachine), known[i]? = some q → Good B q) (fuel : Nat) (p : PartialMachine) (t : Tree)
    (h : audit B known fuel p t = true) : Good B p := by
  induction fuel generalizing p t with
  | zero =>
    cases t with
    | terminal w => exact BB6.Agent13.Box17.leafCheck_sound B known hknown p w h
    | automata c => exact automata_sound B p c h
    | branch s kids | orbit s kids => simp [audit] at h
  | succ fuel ih =>
    cases t with
    | terminal w => exact BB6.Agent13.Box17.leafCheck_sound B known hknown p w h
    | automata c => exact automata_sound B p c h
    | branch s kids =>
      simp only [audit,Bool.and_eq_true,beq_iff_eq] at h
      apply split_good B p s
      intro v
      have hmem : v ∈ kids.map Prod.fst := by rw [h.1]; simp
      obtain ⟨⟨w,u⟩,hmem,hw⟩ := List.mem_map.mp hmem
      dsimp at hw
      subst w
      exact ih _ u (List.all_eq_true.mp h.2 (v,u) hmem)
    | orbit s kids =>
      simp only [audit,Bool.and_eq_true,beq_iff_eq] at h
      apply split_ef_good B p s h.1.1
      intro v hv
      have hmem : v ∈ kids.map Prod.fst := by rw [h.1.2]; simp [reps,hv]
      obtain ⟨⟨w,u⟩,hmem,hw⟩ := List.mem_map.mp hmem
      dsimp at hw
      subst w
      exact ih _ u (List.all_eq_true.mp h.2 (v,u) hmem)

#print axioms split_ef_good
#print axioms audit_sound
end BB6.Agent49.Box27OrbitTree
