import Box17AuditCore
import Raw10EncodedSourceBridge
import Box27MaskedCounter3
import Box27ExceptionalFAR

set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace BB6.Agent49.Box27Slice22
open BB6Coverage BB6.Agent13BlankDelay BB6.Agent49Box BB6.Agent49BoxBridge
open BB6.Agent13.Box17 (decode slot Witness leafCheck leafCheck_sound)

def root : PartialMachine := fun s =>
  match s with
  | (0,false) => some (decode 8)
  | (1,false) => some (decode 11)
  | (2,false) => some (decode 13)
  | (2,true) => some (decode 13)
  | (3,false) => some (decode 14)
  | (3,true) => some (decode 17)
  | (4,false) => some (decode 22)
  | _ => none

/-- The only unresolved one-hole cylinder: F1 free, E1=1RD, F0=1RA. -/
def exceptional : PartialMachine := fun s =>
  match s with
  | (0,false) => some (decode 8)
  | (0,true) => some (decode 24)
  | (1,false) => some (decode 11)
  | (1,true) => some (decode 8)
  | (2,false) | (2,true) => some (decode 13)
  | (3,false) => some (decode 14)
  | (3,true) => some (decode 17)
  | (4,false) => some (decode 22)
  | (4,true) => some (decode 15)
  | (5,false) => some (decode 4)
  | _ => none

/-- A bound conditional only on avoiding the explicit 25-completion holdout. -/
abbrev Good (B : Nat) (p : PartialMachine) : Prop :=
  ∀ m, compatible p m → ¬compatible exceptional m → WeightedBound B m

def externalTable (k : Nat) : PartialMachine :=
  if k=0 then BB6.Agent49.Box27MaskedCounter3.table .e17
  else BB6.Agent49.Box27MaskedCounter3.table .e9

theorem decode_surjective (t : Transition) : ∃ v : Fin 25, decode v = t := by
  cases t with
  | none => exact ⟨0,rfl⟩
  | some mv =>
    rcases mv with ⟨w,r,q⟩
    revert q r w
    decide

inductive Tree where
  | terminal (w : Witness)
  | automata (c : BB6.Agent4Automata.Cert)
  | masked (k : Nat)
  | excluded
  | branch (s : Fin 12) (kids : List (Fin 25 × Tree))

def audit (B : Nat) : Nat → PartialMachine → Tree → Bool
  | _,p,.terminal w => leafCheck B #[] p w
  | _,p,.automata c => BB6.Agent4Automata.check p c
  | _,p,.masked k => BB6.Agent13.Box17.tableEq p (externalTable k)
  | _,p,.excluded => BB6.Agent13.Box17.tableEq p exceptional
  | 0,_,.branch _ _ => false
  | fuel+1,p,.branch s kids =>
    (kids.map Prod.fst == List.finRange 25) &&
    kids.all (fun (v,t) => audit B fuel (refine p (slot s) (decode v)) t)

theorem terminal_sound (B : Nat) (p : PartialMachine) (w : Witness)
    (h : leafCheck B #[] p w = true) : Good B p := by
  intro m hm _
  apply leafCheck_sound B #[] _ p w h m hm
  intro i q hi
  simp at hi

theorem automata_sound (B : Nat) (p : PartialMachine) (c : BB6.Agent4Automata.Cert)
    (h : BB6.Agent4Automata.check p c = true) : Good B p := by
  intro m hm _
  exact weighted_of_never B m (BB6.Agent4Automata.never p c h m hm)


theorem masked_sound (B : Nat) (p : PartialMachine) (k : Nat)
    (h : BB6.Agent13.Box17.tableEq p (externalTable k) = true) : Good B p := by
  have heq := BB6.Agent13.Box17.tableEq_sound p (externalTable k) h
  intro m hm _
  have hc : compatible (externalTable k) m := heq ▸ hm
  by_cases hk : k=0
  · have hv : compatible (BB6.Agent49.Box27MaskedCounter3.table .e17) m := by
      simpa [externalTable,hk] using hc
    exact weighted_of_never B m (BB6.Agent49.Box27MaskedCounter3.never .e17 m hv)
  · have hv : compatible (BB6.Agent49.Box27MaskedCounter3.table .e9) m := by
      simpa [externalTable,hk] using hc
    exact weighted_of_never B m (BB6.Agent49.Box27MaskedCounter3.never .e9 m hv)

theorem excluded_sound (B : Nat) (p : PartialMachine)
    (h : BB6.Agent13.Box17.tableEq p exceptional = true) : Good B p := by
  have heq := BB6.Agent13.Box17.tableEq_sound p exceptional h
  intro m hm hnot
  exact False.elim (hnot (heq ▸ hm))

theorem split_good (B : Nat) (p : PartialMachine) (s : Fin 12)
    (h : ∀ v : Fin 25, Good B (refine p (slot s) (decode v))) : Good B p := by
  intro m hm hnot
  obtain ⟨v,hv⟩ := decode_surjective (m (slot s))
  apply h v m
  rw [hv]
  exact compatible_refine p m (slot s) hm
  exact hnot

theorem audit_sound (B : Nat) (fuel : Nat) (p : PartialMachine) (t : Tree)
    (h : audit B fuel p t = true) : Good B p := by
  induction fuel generalizing p t with
  | zero =>
    cases t with
    | terminal w => exact terminal_sound B p w h
    | automata c => exact automata_sound B p c h
    | masked k => exact masked_sound B p k h
    | excluded => exact excluded_sound B p h
    | branch s kids => simp [audit] at h
  | succ fuel ih =>
    cases t with
    | terminal w => exact terminal_sound B p w h
    | automata c => exact automata_sound B p c h
    | masked k => exact masked_sound B p k h
    | excluded => exact excluded_sound B p h
    | branch s kids =>
      simp only [audit,Bool.and_eq_true,beq_iff_eq] at h
      apply split_good B p s
      intro v
      have hmem : v ∈ kids.map Prod.fst := by rw [h.1]; simp
      obtain ⟨⟨w,u⟩,hmem,hw⟩ := List.mem_map.mp hmem
      dsimp at hw
      subst w
      exact ih _ u (List.all_eq_true.mp h.2 (v,u) hmem)

theorem parent_compatible (m : Machine) (hm : Fits raw10Remainder[27]! m)
    (hd0 : m (3,false) = decode 14) (hd1 : m (3,true) = decode 17)
    (he : m (4,false) = decode 22) : compatible root m := by
  have e0 : raw10Remainder[27]! (0,false) = [decode 8] := by decide
  have e1 : raw10Remainder[27]! (1,false) = [decode 11] := by decide
  have e2 : raw10Remainder[27]! (2,false) = [decode 13] := by decide
  have e3 : raw10Remainder[27]! (2,true) = [decode 13] := by decide
  have h0 : m (0,false) = decode 8 := by simpa [e0] using hm (0,false)
  have h1 : m (1,false) = decode 11 := by simpa [e1] using hm (1,false)
  have h2 : m (2,false) = decode 13 := by simpa [e2] using hm (2,false)
  have h3 : m (2,true) = decode 13 := by simpa [e3] using hm (2,true)
  intro s t ht
  obtain ⟨q,b⟩ := s
  have hq : q=0 ∨ q=1 ∨ q=2 ∨ q=3 ∨ q=4 ∨ q=5 := by omega
  rcases hq with rfl|rfl|rfl|rfl|rfl|rfl <;> cases b <;>
    simp [root] at ht ⊢ <;> simp_all


/-- This equality is an exact equality of original partial machine tables,
    including the missing F1 slot. -/
theorem exceptional_far_table :
    exceptional = BB6.Agent49.Box27ExceptionalFAR.table := by
  funext s
  obtain ⟨q,b⟩ := s
  have hq : q=0 ∨ q=1 ∨ q=2 ∨ q=3 ∨ q=4 ∨ q=5 := by omega
  rcases hq with rfl|rfl|rfl|rfl|rfl|rfl <;> cases b <;>
    decide

/-- Source-level nonhalting for all 25 completions of the former holdout. -/
theorem exceptional_never (m : Machine) (hm : compatible exceptional m) :
    NeverHalts m := by
  rw [exceptional_far_table] at hm
  exact BB6.Agent49.Box27ExceptionalFAR.never m hm

#print axioms exceptional_far_table
#print axioms exceptional_never

#print axioms masked_sound
#print axioms excluded_sound
#print axioms audit_sound
#print axioms parent_compatible
end BB6.Agent49.Box27Slice22
