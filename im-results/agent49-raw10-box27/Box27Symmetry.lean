import WeightedSymmetry
import Box27EarlyTerminal

set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace BB6.Agent49.Box27Symmetry
open BB6Coverage BB6.Agent13BlankDelay BB6.Agent49Box BB6.Agent49BoxBridge
open BB6.Agent13.Box17 (decode)
open BB6.Agent16WeightedSymmetry

def efState (q : Fin 6) : Fin 6 := if q = 4 then 5 else if q = 5 then 4 else q
theorem ef_involutive : ∀ q : Fin 6, efState (efState q) = q := by decide
def ef : StatePerm := ⟨efState, efState, ef_involutive, ef_involutive⟩
def efCode (v : Fin 25) : Fin 25 :=
  Fin.ofNat 25 (if 17 ≤ v.val ∧ v.val ≤ 20 then v.val + 4
    else if 21 ≤ v.val then v.val - 4 else v.val)
theorem ef_code_decode : ∀ v : Fin 25,
    (decode v).map (renameMove ef) = decode (efCode v) := by decide
theorem ef_code_involutive : ∀ v : Fin 25, efCode (efCode v) = v := by decide

theorem decode_surjective (t : Transition) : ∃ v : Fin 25, decode v = t := by
  cases t with
  | none => exact ⟨0,rfl⟩
  | some mv =>
    rcases mv with ⟨w,r,q⟩
    revert q r w
    decide

/-- The entire source Box27, including the D0 restriction, is E/F invariant. -/
theorem source_mem (q : Fin 6) (r : Bool) (v : Fin 25)
    (h : decode v ∈ raw10Remainder[27]! (ef.backward q,r)) :
    decode (efCode v) ∈ raw10Remainder[27]! (q,r) := by
  revert q r v
  decide

theorem fits_renamed (m : Machine) (hm : Fits raw10Remainder[27]! m) :
    Fits raw10Remainder[27]! (renameTable ef m) := by
  intro s
  rcases s with ⟨q,r⟩
  obtain ⟨v,hv⟩ := decode_surjective (m (ef.backward q,r))
  change (m (ef.backward q,r)).map (renameMove ef) ∈ raw10Remainder[27]! (q,r)
  rw [← hv,ef_code_decode]
  apply source_mem q r v
  rw [hv]
  exact hm (ef.backward q,r)

/-- A five-coordinate predicate with the other three source slots unrestricted. -/
abbrev Predicate := Fin 25 → Fin 25 → Fin 25 → Fin 25 → Fin 25 → Bool

def Valid (B : Nat) (p : Predicate) : Prop :=
  ∀ m : Machine, Fits raw10Remainder[27]! m →
  ∀ d0 d1 e0 b1 f0 : Fin 25,
  m (3,false) = decode d0 → m (3,true) = decode d1 →
  m (4,false) = decode e0 → m (1,true) = decode b1 →
  m (5,false) = decode f0 →
  p d0 d1 e0 b1 f0 = true → WeightedBound B m

def closeEF (p : Predicate) : Predicate := fun d0 d1 e0 b1 f0 =>
  p d0 d1 e0 b1 f0 ||
    p (efCode d0) (efCode d1) (efCode f0) (efCode b1) (efCode e0)

theorem closeEF_valid (B : Nat) (p : Predicate) (hp : Valid B p) :
    Valid B (closeEF p) := by
  intro m hm d0 d1 e0 b1 f0 hd0 hd1 he0 hb1 hf0 hc
  rcases Bool.or_eq_true_iff.mp hc with h | h
  · exact hp m hm d0 d1 e0 b1 f0 hd0 hd1 he0 hb1 hf0 h
  · apply (weightedBound_rename_iff B ef (by decide) m).mp
    apply hp (renameTable ef m) (fits_renamed m hm)
      (efCode d0) (efCode d1) (efCode f0) (efCode b1) (efCode e0)
    · change (m (3,false)).map (renameMove ef) = _
      rw [hd0,ef_code_decode]
    · change (m (3,true)).map (renameMove ef) = _
      rw [hd1,ef_code_decode]
    · change (m (5,false)).map (renameMove ef) = _
      rw [hf0,ef_code_decode]
    · change (m (1,true)).map (renameMove ef) = _
      rw [hb1,ef_code_decode]
    · change (m (4,false)).map (renameMove ef) = _
      rw [he0,ef_code_decode]
    · exact h

def extend (p : Predicate) : Predicate := fun d0 d1 e0 b1 f0 =>
  closeEF p d0 d1 e0 b1 f0 || Box27EarlyTerminal.selected d0 d1 e0 b1 f0

theorem extend_valid (p : Predicate) (hp : Valid 255 p) : Valid 255 (extend p) := by
  intro m hm d0 d1 e0 b1 f0 hd0 hd1 he0 hb1 hf0 hc
  rcases Bool.or_eq_true_iff.mp hc with h | h
  · exact closeEF_valid 255 p hp m hm d0 d1 e0 b1 f0 hd0 hd1 he0 hb1 hf0 h
  · exact Box27EarlyTerminal.selected_bound m hm d0 d1 e0 b1 f0 hd0 hd1 he0 hb1 hf0 h

#print axioms fits_renamed
#print axioms closeEF_valid
#print axioms extend_valid
end BB6.Agent49.Box27Symmetry
