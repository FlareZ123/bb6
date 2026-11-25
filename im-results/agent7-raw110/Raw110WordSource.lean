import Raw110WordSweep
import BlockFARBridge
import Raw110PairMacro
import WeightedTNF
set_option maxHeartbeats 0
namespace BB6.Agent7Raw110Late
open BB6Coverage BB6.Agent13BlankDelay
open BB6BlockFAR BB6Raw110Word

abbrev table := BB6.Agent7Raw110Pair.table

theorem table_eq (slow : Bool) : partialTable (BB6Carry.machine slow) = table slow := by
  funext s
  rcases s with ⟨q,b⟩
  revert q b
  cases slow <;> decide

theorem hole (slow : Bool) : ∀ q b, BB6Carry.machine slow q b = none → (q,b) = ((0 : Fin 6),true) := by
  cases slow <;> decide

theorem transfer_live (M : BB6BlockFAR.Table) (m : BB6Coverage.Machine)
    (hm : compatible (partialTable M) m) (n : Nat)
    (c : BB6Coverage.Config) (x y : Prim) (hrel : Related c x)
    (hr : BB6BlockFAR.run M n x = some y) :
    ∃ d, BB6Coverage.run m n c = some d ∧ Related d y := by
  induction n generalizing c x y with
  | zero =>
    have h : x = y := Option.some.inj hr
    subst y
    exact ⟨c,rfl,hrel⟩
  | succ n ih =>
    cases hs : primStep M x with
    | none => simp [BB6BlockFAR.run,hs] at hr
    | some u =>
      obtain ⟨d,hd,hdr⟩ := related_step M m hm c x u hrel hs
      obtain ⟨e,he,her⟩ := ih d u y hdr (by simpa [BB6BlockFAR.run,hs] using hr)
      refine ⟨e,?_,her⟩
      rw [show n+1=1+n by omega, BB6Coverage.run_append]
      have hh : BB6Coverage.run m 1 c = some d := by simpa [BB6Coverage.run] using hd
      rw [hh]
      exact he

theorem halt_of_trace (slow : Bool) (n : Nat)
    (H : (Outcome.halt n).sound slow primBlank)
    (m : BB6Coverage.Machine) (hm : compatible (refine (table slow) (0,true) none) m) :
    HaltsAfter m n := by
  obtain ⟨x,hx,hf⟩ := H
  have hc := refine_preserves_compat (table slow) m (0,true) none (by cases slow <;> decide) hm
  rw [← table_eq] at hc
  obtain ⟨d,hd,hr⟩ := transfer_live (BB6Carry.machine slow) m hc n blank primBlank x related_blank hx
  have hrow : BB6Carry.machine slow x.q (x.r 0) = none := by
    cases ht : BB6Carry.machine slow x.q (x.r 0) with
    | none => rfl
    | some mv => cases hdir : mv.right <;> simp [primStep,ht,hdir] at hf
  have hslot : readSlot d = (0,true) := by
    have hread : d.tape d.head = x.r 0 := by simpa using hr.2.2 0
    change (d.state,d.tape d.head) = _
    rw [hr.1,hread]
    exact hole slow _ _ hrow
  have ht := hm (0,true) none (by simp [refine])
  exact ⟨by simp [hd], by simp [BB6Coverage.run,hd,rawStep,hslot,ht]⟩

theorem rest (slow : Bool) (s : Slot) (hs : s ≠ (0,true)) :
    ∃ v, table slow s = some (some v) := by
  have h : ∀ q : Fin 6, ∀ b : Bool, (q,b) ≠ ((0 : Fin 6),true) →
      ((table slow (q,b)).bind id).isSome = true := by cases slow <;> decide
  have hh := h s.1 s.2 hs
  cases he : table slow s with
  | none => simp [he] at hh
  | some t =>
    cases t with
    | none => simp [he] at hh
    | some v => exact ⟨v,rfl⟩

theorem cover_of_trace (slow : Bool) (n B : Nat) (hB : n+1 ≤ B)
    (H : (Outcome.halt n).sound slow primBlank) : Cover (WeightedBound B) (table slow) := by
  refine Cover.leaf _ ?_
  intro m hm
  cases h : m (0,true) with
  | none =>
    let p := refine (table slow) (0,true) none
    have hp : compatible p m := by simpa [p,h] using compatible_refine (table slow) m (0,true) hm
    have hf : p initialSlot=some (some ⟨true,true,1⟩) := by cases slow <;> decide
    have hh : ∀ m, compatible p m → HaltsAfter m n := halt_of_trace slow n H
    apply (uniform_halter_weight_iff p B n hf hh).mpr _ m hp
    have hd0 : possibleDelays p 0 = [0] := by cases slow <;> decide
    intro d hd
    rw [hd0] at hd
    have he : d = 0 := by simpa using hd
    omega
  | some mv =>
    apply weighted_never B m
    apply all_ordinary_never m
    intro s
    by_cases hs : s = (0,true)
    · subst s
      exact ⟨mv,h⟩
    · obtain ⟨v,hv⟩ := rest slow s hs
      exact ⟨v,hm _ _ hv⟩

#print axioms halt_of_trace
#print axioms cover_of_trace
end BB6.Agent7Raw110Late
