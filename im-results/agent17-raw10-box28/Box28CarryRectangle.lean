import Box28CarryWildcard
import Box28CarryTail01
import Box17AuditCore

namespace BB6.Agent17.Box28CarryRectangle
open BB6Coverage BB6.Agent13BlankDelay BB6.Agent13.Box17
open BB6.Agent17.Box28CarryGateSource
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false

/-- Both B1 and E0 are free in the parent. The cut fixes E0 alone. -/
def cylinder (two : Bool) (e : Fin 25) : PartialMachine :=
  refine (baseTable two) (4,false) (decode e)

def witness (two : Bool) (e : Fin 25) : Option Witness :=
  match two,e.val with
  | _,0 => some (.halt 4)
  | _,1 => some (.cycle 0 5 false 1)
  | false,2 => some (.cycle 0 7 true (-1))
  | _,3 => some (.last 3 6)
  | _,5 => some (.cycle 6 1 false (-2))
  | _,6 => some (.last 3 5)
  | _,7 => some (.cycle 6 1 false (-2))
  | _,8 => some (.last 3 5)
  | _,9 => some (.cycle 5 1 false (-1))
  | _,10 => some (.cycle 8 1 false 2)
  | _,11 => some (.cycle 5 1 false (-1))
  | _,13 => some (.cycle 3 2 true (-1))
  | false,16 => some (.cycle 17 2 true 3)
  | _,17 => some (.cycle 4 1 false 0)
  | _,19 => some (.cycle 4 1 false 0)
  | _,21 => some (.last 3 7)
  | _,22 => some (.cycle 2 5 true (-1))
  | false,23 => some (.cycle 11 76 true (-2))
  | _,_ => none

def witnessOK (two : Bool) (e : Fin 25) : Bool :=
  match witness two e with
  | none => true
  | some w => leafCheck 8 #[] (cylinder two e) w

theorem all_checks : ∀ (two : Bool) (e : Fin 25), witnessOK two e = true := by decide

theorem carry_cases3 : ∀ e : Fin 25, (witness false e).isSome = false →
    e=4 ∨ e=12 ∨ e=14 ∨ e=15 ∨ e=18 ∨ e=20 ∨ e=24 := by decide

theorem carry_cases2 : ∀ e : Fin 25, (witness true e).isSome = false →
    e=2 ∨ e=4 ∨ e=12 ∨ e=14 ∨ e=15 ∨ e=16 ∨ e=18 ∨ e=20 ∨ e=23 ∨ e=24 := by decide

theorem cut_compatible (two : Bool) (m : Machine) (hm : compatible (baseTable two) m)
    (e : Fin 25) (he : m (4,false) = decode e) : compatible (cylinder two e) m := by
  unfold cylinder
  rw [← he]
  exact compatible_refine _ _ _ hm

theorem cut_bound (two : Bool) (m : Machine) (hm : compatible (baseTable two) m)
    (e : Fin 25) (he : m (4,false) = decode e) : WeightedBound 8 m := by
  cases hw : witness two e with
  | some w =>
    have hc : leafCheck 8 #[] (cylinder two e) w = true := by
      simpa [witnessOK,hw] using all_checks two e
    apply leafCheck_sound 8 #[] ?_ _ w hc m (cut_compatible two m hm e he)
    intro i q h
    simp at h
  | none =>
    apply weighted_of_never
    cases two with
    | false =>
      have hc := carry_cases3 e (by simp [hw])
      rcases hc with h|h|h|h|h|h|h <;> subst e
      · exact BB6.Agent17.Box28CarryTail01.gate20_4 m hm he
      · exact BB6.Agent17.Box28CarryWildcard.gate20_12 m hm he
      · exact BB6.Agent17.Box28CarryWildcard.gate20_14 m hm he
      · exact BB6.Agent17.Box28CarryWildcard.gate20_15 m hm he
      · exact BB6.Agent17.Box28CarryWildcard.gate20_18 m hm he
      · exact BB6.Agent17.Box28CarryTail01.gate20_20 m hm he
      · exact BB6.Agent17.Box28CarryWildcard.gate20_24 m hm he
    | true =>
      have hc := carry_cases2 e (by simp [hw])
      rcases hc with h|h|h|h|h|h|h|h|h|h <;> subst e
      · exact BB6.Agent17.Box28CarryWildcard.gate24_2 m hm he
      · exact BB6.Agent17.Box28CarryWildcard.gate24_4 m hm he
      · exact BB6.Agent17.Box28CarryWildcard.gate24_12 m hm he
      · exact BB6.Agent17.Box28CarryWildcard.gate24_14 m hm he
      · exact BB6.Agent17.Box28CarryWildcard.gate24_15 m hm he
      · exact BB6.Agent17.Box28CarryWildcard.gate24_16 m hm he
      · exact BB6.Agent17.Box28CarryWildcard.gate24_18 m hm he
      · exact BB6.Agent17.Box28CarryWildcard.gate24_20 m hm he
      · exact BB6.Agent17.Box28CarryWildcard.gate24_23 m hm he
      · exact BB6.Agent17.Box28CarryWildcard.gate24_24 m hm he

theorem decode_complete (t : Transition) : ∃ e : Fin 25, decode e = t := by
  cases t with
  | none => exact ⟨0,rfl⟩
  | some mv =>
    rcases mv with ⟨w,r,q⟩
    revert q r w
    decide

/-- Complete weighted bound for the two disjoint 625-table rectangles.
    No assumption about whether B1 or E0 halts is needed. -/
theorem rectangle_bound (two : Bool) (m : Machine)
    (hm : compatible (baseTable two) m) : WeightedBound 8 m := by
  obtain ⟨e,he⟩ := decode_complete (m (4,false))
  exact cut_bound two m hm e he.symm

theorem rectangle_mono (B : Nat) (hB : 8 ≤ B) (two : Bool) (m : Machine)
    (hm : compatible (baseTable two) m) : WeightedBound B m := by
  intro k d hk hd
  exact Nat.le_trans (rectangle_bound two m hm k d hk hd) hB

def maxRow : PartialMachine := refine (cylinder false 21) (1,true) none
def maxMachine : Machine := fun s => (maxRow s).getD none

theorem max_compatible : compatible maxRow maxMachine := by
  intro s t h
  simp [maxMachine,h]

theorem max_base_check : ∀ (q : Fin 6) (b : Bool),
    (baseTable false (q,b)).isSome = true →
    maxRow (q,b) = baseTable false (q,b) := by decide

theorem max_base : compatible (baseTable false) maxMachine := by
  intro s t h
  have he := max_base_check s.1 s.2 (by simp [h])
  exact max_compatible s t (he.trans h)

theorem max_halts : HaltsAfter maxMachine 7 :=
  zipHalt_sound maxRow 7 (by decide) maxMachine max_compatible

#print axioms all_checks
#print axioms rectangle_bound
#print axioms max_halts
#print axioms max_base
end BB6.Agent17.Box28CarryRectangle
