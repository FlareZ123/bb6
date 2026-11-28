import FastFAR
import Raw34M2071Growth

namespace BB6.Agent50Raw34Cylinder
open BB6Coverage

def slots : List Slot := (List.finRange 6).flatMap fun q => [(q,false),(q,true)]

theorem slots_complete (s : Slot) : s ∈ slots := by
  rcases s with ⟨q,b⟩
  apply List.mem_flatMap.mpr
  refine ⟨q,List.mem_finRange q,?_⟩
  cases b <;> simp

def moves : List Move :=
  [false,true].flatMap fun w =>
    [false,true].flatMap fun r =>
      (List.finRange 6).map fun q => ⟨w,r,q⟩

def table (codes : List Nat) : PartialMachine := fun s =>
  let code := (codes[2*s.1.val+s.2.toNat]?).getD 0
  if code = 0 then none
  else if code = 1 then some none
  else (moves[code-2]?).map some

def sameTable (p q : PartialMachine) : Bool :=
  slots.all fun s => decide (p s = q s)

theorem sameTable_sound (p q : PartialMachine) (h : sameTable p q = true) : p = q := by
  funext s
  exact of_decide_eq_true (List.all_eq_true.mp h s (slots_complete s))

/-- A missing transition becomes a genuine halt in the least live completion. -/
def haltFill (p : PartialMachine) : Machine := fun s => (p s).getD none

theorem haltFill_compatible (p : PartialMachine) : compatible p (haltFill p) := by
  intro s t hs
  simp [haltFill,hs]

/-- A live prefix of the halt completion consults only assigned ordinary moves. -/
theorem haltFill_live_prefix (p : PartialMachine) (m : Machine) (hm : compatible p m)
    (n : Nat) (c d : Config) (h : run (haltFill p) n c = some d) : run m n c = some d := by
  induction n generalizing d with
  | zero => simpa [run] using h
  | succ n ih =>
    cases he : run (haltFill p) n c with
    | none => simp [run,he] at h
    | some e =>
      have ht : rawStep (haltFill p) e = some d := by simpa [run,he] using h
      have hp : run m n c = some e := ih e he
      cases hs : p (readSlot e) with
      | none => simp [rawStep,haltFill,hs] at ht
      | some t =>
        have hstep : rawStep m e = rawStep (haltFill p) e := by
          simp [rawStep,haltFill,hs,hm _ _ hs]
        simp [run,hp,hstep,ht]

/-- If the halt completion never halts, all compatible completions have its live trace. -/
theorem haltFill_never (p : PartialMachine) (h : NeverHalts (haltFill p))
    (m : Machine) (hm : compatible p m) : NeverHalts m := by
  intro n
  have hn := h n
  cases he : run (haltFill p) n blank with
  | none => simp [he] at hn
  | some d => simp [haltFill_live_prefix p m hm n blank d he]

/-- Boolean check for the exact halt-completion witness table, using all twelve slots. -/
def fillCheck (p q : PartialMachine) : Bool :=
  slots.all fun s => decide (q s = some (haltFill p s))

theorem fillCheck_sound (p q : PartialMachine) (h : fillCheck p q = true)
    (hn : ∀ m, compatible q m → NeverHalts m)
    (m : Machine) (hm : compatible p m) : NeverHalts m := by
  apply haltFill_never p _ m hm
  apply hn
  intro s t hs
  have hq := of_decide_eq_true (List.all_eq_true.mp h s (slots_complete s))
  rw [hs] at hq
  exact (Option.some.inj hq).symm

#print axioms haltFill_live_prefix
#print axioms haltFill_never
#print axioms fillCheck_sound
end BB6.Agent50Raw34Cylinder
