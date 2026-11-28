import Leaf2265Core
import FastThreeHoleAudit
import WeightedTNF

namespace BB6.Agent3Leaf2265Bridge
open BB6Coverage BB6Coverage.FAR BB6.Agent13BlankDelay
open BB6.Agent3Leaf2265 (Cfg cons tail table terminalCfg terminalRun terminalRead blankCfg)

def ctr : PartialMachine := fromCodes [7,20,11,1,14,11,22,16,24,13,2,12]

def tableMove (s : Slot) : Option Move := (table s.1 s.2).map fun (w,d,q) => ⟨w,d,q⟩

theorem table_match (s : Slot) : ctr s = (tableMove s).map some := by
  rcases s with ⟨q,b⟩
  have hcases : q = 0 ∨ q = 1 ∨ q = 2 ∨ q = 3 ∨ q = 4 ∨ q = 5 := by
    have hlt := q.isLt
    simp only [Fin.ext_iff]
    omega
  rcases hcases with h | h | h | h | h | h <;> subst q <;> cases b <;> rfl

-- Observe the physical tape relative to its head, with no loss of a read bit.
def observe (c : Config) : Cfg := ⟨c.state,
  fun n => c.tape (c.head - (n : Int) - 1),
  fun n => c.tape (c.head + (n : Int))⟩

def moveC (mv : Move) (c : Cfg) : Cfg :=
  if mv.right then ⟨mv.next, cons mv.write c.l, tail c.r⟩
  else ⟨mv.next, tail c.l, cons (c.l 0) (cons mv.write (tail c.r))⟩

theorem observe_move (mv : Move) (c : Config) :
    observe (applyMove c mv) = moveC mv (observe c) := by
  rcases mv with ⟨w,d,q⟩
  cases d with
  | false =>
    simp only [observe,applyMove,moveC,Bool.false_eq_true,ite_false]
    congr 1
    · funext n
      simp only [tail]
      split
      · omega
      · congr 1; omega
    · funext n
      cases n with
      | zero =>
        simp only [cons]
        split
        · omega
        · congr 1; omega
      | succ n =>
        cases n with
        | zero =>
          simp only [cons]
          split
          · rfl
          · omega
        | succ n =>
          simp only [cons,tail]
          split
          · omega
          · congr 1; omega
  | true =>
    simp only [observe,applyMove,moveC,ite_true]
    congr 1
    · funext n
      cases n with
      | zero =>
        simp only [cons]
        split
        · rfl
        · omega
      | succ n =>
        simp only [cons]
        split
        · omega
        · congr 1; omega
    · funext n
      simp only [tail]
      split
      · omega
      · congr 1; omega

theorem observed_slot (c : Config) : (observe c).q = c.state ∧ (observe c).r 0 = c.tape c.head := by
  constructor
  · rfl
  · simp [observe]

theorem step_eq (c : Cfg) : BB6.Agent3Leaf2265.step c = (tableMove (c.q,c.r 0)).map (fun mv => moveC mv c) := by
  unfold BB6.Agent3Leaf2265.step tableMove moveC
  cases ht : table c.q (c.r 0) with
  | none => rfl
  | some v => rcases v with ⟨w,d,q⟩; rfl

theorem step_sound (m : Machine) (hm : compatible ctr m) (c : Config) (d : Cfg)
    (hs : BB6.Agent3Leaf2265.step (observe c) = some d) :
    ∃ c', rawStep m c = some c' ∧ observe c' = d := by
  rw [step_eq,(observed_slot c).1,(observed_slot c).2] at hs
  change (tableMove (readSlot c)).map (fun mv => moveC mv (observe c)) = some d at hs
  cases ht : tableMove (readSlot c) with
  | none => simp [ht] at hs
  | some mv =>
    have hctr : ctr (readSlot c) = some (some mv) := by rw [table_match,ht]; rfl
    have hmv := hm _ _ hctr
    refine ⟨applyMove c mv, ?_, ?_⟩
    · simp [rawStep,hmv]
    · rw [observe_move]
      simpa [ht] using hs

theorem run_sound (m : Machine) (hm : compatible ctr m) (n : Nat) (c : Config) (d : Cfg)
    (hs : BB6.Agent3Leaf2265.run n (observe c) = some d) :
    ∃ c', BB6Coverage.run m n c = some c' ∧ observe c' = d := by
  induction n generalizing c with
  | zero => exact ⟨c,rfl,Option.some.inj hs⟩
  | succ n ih =>
    cases ht : BB6.Agent3Leaf2265.step (observe c) with
    | none => simp [BB6.Agent3Leaf2265.run,ht] at hs
    | some e =>
      obtain ⟨c',hc',he⟩ := step_sound m hm c e ht
      have hh : BB6.Agent3Leaf2265.run n (observe c') = some d := by
        rw [he]; simpa [BB6.Agent3Leaf2265.run,ht] using hs
      obtain ⟨c'',hc'',hd⟩ := ih c' hh
      refine ⟨c'',?_,hd⟩
      rw [show n+1=1+n by omega, BB6Coverage.run_append]
      have h1 : BB6Coverage.run m 1 c = some c' := by simpa [BB6Coverage.run] using hc'
      rw [h1]; exact hc''


/-- Source-to-original-machine transport at *any* counted source endpoint.
    This theorem does not depend on the concrete 228-digit arithmetic. -/
theorem reached_of_source (m : Machine) (hm : compatible ctr m)
    (steps : Nat) (d : Cfg)
    (hs : BB6.Agent3Leaf2265.Runs steps blankCfg d)
    (hd : d.q = 4 ∧ d.r 0 = false) :
    ∃ c, BB6Coverage.run m steps BB6Coverage.blank = some c ∧
      readSlot c = (4,false) := by
  have hb : observe BB6Coverage.blank = blankCfg := rfl
  have hr : BB6.Agent3Leaf2265.run steps (observe BB6Coverage.blank) = some d := by
    rw [hb]
    exact hs
  obtain ⟨c,hc,he⟩ := run_sound m hm steps BB6Coverage.blank d hr
  refine ⟨c,hc,?_⟩
  have hh := observed_slot c
  rw [he] at hh
  change (c.state,c.tape c.head) = (4,false)
  exact Prod.ext (hh.1.symm.trans hd.1) (hh.2.symm.trans hd.2)

theorem rest (s : Slot) (h : s ≠ (4,false)) :
    ∃ mv, ctr s = some (some mv) := by
  rcases s with ⟨q,b⟩
  have hcases : q = 0 ∨ q = 1 ∨ q = 2 ∨ q = 3 ∨ q = 4 ∨ q = 5 := by
    have hlt := q.isLt
    simp only [Fin.ext_iff]
    omega
  rcases hcases with hq | hq | hq | hq | hq | hq <;>
    subst q <;> cases b <;>
    first | exact ⟨_,rfl⟩ | exact False.elim (h rfl)

/-- Every completion of this one-hole table has either no halt instruction
    or halts exactly at the first missing E0 query. The +6 is the standard
    six-state weighted first-one convention (five possible delay steps). -/
theorem weighted_of_source (steps : Nat) (d : Cfg)
    (hs : BB6.Agent3Leaf2265.Runs steps blankCfg d)
    (hd : d.q = 4 ∧ d.r 0 = false) :
    Cover (WeightedBound (steps+6)) ctr := by
  apply Cover.leaf
  intro m hm
  cases ht : m (4,false) with
  | some mv =>
    apply weighted_never
    apply all_ordinary_never
    intro s
    by_cases hslot : s = (4,false)
    · subst s
      exact ⟨mv,ht⟩
    · obtain ⟨u,hu⟩ := rest s hslot
      exact ⟨u,hm s _ hu⟩
  | none =>
    obtain ⟨c,hc,hslot⟩ := reached_of_source m hm steps d hs hd
    have hh : HaltsAfter m steps := by
      constructor
      · simpa [hc]
      · change (BB6Coverage.run m steps BB6Coverage.blank).bind (rawStep m) = none
        rw [hc]
        simp [rawStep, hslot, ht]
    intro k delay hk hdelay
    have he := halting_time_unique m k steps hk hh
    have hlt : delay < 6 := List.mem_range.mp (List.mem_filter.mp hdelay).1
    omega

#print axioms table_match
#print axioms observe_move
#print axioms run_sound
#print axioms reached_of_source
#print axioms weighted_of_source
end BB6.Agent3Leaf2265Bridge
