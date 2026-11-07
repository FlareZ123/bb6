import BB429PhysicalFrontier
import Lean.Elab.Tactic.Omega

namespace BB429FEntry
open BB6Coverage

def A : Fin 6 := ⟨0, by decide⟩
def C : Fin 6 := ⟨2, by decide⟩
def D : Fin 6 := ⟨3, by decide⟩
def F : Fin 6 := ⟨5, by decide⟩

/-- A left-moving zero-writing instruction clears the cell immediately to
    the right of its successor head. This uses the original raw tape. -/
theorem move_left_zero_right (c : Config) (t : Move)
    (hw : t.write = false) (hd : t.right = false) :
    (applyMove c t).tape ((applyMove c t).head + 1) = false := by
  simp only [applyMove, hd, hw, Bool.false_eq_true]
  have heq : c.head + -1 + 1 = c.head := by omega
  simp [heq]

/-- Generic all-time F-entry invariant, independent of the rest of the
    transition table. The start state is A, which differs from F. -/
theorem safe_F (m : Machine)
    (hF : ∀ s t, m s = some t → t.next = F →
        t.write = false ∧ t.right = false)
    (n : Nat) (c : Config)
    (hr : run m n blank = some c)
    (hf : c.state = F) : c.tape (c.head + 1) = false := by
  cases n with
  | zero =>
      have hc : c = blank := by simpa [run] using hr.symm
      subst c
      simp [blank, F] at hf
  | succ n =>
      cases hprev : run m n blank with
      | none => simp [run, hprev] at hr
      | some d =>
          cases hs : m (readSlot d) with
          | none => simp [run, rawStep, hprev, hs] at hr
          | some t =>
              have hc : applyMove d t = c := by
                simpa [run, rawStep, hprev, hs] using hr
              have hn : t.next = F := by
                rw [← hc] at hf
                exact hf
              obtain ⟨hw,hd⟩ := hF (readSlot d) t hs hn
              rw [← hc]
              exact move_left_zero_right d t hw hd

/-- A right-moving F/0 to D cannot enter D on a marked symbol. -/
theorem F0_successor_reads_zero (m : Machine)
    (hF : ∀ s t, m s = some t → t.next = F →
        t.write = false ∧ t.right = false)
    (hFD : m (F,false) = some ⟨true,true,D⟩)
    (n : Nat) (c : Config)
    (hr : run m n blank = some c)
    (hf : c.state = F)
    (hread : c.tape c.head = false) :
    ∃ d, rawStep m c = some d ∧ d.state = D ∧ d.tape d.head = false := by
  have hsafe := safe_F m hF n c hr hf
  have hs : readSlot c = (F,false) := by simp [readSlot,hf,hread]
  refine ⟨applyMove c ⟨true,true,D⟩, ?_, rfl, ?_⟩
  · simp [rawStep, hs, hFD]
  · have hne : c.head + 1 ≠ c.head := by omega
    simpa [applyMove, hne] using hsafe

open BB429PhysicalFrontier (target429)

/-- Direct finite inspection of the exact #429 transition table: every
    incoming F instruction is a zero-writing left move (from A/1). -/
theorem target429_F_entry (s : Slot) (t : Move)
    (h : target429 s = some t)
    (ht : t.next = F) : t.write = false ∧ t.right = false := by
  rcases s with ⟨q,b⟩
  have hq : q = 0 ∨ q = 1 ∨ q = 2 ∨ q = 3 ∨ q = 4 ∨ q = 5 := by
    have hlt := q.isLt
    omega
  rcases hq with hq|hq|hq|hq|hq|hq <;> subst q <;> cases b <;>
    simp [BB429PhysicalFrontier.target429, BB429PhysicalFrontier.prefix11,
      BB429PhysicalFrontier.prefix10, BB429PhysicalFrontier.prefix9,
      BB429PhysicalFrontier.prefix8, BB429PhysicalFrontier.prefix7,
      BB429PhysicalFrontier.prefix6, BB429PhysicalFrontier.prefix5,
      BB429PhysicalFrontier.prefix4, BB429PhysicalFrontier.prefix3,
      BB429PhysicalFrontier.prefix2, BB429PhysicalFrontier.prefix1,
      BB429PhysicalFrontier.prefix0, refine, emptyTable] at h <;>
    cases h <;> simp_all [F]

theorem target429_F0_safe (n : Nat) (c : Config)
    (hr : run target429 n blank = some c)
    (hf : c.state = F)
    (hread : c.tape c.head = false) :
    ∃ d, rawStep target429 c = some d ∧ d.state = D ∧ d.tape d.head = false := by
  apply F0_successor_reads_zero target429 target429_F_entry
  · decide
  · exact hr
  · exact hf
  · exact hread

/-- On the exact #429 original table, a D entry can only follow C/0 or F/0. -/
theorem target429_D_input (s : Slot) (t : Move)
    (h : target429 s = some t)
    (ht : t.next = D) : s = (C,false) ∨ s = (F,false) := by
  rcases s with ⟨q,b⟩
  have hq : q = 0 ∨ q = 1 ∨ q = 2 ∨ q = 3 ∨ q = 4 ∨ q = 5 := by
    have hlt := q.isLt
    omega
  rcases hq with hq|hq|hq|hq|hq|hq <;> subst q <;> cases b <;>
    simp [BB429PhysicalFrontier.target429, BB429PhysicalFrontier.prefix11,
      BB429PhysicalFrontier.prefix10, BB429PhysicalFrontier.prefix9,
      BB429PhysicalFrontier.prefix8, BB429PhysicalFrontier.prefix7,
      BB429PhysicalFrontier.prefix6, BB429PhysicalFrontier.prefix5,
      BB429PhysicalFrontier.prefix4, BB429PhysicalFrontier.prefix3,
      BB429PhysicalFrontier.prefix2, BB429PhysicalFrontier.prefix1,
      BB429PhysicalFrontier.prefix0, refine, emptyTable] at h <;>
    cases h <;> simp_all [F, C, D]

/-- All-time original-blank-root necessary predecessor: if a reachable D
    head reads one, the immediately preceding input was C/0, never F/0.
    This remains a necessary condition; it does not decide the machine. -/
theorem target429_D1_only_from_C0 (n : Nat) (c : Config)
    (hr : run target429 (n+1) blank = some c)
    (hD : c.state = D) (hone : c.tape c.head = true) :
    ∃ d, run target429 n blank = some d ∧ readSlot d = (C,false) := by
  cases hprev : run target429 n blank with
  | none => simp [run, hprev] at hr
  | some d =>
      have hstep : rawStep target429 d = some c := by
        simpa [run, hprev] using hr
      cases hs : target429 (readSlot d) with
      | none => simp [rawStep, hs] at hstep
      | some mv =>
          have hc : applyMove d mv = c := by
            simpa [rawStep, hs] using hstep
          have hn : mv.next = D := by
            rw [← hc] at hD
            exact hD
          rcases target429_D_input (readSlot d) mv hs hn with hC | hF
          · exact ⟨d, by simp only, hC⟩
          · have hdF : d.state = F := by
              simpa [readSlot] using congrArg Prod.fst hF
            have hd0 : d.tape d.head = false := by
              simpa [readSlot] using congrArg Prod.snd hF
            obtain ⟨e, he, _, he0⟩ := target429_F0_safe n d hprev hdF hd0
            have hce : c = e := Option.some.inj (hstep.symm.trans he)
            subst e
            simp [hone] at he0

#print axioms move_left_zero_right
#print axioms safe_F
#print axioms F0_successor_reads_zero
#print axioms target429_F_entry
#print axioms target429_F0_safe
#print axioms target429_D_input
#print axioms target429_D1_only_from_C0
end BB429FEntry
