import BB429AGate
import Lean.Elab.Tactic.Omega

namespace BB429EGuard
open BB6Coverage BB429PhysicalFrontier

private def A : Fin 6 := ⟨0, by decide⟩
private def B : Fin 6 := ⟨1, by decide⟩
private def C : Fin 6 := ⟨2, by decide⟩
private def D : Fin 6 := ⟨3, by decide⟩
private def E : Fin 6 := ⟨4, by decide⟩
private def F : Fin 6 := ⟨5, by decide⟩

/-- The only original incoming E inputs are D/0 and E/1, both writing
    one and moving left. The result is for the original complete table. -/
private theorem target429_E_entry (s : Slot) (mv : Move)
    (h : target429 s=some mv) (hn : mv.next=E) :
    mv.write=true ∧ mv.right=false := by
  rcases s with ⟨q,b⟩
  have hq : q=0 ∨ q=1 ∨ q=2 ∨ q=3 ∨ q=4 ∨ q=5 := by
    have hh := q.isLt
    omega
  rcases hq with hq|hq|hq|hq|hq|hq <;> subst q <;> cases b <;>
    simp [BB429PhysicalFrontier.target429,
      BB429PhysicalFrontier.prefix11,BB429PhysicalFrontier.prefix10,
      BB429PhysicalFrontier.prefix9,BB429PhysicalFrontier.prefix8,
      BB429PhysicalFrontier.prefix7,BB429PhysicalFrontier.prefix6,
      BB429PhysicalFrontier.prefix5,BB429PhysicalFrontier.prefix4,
      BB429PhysicalFrontier.prefix3,BB429PhysicalFrontier.prefix2,
      BB429PhysicalFrontier.prefix1,BB429PhysicalFrontier.prefix0,
      refine, emptyTable] at h <;>
    cases h <;> simp_all [A,B,C,D,E,F]

private theorem left_write_one_right (c : Config) (mv : Move)
    (hw : mv.write=true) (hd : mv.right=false) :
    (applyMove c mv).tape ((applyMove c mv).head+1)=true := by
  simp only [applyMove,hd,hw]
  have heq : c.head + -1 + 1 = c.head := by omega
  simp [heq]

/-- Every genuine E configuration has a marked right neighbor, independent
    of time and of the E head's scanned bit. -/
theorem every_reachable_E_right_one (n : Nat) (c : Config)
    (hr : run target429 n blank=some c) (hs : c.state=E) :
    c.tape (c.head+1)=true := by
  cases n with
  | zero =>
      have hc : c=blank := by simpa [run] using hr.symm
      subst c
      simp [blank,E] at hs
  | succ n =>
      cases hprev : run target429 n blank with
      | none => simp [run,hprev] at hr
      | some d =>
          cases ht : target429 (readSlot d) with
          | none => simp [run,hprev,rawStep,ht] at hr
          | some mv =>
              have hc : applyMove d mv = c := by
                simpa [run,hprev,rawStep,ht] using hr
              have hn : mv.next=E := by
                rw [←hc] at hs
                exact hs
              obtain ⟨hw,hd⟩ := target429_E_entry (readSlot d) mv ht hn
              rw [←hc]
              exact left_write_one_right d mv hw hd

/-- A genuine E/0 exit to A cannot emit the k=0 fatal A-corridor word
    0001: every genuine E configuration has a marked right neighbor. -/
theorem E0_cannot_enter_aGate_zero (n : Nat) (e : Config)
    (hr : run target429 n blank=some e) (heslot : readSlot e=(E,false)) :
    ¬ BB429AGate.aGate 0 (applyMove e ⟨false,false,A⟩) := by
  intro hg
  have hs : e.state=E := by simpa [readSlot] using congrArg Prod.fst heslot
  have ht := every_reachable_E_right_one n e hr hs
  have hz : (applyMove e ⟨false,false,A⟩).tape
      ((applyMove e ⟨false,false,A⟩).head+2)=false := by
    simpa using hg.2.2.2.1
  have heq : (applyMove e ⟨false,false,A⟩).tape
      ((applyMove e ⟨false,false,A⟩).head+2)=e.tape (e.head+1) := by
    have ne : e.head + 1 ≠ e.head := by omega
    have he : e.head + -1 + 2 = e.head + 1 := by omega
    simp [applyMove,he,ne]
  rw [heq] at hz
  simp [ht] at hz

#print axioms every_reachable_E_right_one
#print axioms E0_cannot_enter_aGate_zero
end BB429EGuard
