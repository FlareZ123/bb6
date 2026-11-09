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


/-- All original incoming A inputs are B/1, E/0 or F/1. -/
private theorem target429_A_input (s : Slot) (mv : Move)
    (h : target429 s=some mv) (hn : mv.next=A) :
    s=(B,true) ∨ s=(E,false) ∨ s=(F,true) := by
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

/-- A genuine A/0001 gate must immediately follow B/1. E/0 is excluded
    by the all-time E-entry right-mark invariant, and F/1 just wrote one
    over the gate's required first blank cell. -/
theorem root_aGate_zero_has_B1_parent (n : Nat) (a : Config)
    (hr : run target429 (n+1) blank=some a)
    (hg : BB429AGate.aGate 0 a) :
    ∃ b, run target429 n blank=some b ∧ readSlot b=(B,true) := by
  cases hp : run target429 n blank with
  | none => simp [run,hp] at hr
  | some b =>
    have hstep : rawStep target429 b=some a := by
      simpa [run,hp] using hr
    cases ht : target429 (readSlot b) with
    | none => simp [rawStep,ht] at hstep
    | some mv =>
      have heq : a=applyMove b mv := by
        simpa [rawStep,ht] using hstep.symm
      have ha : a.state=A := by
        have hh := congrArg Prod.fst hg.1
        simpa [readSlot] using hh
      have hn : mv.next=A := by rw [heq] at ha;exact ha
      rcases target429_A_input (readSlot b) mv ht hn with hB|hE|hF
      · exact ⟨b,by simpa using hp,hB⟩
      · have hmv : mv=⟨false,false,A⟩ := by
          have hrow : target429 (readSlot b)=some ⟨false,false,A⟩ := by
            simpa [hE] using
              (show target429 (E,false)=some ⟨false,false,A⟩ by decide)
          exact Option.some.inj (ht.symm.trans hrow)
        rw [hmv] at heq
        rw [heq] at hg
        exact False.elim (E0_cannot_enter_aGate_zero n b (by simpa using hp) hE hg)
      · have hmv : mv=⟨true,false,A⟩ := by
          have hrow : target429 (readSlot b)=some ⟨true,false,A⟩ := by
            simpa [hF] using
              (show target429 (F,true)=some ⟨true,false,A⟩ by decide)
          exact Option.some.inj (ht.symm.trans hrow)
        have h1 : a.tape (a.head+1)=true := by
          rw [heq,hmv]
          exact left_write_one_right b ⟨true,false,A⟩ rfl rfl
        have h0 : a.tape (a.head+1)=false := by
          simpa using hg.2.2.1
        simp [h0] at h1

/-- Since the genuine blank start has no marked cells, the B/1 parent
    requirement for the first A/0001 gate is unconditional. -/
theorem root_aGate_zero_only_B1 (n : Nat) (a : Config)
    (hr : run target429 n blank=some a) (hg : BB429AGate.aGate 0 a) :
    ∃ j b, n=j+1 ∧ run target429 j blank=some b ∧ readSlot b=(B,true) := by
  cases n with
  | zero =>
      have hb : a=blank := by simpa [run] using hr.symm
      subst a
      simp [BB429AGate.aGate,blank] at hg
  | succ n =>
      obtain ⟨b,hb,hs⟩ := root_aGate_zero_has_B1_parent n a hr hg
      exact ⟨n,b,rfl,hb,hs⟩

#print axioms root_aGate_zero_has_B1_parent
#print axioms root_aGate_zero_only_B1

#print axioms every_reachable_E_right_one
#print axioms E0_cannot_enter_aGate_zero
end BB429EGuard
