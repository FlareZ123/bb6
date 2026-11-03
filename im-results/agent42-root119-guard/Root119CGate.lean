import Root119Gate

set_option linter.unusedSimpArgs false

namespace BB6Root119

/-- One raw step earlier, the fatal D/0 left-11 pattern is a C/0
    section reading the rightmost zero in the four-cell word 1100. -/
def CGate (c : Conf) : Prop :=
  c.q = .C ∧ c.tape c.h = false ∧
  c.tape (c.h-1) = false ∧
  c.tape (c.h-2) = true ∧ c.tape (c.h-3) = true

theorem to_D {u v : Conf} (hstep : next u = some v) (hd : v.q = .D) :
    (u.q = .C ∧ u.tape u.h = false) ∨
    (u.q = .F ∧ u.tape u.h = true) := by
  cases u with
  | mk q h t =>
    cases q <;> cases hb : t h <;> simp [next,hb] at hstep
    all_goals cases hstep
    all_goals simp_all

theorem F1_D_not_gate {u v : Conf} (hstep : next u = some v)
    (hF : u.q = .F) (hb : u.tape u.h = true) : ¬ Gate v := by
  rcases u with ⟨q,pos,t⟩
  cases q <;> simp_all [next]
  cases hstep
  simp [Gate, setBit, show pos+1-1=pos by omega]

theorem C0_D_gate_iff {u v : Conf} (hstep : next u = some v)
    (hC : u.q = .C) (hb : u.tape u.h = false) :
    Gate v ↔ CGate u := by
  rcases u with ⟨q,pos,t⟩
  cases q <;> simp_all [next]
  cases hstep
  have hp1 : pos-1 ≠ pos := by omega
  have hp2 : pos-1-1 ≠ pos := by omega
  have hp3 : pos-1-2 ≠ pos := by omega
  have hp2r : pos-2 ≠ pos := by omega
  have hp3r : pos-3 ≠ pos := by omega
  simp [Gate,CGate,setBit,hp1,hp2,hp3,hp2r,hp3r,hb,
    show pos-1-1=pos-2 by omega, show pos-1-2=pos-3 by omega]

theorem reached_D_gate_has_C_gate (d : Conf) (hd : Reach d)
    (hg : Gate d) : ∃ c, Reach c ∧ CGate c := by
  cases hd with
  | initial => simp [Gate,blank] at hg
  | follow hprev hstep =>
    obtain hC | hF := to_D hstep hg.1
    · have hc := (C0_D_gate_iff hstep hC.1 hC.2).mp hg
      exact ⟨_,hprev,hc⟩
    · exact False.elim ((F1_D_not_gate hstep hF.1 hF.2) hg)

theorem reached_C_gate_has_D_gate (c : Conf) (hc : Reach c)
    (hg : CGate c) : ∃ d, Reach d ∧ Gate d := by
  have hq : c.q = .C := hg.1
  have hb : c.tape c.h = false := hg.2.1
  have hstep : ∃ d, next c = some d := by
    rcases c with ⟨q,pos,t⟩
    cases q <;> simp_all [next]
  obtain ⟨d,hd⟩ := hstep
  exact ⟨d,Reach.follow hc hd,(C0_D_gate_iff hd hq hb).mpr hg⟩

/-- An exact refined halting gateway, the word 1100 immediately ending under C/0. -/
theorem blank_halts_iff_C_gate :
    (∃ a, Reach a ∧ next a = none) ↔ (∃ c, Reach c ∧ CGate c) := by
  rw [blank_halts_iff_gate]
  constructor
  · rintro ⟨d,hd,hg⟩
    exact reached_D_gate_has_C_gate d hd hg
  · rintro ⟨c,hc,hg⟩
    exact reached_C_gate_has_D_gate c hc hg

#print axioms BB6Root119.blank_halts_iff_C_gate
end BB6Root119
