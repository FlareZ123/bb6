import BB429FEntry
import Lean.Elab.Tactic.Omega

namespace BB429FatalB
open BB6Coverage BB429FEntry BB429PhysicalFrontier

def B : Fin 6 := ⟨1, by decide⟩
def fatalB (c : Config) : Prop :=
  c.state = B ∧ c.tape c.head = false ∧
  c.tape (c.head + 1) = false ∧ c.tape (c.head + 2) = true

private theorem b0 : target429 (B,false) = some ⟨true,true,C⟩ := by decide
private theorem c0 : target429 (C,false) = some ⟨false,true,D⟩ := by decide
private theorem d1 : target429 (D,true) = none := by decide

private theorem right_head_tape (c : Config) (t : Move) (hr : t.right = true) :
    (applyMove c t).tape ((applyMove c t).head) = c.tape (c.head+1) := by
  simp only [applyMove, hr, ite_true]
  have h : c.head + 1 ≠ c.head := by omega
  simp [h]

private theorem right_next_tape (c : Config) (t : Move) (hr : t.right = true) :
    (applyMove c t).tape ((applyMove c t).head + 1) = c.tape (c.head+2) := by
  simp only [applyMove, hr, ite_true]
  have h : c.head + 1 + 1 = c.head + 2 := by omega
  have h' : c.head + 2 ≠ c.head := by omega
  simp [h,h']

private theorem fatal_B_two_moves (c : Config) (hf : fatalB c) :
  ∃ d, rawStep target429 c = some d ∧
    ∃ e, rawStep target429 d = some e ∧
      readSlot e = (D,true) := by
  rcases hf with ⟨hb, hzero, hnext0, hnext1⟩
  let tB : Move := ⟨true,true,C⟩
  let tC : Move := ⟨false,true,D⟩
  let d := applyMove c tB
  let e := applyMove d tC
  have hc : readSlot c = (B,false) := by simp [readSlot,hb,hzero]
  have hd : readSlot d = (C,false) := by
    have hdk : d.tape d.head = false := by
      simpa [d,tB] using (right_head_tape c tB rfl).trans hnext0
    change (d.state,d.tape d.head) = (C,false)
    exact Prod.ext rfl hdk
  have he : readSlot e = (D,true) := by
    have he1 : e.tape e.head = true := by
      have hde : d.tape (d.head+1) = true := by
        simpa [d,tB] using (right_next_tape c tB rfl).trans hnext1
      exact (right_head_tape d tC rfl).trans hde
    change (e.state,e.tape e.head) = (D,true)
    exact Prod.ext rfl he1
  refine ⟨d, ?_, e, ?_, he⟩
  · simp [rawStep,hc,b0,d,tB]
  · simp [rawStep,hd,c0,e,tC]

theorem fatal_B_causes_halt (n : Nat) (c : Config)
    (hr : run target429 n blank = some c)
    (h : fatalB c) :
    HaltsAfter target429 (n+2) := by
  obtain ⟨d,hd,e,he,hhalt⟩ := fatal_B_two_moves c h
  have hn1 : run target429 (n+1) blank = some d := by
    change (run target429 n blank).bind (rawStep target429) = some d
    rw [hr]
    exact hd
  have hn2 : run target429 (n+2) blank = some e := by
    have heq : n+2 = (n+1)+1 := by omega
    rw [heq]
    change (run target429 (n+1) blank).bind (rawStep target429) = some e
    rw [hn1]
    exact he
  constructor
  · simp [hn2]
  · change (run target429 (n+2) blank).bind (rawStep target429) = none
    rw [hn2]
    simp only [Option.bind_some]
    simp [rawStep, hhalt, d1]

#print axioms fatal_B_causes_halt
end BB429FatalB

namespace BB429FatalB
open BB6Coverage BB429FEntry BB429PhysicalFrontier

private def moveB : Move := ⟨true,true,C⟩
private def moveC : Move := ⟨false,true,D⟩

private theorem target429_C_input (s : Slot) (t : Move)
    (h : target429 s = some t) (ht : t.next = C) :
    s = (B,false) := by
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
    cases h <;> simp_all [B,C]

private theorem exact_C0_parent (n : Nat) (c : Config)
    (hr : run target429 (n+1) blank = some c)
    (hc : readSlot c = (C,false)) :
    ∃ b, run target429 n blank = some b ∧
      readSlot b = (B,false) ∧ c = applyMove b moveB := by
  cases hprev : run target429 n blank with
  | none => simp [run, hprev] at hr
  | some b =>
      have hstep : rawStep target429 b = some c := by
        simpa [run,hprev] using hr
      cases hs : target429 (readSlot b) with
      | none => simp [rawStep,hs] at hstep
      | some mv =>
          have heq : c = applyMove b mv := by
            simpa [rawStep,hs] using hstep.symm
          have hm : mv.next=C := by
            have hsC : c.state=C := by simpa [readSlot] using congrArg Prod.fst hc
            rw [heq] at hsC
            exact hsC
          have hb : readSlot b = (B,false) := target429_C_input _ mv hs hm
          have hmv : mv=moveB := by
            have hbRule : target429 (readSlot b) = some moveB := by
              rw [hb]
              exact b0
            have hx : some mv = some moveB := hs.symm.trans hbRule
            exact Option.some.inj hx
          exact ⟨b, rfl, hb, by simpa [hmv] using heq⟩

private theorem target429_D1_one_step (n : Nat) (z : Config)
    (hr : run target429 (n+1) blank = some z)
    (hz : readSlot z = (D,true)) :
    ∃ c, run target429 n blank = some c ∧
      readSlot c = (C,false) ∧ z = applyMove c moveC := by
  have hD : z.state=D := by simpa [readSlot] using congrArg Prod.fst hz
  have h1 : z.tape z.head=true := by simpa [readSlot] using congrArg Prod.snd hz
  obtain ⟨c,hc,hslot⟩ := target429_D1_only_from_C0 n z hr hD h1
  have hstep : rawStep target429 c = some z := by
    change (run target429 n blank).bind (rawStep target429)=some z at hr
    rw [hc] at hr
    exact hr
  have hraw : rawStep target429 c = some (applyMove c moveC) := by
    simp [rawStep,hslot,c0,moveC]
  have heq : z = applyMove c moveC := Option.some.inj (hstep.symm.trans hraw)
  exact ⟨c,hc,hslot,heq⟩

theorem target429_D1_iff_B001 (n : Nat) :
    (∃ z, run target429 (n+2) blank = some z ∧ readSlot z = (D,true)) ↔
    (∃ b, run target429 n blank = some b ∧ fatalB b) := by
  constructor
  · rintro ⟨z,hzrun,hzslot⟩
    obtain ⟨c,hcrun,hcslot,hzc⟩ :=
      target429_D1_one_step (n+1) z hzrun hzslot
    obtain ⟨b,hbrun,hbslot,hcb⟩ := exact_C0_parent n c hcrun hcslot
    have hbstate : b.state = B := by
      simpa [readSlot] using congrArg Prod.fst hbslot
    have hbzero : b.tape b.head = false := by
      simpa [readSlot] using congrArg Prod.snd hbslot
    have hbnext : b.tape (b.head+1) = false := by
      have hc0 : c.tape c.head = false := by
        simpa [readSlot] using congrArg Prod.snd hcslot
      rw [hcb] at hc0
      exact (right_head_tape b moveB rfl).symm.trans hc0
    have hbnext2 : b.tape (b.head+2) = true := by
      have hz1 : z.tape z.head=true := by
        simpa [readSlot] using congrArg Prod.snd hzslot
      rw [hzc] at hz1
      have hc1 : c.tape (c.head+1) = true :=
        (right_head_tape c moveC rfl).symm.trans hz1
      rw [hcb] at hc1
      exact (right_next_tape b moveB rfl).symm.trans hc1
    exact ⟨b,hbrun,⟨hbstate,hbzero,hbnext,hbnext2⟩⟩
  · rintro ⟨b,hbrun,hfatal⟩
    obtain ⟨c,hstep,z,hstep2,hslot⟩ := fatal_B_two_moves b hfatal
    have hc : run target429 (n+1) blank = some c := by
      change (run target429 n blank).bind (rawStep target429) = some c
      rw [hbrun]
      exact hstep
    have hz : run target429 (n+2) blank = some z := by
      have hn : n+2=(n+1)+1 := by omega
      rw [hn]
      change (run target429 (n+1) blank).bind (rawStep target429)=some z
      rw [hc]
      exact hstep2
    exact ⟨z,hz,hslot⟩

#print axioms target429_D1_iff_B001
end BB429FatalB

namespace BB429FatalB
open BB6Coverage BB429FEntry BB429PhysicalFrontier

private theorem only_halt_D1 (s : Slot) (h : target429 s = none) :
    s = (D,true) := by
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
      BB429PhysicalFrontier.prefix0, refine, emptyTable, D] at h ⊢

private theorem no_halt0 : ¬HaltsAfter target429 0 := by
  intro h
  have hsome : (run target429 1 blank).isSome = true := by decide
  rw [h.2] at hsome
  contradiction

private theorem no_halt1 : ¬HaltsAfter target429 1 := by
  intro h
  have hsome : (run target429 2 blank).isSome = true := by decide
  rw [h.2] at hsome
  contradiction

theorem target429_halts_iff_root_B001 :
    (∃ n, HaltsAfter target429 n) ↔
    (∃ n b, run target429 n blank = some b ∧ fatalB b) := by
  constructor
  · rintro ⟨t, ht⟩
    cases t with
    | zero => exact False.elim (no_halt0 ht)
    | succ t =>
        cases t with
        | zero => exact False.elim (no_halt1 ht)
        | succ n =>
            have hrun : ∃ z, run target429 (n+2) blank = some z ∧
                 readSlot z = (D,true) := by
              cases hs : run target429 (n+2) blank with
              | none =>
                  have hh : (run target429 (n+2) blank).isSome = true := by
                    simpa [HaltsAfter] using ht.1
                  simp [hs] at hh
              | some z =>
                  have heq : (run target429 (n+2+1) blank) = none := by
                    simpa [HaltsAfter] using ht.2
                  have hstep : rawStep target429 z = none := by
                    change (run target429 (n+2) blank).bind (rawStep target429) = none at heq
                    simpa [hs] using heq
                  have hm : target429 (readSlot z) = none := by
                    simpa [rawStep] using hstep
                  exact ⟨z, rfl, only_halt_D1 _ hm⟩
            exact ⟨n, (target429_D1_iff_B001 n).mp hrun⟩
  · rintro ⟨n,b,hbrun,hfatal⟩
    exact ⟨n+2, fatal_B_causes_halt n b hbrun hfatal⟩

#print axioms target429_halts_iff_root_B001
end BB429FatalB
