import Frontier
import Lean.Elab.Tactic.Omega

namespace BB6Coverage

/-- Historical six-state holdout line 310: 1RB0LC_1LC0RB_0LE1LD_1LB1LA_0RA1LF_0LA---. -/
def root310 : Machine := fun s =>
  match s.1.val, s.2 with
  | 0, false => some ⟨true, true, 1⟩
  | 0, true  => some ⟨false, false, 2⟩
  | 1, false => some ⟨true, false, 2⟩
  | 1, true  => some ⟨false, true, 1⟩
  | 2, false => some ⟨false, false, 4⟩
  | 2, true  => some ⟨true, false, 3⟩
  | 3, false => some ⟨true, false, 1⟩
  | 3, true  => some ⟨true, false, 0⟩
  | 4, false => some ⟨false, true, 0⟩
  | 4, true  => some ⟨true, false, 5⟩
  | 5, false => some ⟨false, false, 0⟩
  | _, _ => none

/-- The unique raw three-step-to-halt source pattern, including both actual
    physical cells immediately to the left of a C/zero head. -/
def gate310 (c : Config) : Prop :=
  c.state = (2 : Fin 6) ∧ c.tape c.head = false ∧
  c.tape (c.head - 1) = true ∧ c.tape (c.head - 2) = true

theorem halt_slot_310 (c : Config) :
    root310 (readSlot c) = none ↔ c.state = (5 : Fin 6) ∧ c.tape c.head = true := by
  rcases c with ⟨state, head, tape⟩
  rcases state with ⟨n, hn⟩
  have hn0 : n=0 ∨ n=1 ∨ n=2 ∨ n=3 ∨ n=4 ∨ n=5 := by omega
  rcases hn0 with h0 | h1 | h2 | h3 | h4 | h5 <;> subst n <;>
    cases hb : tape head <;> simp [root310, hb]

theorem only_enter_F_all :
  ∀ s : Slot, ((root310 s).map Move.next = some 5) ↔ s=(4,true) := by
  intro s
  rcases s with ⟨state, bit⟩
  rcases state with ⟨n, hn⟩
  have hs : n=0 ∨ n=1 ∨ n=2 ∨ n=3 ∨ n=4 ∨ n=5 := by omega
  rcases hs with h0 | h1 | h2 | h3 | h4 | h5 <;> subst n <;>
    cases bit <;> simp [root310, Fin.ext_iff] <;> decide

theorem only_enter_E_all :
  ∀ s : Slot, ((root310 s).map Move.next = some 4) ↔ s=(2,false) := by
  intro s
  rcases s with ⟨state, bit⟩
  rcases state with ⟨n, hn⟩
  have hs : n=0 ∨ n=1 ∨ n=2 ∨ n=3 ∨ n=4 ∨ n=5 := by omega
  rcases hs with h0 | h1 | h2 | h3 | h4 | h5 <;> subst n <;>
    cases bit <;> simp [root310, Fin.ext_iff] <;> decide

theorem predecessor_F (c d : Config)
    (h : rawStep root310 c = some d) (hd : d.state = 5) :
    c.state = 4 ∧ c.tape c.head = true ∧
    d.head = c.head - 1 ∧ d.tape d.head = c.tape (c.head - 1) := by
  unfold rawStep at h
  cases hs : root310 (readSlot c) with
  | none => simp [hs] at h
  | some mv =>
    simp only [hs, Option.map_some, Option.some.injEq] at h
    subst d
    have hn : mv.next = 5 := by simpa [applyMove] using hd
    have hmap : (root310 (readSlot c)).map Move.next = some 5 := by
      simp [hs, hn]
    have hslot : readSlot c = (4,true) := (only_enter_F_all _).mp hmap
    have hstate : c.state = 4 := congrArg Prod.fst hslot
    have hbit : c.tape c.head = true := congrArg Prod.snd hslot
    have hmv : mv = ⟨true,false,5⟩ := by
      have hlookup : root310 (readSlot c) = some ⟨true,false,5⟩ := by
        rw [hslot]
        rfl
      rw [hlookup] at hs
      exact (Option.some.inj hs).symm
    subst mv
    refine ⟨hstate, hbit, ?_, ?_⟩
    · simp [applyMove]; omega
    · change (if c.head - 1 = c.head then true else c.tape (c.head-1)) =
        c.tape (c.head - 1)
      have hx : c.head - 1 ≠ c.head := by omega
      simp [hx]

theorem predecessor_E (c d : Config)
    (h : rawStep root310 c = some d) (hd : d.state = 4) :
    c.state = 2 ∧ c.tape c.head = false ∧
    d.head = c.head - 1 ∧
    d.tape d.head = c.tape (c.head-1) ∧
    d.tape (d.head-1) = c.tape (c.head-2) := by
  unfold rawStep at h
  cases hs : root310 (readSlot c) with
  | none => simp [hs] at h
  | some mv =>
    simp only [hs, Option.map_some, Option.some.injEq] at h
    subst d
    have hn : mv.next = 4 := by simpa [applyMove] using hd
    have hmap : (root310 (readSlot c)).map Move.next = some 4 := by
      simp [hs, hn]
    have hslot : readSlot c = (2,false) := (only_enter_E_all _).mp hmap
    have hstate : c.state = 2 := congrArg Prod.fst hslot
    have hbit : c.tape c.head = false := congrArg Prod.snd hslot
    have hmv : mv = ⟨false,false,4⟩ := by
      have hlookup : root310 (readSlot c) = some ⟨false,false,4⟩ := by
        rw [hslot]
        rfl
      rw [hlookup] at hs
      exact (Option.some.inj hs).symm
    subst mv
    refine ⟨hstate, hbit, ?_, ?_, ?_⟩
    · simp [applyMove]; omega
    · change (if c.head - 1 = c.head then false else c.tape (c.head-1)) =
        c.tape (c.head - 1)
      have hx : c.head - 1 ≠ c.head := by omega
      simp [hx]
    · change (if (c.head - 1)-1 = c.head then false else c.tape ((c.head-1)-1)) =
        c.tape (c.head - 2)
      have hx : (c.head - 1)-1 ≠ c.head := by omega
      have heq : (c.head - 1)-1 = c.head - 2 := by omega
      rw [if_neg hx, heq]

theorem critical_310_necessary (c0 c1 c2 : Config)
    (h01 : rawStep root310 c0 = some c1)
    (h12 : rawStep root310 c1 = some c2)
    (hhalt : rawStep root310 c2 = none) : gate310 c0 := by
  have hf : c2.state = 5 ∧ c2.tape c2.head = true := by
    apply (halt_slot_310 c2).mp
    simpa only [rawStep, Option.map_eq_none_iff] using hhalt
  have h1 := predecessor_F c1 c2 h12 hf.1
  have h0 := predecessor_E c0 c1 h01 h1.1
  exact ⟨h0.1, h0.2.1, h0.2.2.2.1.symm.trans h1.2.1,
    h0.2.2.2.2.symm.trans (h1.2.2.2.symm.trans hf.2)⟩

theorem critical_310_sufficient (c : Config) (h : gate310 c) :
    ∃ c1 c2 : Config, rawStep root310 c = some c1 ∧
      rawStep root310 c1 = some c2 ∧ rawStep root310 c2 = none := by
  rcases h with ⟨hstate, hbit, hleft1, hleft2⟩
  let c1 := applyMove c ⟨false,false,4⟩
  let c2 := applyMove c1 ⟨true,false,5⟩
  have h0 : rawStep root310 c = some c1 := by
    have hslot : readSlot c = (2,false) := by
      exact Prod.ext hstate hbit
    simp only [rawStep, hslot]
    rfl
  have hhead1 : c1.head = c.head-1 := by simp [c1,applyMove]; omega
  have hbit1 : c1.tape c1.head = true := by
    have hneq : c.head-1≠c.head := by omega
    change (if c.head - 1 = c.head then false else c.tape (c.head - 1)) = true
    rw [if_neg hneq, hleft1]
  have hslot1 : readSlot c1 = (4,true) := by
    exact Prod.ext rfl hbit1
  have h1 : rawStep root310 c1 = some c2 := by
    simp only [rawStep, hslot1]
    rfl
  have hhead2 : c2.head = c.head-2 := by
    simp [c2,applyMove,hhead1]
    omega
  have hbit2 : c2.tape c2.head = true := by
    have hneq : c.head-2≠c.head-1 := by omega
    have hneq0 : c.head-2≠c.head := by omega
    change (if c.head - 1 - 1 = c.head - 1 then true else
      (if c.head - 1 - 1 = c.head then false else c.tape (c.head - 1 - 1))) = true
    have heq : c.head - 1 - 1 = c.head - 2 := by omega
    rw [if_neg (by omega : c.head - 1 - 1 ≠ c.head - 1),
      if_neg (by omega : c.head - 1 - 1 ≠ c.head),heq,hleft2]
  have hslot2 : readSlot c2 = (5,true) := by
    exact Prod.ext rfl hbit2
  refine ⟨c1,c2,h0,h1,?_⟩
  simp only [rawStep,hslot2]
  rfl

theorem critical_310_iff (c : Config) :
    gate310 c ↔ ∃ c1 c2 : Config, rawStep root310 c = some c1 ∧
      rawStep root310 c1 = some c2 ∧ rawStep root310 c2 = none := by
  constructor
  · exact critical_310_sufficient c
  · rintro ⟨c1,c2,h01,h12,hh⟩
    exact critical_310_necessary c c1 c2 h01 h12 hh

theorem run_live_previous (m : Machine) (c : Config) (n : Nat)
    (h : (run m (n+1) c).isSome = true) :
    (run m n c).isSome = true := by
  cases hn : run m n c with
  | none => simp [run, hn] at h
  | some x => rfl

/-- The root machine halts iff its actual blank-origin run ever visits the
    exact four-cell marked C/0 gate. The equivalence is all-time. -/
theorem root310_halts_iff_gate :
    (∃ n : Nat, (run root310 n blank).isSome = true ∧
      run root310 (n+1) blank = none) ↔
      ∃ (n : Nat) (c : Config), run root310 n blank = some c ∧ gate310 c := by
  constructor
  · rintro ⟨n, hsome, hnone⟩
    have hbound : 2 ≤ n := by
      by_cases hlt : n < 2
      · have hh : n = 0 ∨ n = 1 := by omega
        rcases hh with hzero | hone
        · subst n
          have hnon : run root310 1 blank ≠ none := by decide
          exact False.elim (hnon hnone)
        · subst n
          have hnon : run root310 2 blank ≠ none := by decide
          exact False.elim (hnon hnone)
      · omega
    let k := n - 2
    have hn : n = k + 2 := by dsimp [k]; omega
    have hk1 : (run root310 (k+1) blank).isSome = true := by
      have hs2 : (run root310 (k+1+1) blank).isSome = true := by
        simpa only [show k+1+1=n by omega] using hsome
      exact run_live_previous root310 blank (k+1) hs2
    have hk0 : (run root310 k blank).isSome = true :=
      run_live_previous root310 blank k hk1
    cases h0 : run root310 k blank with
    | none => simp [h0] at hk0
    | some c0 =>
      cases h1 : run root310 (k+1) blank with
      | none => simp [h1] at hk1
      | some c1 =>
        cases h2 : run root310 n blank with
        | none => simp [h2] at hsome
        | some c2 =>
          have h01 : rawStep root310 c0 = some c1 := by
            have h : run root310 (k+1) blank =
                (run root310 k blank).bind (rawStep root310) := rfl
            simpa [h0] using h.symm.trans h1
          have h12 : rawStep root310 c1 = some c2 := by
            have h : run root310 n blank =
                (run root310 (k+1) blank).bind (rawStep root310) := by
              rw [hn]
              rfl
            simpa [h1] using h.symm.trans h2
          have hhalt : rawStep root310 c2 = none := by
            have h : run root310 (n+1) blank =
                (run root310 n blank).bind (rawStep root310) := rfl
            simpa [h2] using h.symm.trans hnone
          exact ⟨k,c0,h0,critical_310_necessary c0 c1 c2 h01 h12 hhalt⟩
  · rintro ⟨n,c0,h0,hg⟩
    obtain ⟨c1,c2,h01,h12,hh⟩ := critical_310_sufficient c0 hg
    have h1 : run root310 (n+1) blank = some c1 := by
      simp [run,h0,h01]
    have h2 : run root310 (n+2) blank = some c2 := by
      rw [show n+2 = (n+1)+1 by omega,run,h1]
      exact h12
    refine ⟨n+2, ?_, ?_⟩
    · simp [h2]
    · rw [show n+2+1=(n+2)+1 by omega,run,h2]
      exact hh

#print axioms critical_310_iff
#print axioms root310_halts_iff_gate

end BB6Coverage
