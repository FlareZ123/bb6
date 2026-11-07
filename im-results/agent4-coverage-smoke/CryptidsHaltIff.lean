import CryptidsTapeAdapter

namespace BB6.ConjectureBridge

/-- The finite local source iterator, using exactly the primitive
    ConjectureMachines step function that underlies its halting predicate. -/
def sourceRun (m : ConjectureMachines.Machine 6 2) :
    Nat → Option (ConjectureMachines.Cfg 6 2)
  | 0 => some ConjectureMachines.init
  | n+1 => (sourceRun m n).bind (ConjectureMachines.step m)

/-- The state/tape projection of one fully positioned physical step. -/
theorem positioned_step_cfg (m : ConjectureMachines.Machine 6 2)
    (p : Positioned) :
    (step m p).map Positioned.cfg =
      ConjectureMachines.step m p.cfg := by
  cases h : m.transition p.cfg.state p.cfg.tape.head with
  | none => simp [step, ConjectureMachines.step, h]
  | some a =>
    rcases a with ⟨w, d, q⟩
    simp [step, ConjectureMachines.step, h]

/-- All finite positioned runs project to the original source run. -/
theorem positioned_run_cfg (m : ConjectureMachines.Machine 6 2)
    (n : Nat) :
    (run m n initialPositioned).map Positioned.cfg =
      sourceRun m n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    change ((run m n initialPositioned).bind (step m)).map
        Positioned.cfg =
      (sourceRun m n).bind (ConjectureMachines.step m)
    rw [← ih]
    cases hp : run m n initialPositioned with
    | none => simp [hp]
    | some p => simpa [hp] using positioned_step_cfg m p

/-- Each finite successful source run has a genuine primitive-step
    reachability witness, with no bounded-tape assumption. -/
theorem sourceRun_reaches (m : ConjectureMachines.Machine 6 2)
    (n : Nat) (c : ConjectureMachines.Cfg 6 2)
    (hc : sourceRun m n = some c) :
    StateTransition.Reaches (ConjectureMachines.step m)
      ConjectureMachines.init c := by
  induction n generalizing c with
  | zero =>
    simp only [sourceRun] at hc
    cases hc
    exact Relation.ReflTransGen.refl
  | succ n ih =>
    cases hp : sourceRun m n with
    | none => simp [sourceRun, hp] at hc
    | some p =>
      have hs : ConjectureMachines.step m p = some c := by
        simpa [sourceRun, hp] using hc
      exact Relation.ReflTransGen.tail (ih p hp) hs

/-- Every source-reachable configuration is attained at a finite
    iteration index of the identical primitive transition semantics. -/
theorem sourceRun_of_reaches (m : ConjectureMachines.Machine 6 2)
    (c : ConjectureMachines.Cfg 6 2)
    (hc : StateTransition.Reaches (ConjectureMachines.step m)
      ConjectureMachines.init c) :
    ∃ n, sourceRun m n = some c := by
  induction hc with
  | refl => exact ⟨0, rfl⟩
  | @tail b c hprev hstep ih =>
    obtain ⟨n, hn⟩ := ih
    cases hs : ConjectureMachines.step m b with
    | none => simp [hs] at hstep
    | some c' =>
      have hc : c' = c := by simpa [hs] using hstep
      subst c'
      exact ⟨n+1, by simp [sourceRun, hn, hs]⟩

/-- Mathematically exact equivalence of finite physical halting and
    upstream's partial-computation-domain halting definition. -/
theorem source_halts_iff_finite_none (m : ConjectureMachines.Machine 6 2) :
    ConjectureMachines.Halts m ↔ ∃ n, sourceRun m n = none := by
  constructor
  · intro hh
    unfold ConjectureMachines.Halts at hh
    rw [Part.dom_iff_mem] at hh
    obtain ⟨c, hc⟩ := hh
    obtain ⟨hr, hs⟩ := (ConjectureMachines.mem_eval').mp hc
    obtain ⟨n, hn⟩ := sourceRun_of_reaches m c hr
    exact ⟨n+1, by simp [sourceRun, hn, hs]⟩
  · rintro ⟨n, hn⟩
    have hstop : ∃ c, StateTransition.Reaches
        (ConjectureMachines.step m) ConjectureMachines.init c ∧
        ConjectureMachines.step m c = none := by
      induction n with
      | zero => simp [sourceRun] at hn
      | succ n ih =>
        cases hp : sourceRun m n with
        | none => exact ih hp
        | some c =>
          have hs : ConjectureMachines.step m c = none := by
            simpa [sourceRun, hp] using hn
          exact ⟨c, sourceRun_reaches m n c hp, hs⟩
    rcases hstop with ⟨c, hr, hs⟩
    unfold ConjectureMachines.Halts
    rw [Part.dom_iff_mem]
    exact ⟨c, (ConjectureMachines.mem_eval').mpr ⟨hr, hs⟩⟩

/-- Exact primitive-step halting equivalence at **every fixed step index**
    for the original source machine and the independent absolute-tape model.
    The equality of timestamps is stronger than eventual halting alone. -/
theorem sourceRun_none_iff_original_none
    (m : ConjectureMachines.Machine 6 2) (n : Nat) :
    BB6Coverage.run (toAgent8 m) n BB6Coverage.blank = none ↔
      sourceRun m n = none := by
  rw [blank_run_toAbsolute, ← positioned_run_cfg]
  cases hp : run m n initialPositioned with
  | none => simp [hp]
  | some p => simp [hp]

/-- For every raw six-state, two-symbol transition table, the existing
    quotient-tape adapter preserves *both directions* of eventual halting. -/
theorem conjecture_halts_iff_agent8_halts
    (m : ConjectureMachines.Machine 6 2) :
    ConjectureMachines.Halts m ↔
      ∃ n, BB6Coverage.run (toAgent8 m) n BB6Coverage.blank = none := by
  rw [source_halts_iff_finite_none]
  have hpoint := sourceRun_none_iff_original_none m
  constructor
  · rintro ⟨n, hn⟩
    exact ⟨n, (hpoint n).mpr hn⟩
  · rintro ⟨n, hn⟩
    exact ⟨n, (hpoint n).mp hn⟩

/-- Both directions of *nonhalting* transfer, including a converse to
    the existing source-to-original adapter used by A6/F287. -/
theorem conjecture_nonhalts_iff_agent8_never
    (m : ConjectureMachines.Machine 6 2) :
    ¬ ConjectureMachines.Halts m ↔
      BB6Coverage.NeverHalts (toAgent8 m) := by
  rw [conjecture_halts_iff_agent8_halts]
  constructor
  · intro h n
    cases hr : BB6Coverage.run (toAgent8 m) n BB6Coverage.blank with
    | none => exact False.elim (h ⟨n, hr⟩)
    | some c => rfl
  · intro h ⟨n, hr⟩
    have hlive := h n
    simp [hr] at hlive

#print axioms sourceRun_none_iff_original_none
#print axioms conjecture_nonhalts_iff_agent8_never

#print axioms sourceRun_reaches
#print axioms sourceRun_of_reaches
#print axioms source_halts_iff_finite_none
#print axioms conjecture_halts_iff_agent8_halts

end BB6.ConjectureBridge
