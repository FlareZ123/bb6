import DrainDigitTransducerCarry

open DrainState

/-!
# Offset identities for the three-state drain transducer

The two paired runs below read the same ternary suffix after their first
symbol.  Their output digit counts agree, although their terminal states
need not agree.  This is the finite-state offset interface needed when a
root-sector drain input changes by one.
-/

/-- Output and digit counts, deliberately omitting the terminal phase. -/
def runStatsData : Nat → Nat → DrainState → Int × Nat × Nat
  | 0, _, _ => (0, 0, 0)
  | n + 1, b, s =>
      let (s', out) := step s (b % 3)
      let tail := runStatsData n (b / 3) s'
      (out + 3 * tail.1,
       tail.2.1 + (if out = 1 then 1 else 0),
       tail.2.2 + (if out = 2 then 1 else 0))

theorem runStatsData_eq (n b : Nat) (s : DrainState) :
    runStatsData n b s =
      ((runStats n b s).output, (runStats n b s).ones, (runStats n b s).twos) := by
  induction n generalizing b s with
  | zero => simp [runStatsData, runStats]
  | succ n ih =>
      cases hst : step s (b % 3) with
      | mk s' out =>
          simp [runStatsData, runStats, hst, ih]

/--
Mutual offset identities.  For every n-digit suffix q, incrementing q by
one and changing the initial transducer state B→A or A→C leaves the emitted
integer and the counts of output digits 1 and 2 unchanged.  The terminal
state is intentionally not included in this equality.
-/
theorem runStatsData_offset_identities (n : Nat) :
    (∀ q, q + 1 < 3 ^ n →
      runStatsData n (q + 1) B = runStatsData n q A) ∧
    (∀ q, q + 1 < 3 ^ n →
      runStatsData n (q + 1) A = runStatsData n q C) := by
  induction n with
  | zero =>
      constructor <;> intro q hq <;> omega
  | succ n ih =>
      constructor
      · intro q hq
        let k := q / 3
        have hmodlt : q % 3 < 3 := Nat.mod_lt _ (by decide)
        have hcases : q % 3 = 0 ∨ q % 3 = 1 ∨ q % 3 = 2 := by omega
        rcases hcases with h0 | h1 | h2
        · have hplusmod : (q + 1) % 3 = 1 := by
            have hdecomp := Nat.mod_add_div q 3
            omega
          have hplusdiv : (q + 1) / 3 = k := by
            have hdecomp := Nat.mod_add_div q 3
            omega
          simp [runStatsData, step, h0, hplusmod, hplusdiv, k]
        · have hplusmod : (q + 1) % 3 = 2 := by
            have hdecomp := Nat.mod_add_div q 3
            omega
          have hplusdiv : (q + 1) / 3 = k := by
            have hdecomp := Nat.mod_add_div q 3
            omega
          simp [runStatsData, step, h1, hplusmod, hplusdiv, k]
        · have hplusmod : (q + 1) % 3 = 0 := by
            have hdecomp := Nat.mod_add_div q 3
            omega
          have hplusdiv : (q + 1) / 3 = k + 1 := by
            have hdecomp := Nat.mod_add_div q 3
            omega
          have htailBound : k + 1 < 3 ^ n := by
            have hdecomp := Nat.mod_add_div q 3
            rw [Nat.pow_succ] at hq
            omega
          have htail := ih.2 k htailBound
          simpa [runStatsData, step, h2, hplusmod, hplusdiv, k] using
            congrArg (fun t : Int × Nat × Nat => (3 * t.1, t.2.1, t.2.2)) htail
      · intro q hq
        let k := q / 3
        have hmodlt : q % 3 < 3 := Nat.mod_lt _ (by decide)
        have hcases : q % 3 = 0 ∨ q % 3 = 1 ∨ q % 3 = 2 := by omega
        rcases hcases with h0 | h1 | h2
        · have hplusmod : (q + 1) % 3 = 1 := by
            have hdecomp := Nat.mod_add_div q 3
            omega
          have hplusdiv : (q + 1) / 3 = k := by
            have hdecomp := Nat.mod_add_div q 3
            omega
          simp [runStatsData, step, h0, hplusmod, hplusdiv, k]
        · have hplusmod : (q + 1) % 3 = 2 := by
            have hdecomp := Nat.mod_add_div q 3
            omega
          have hplusdiv : (q + 1) / 3 = k := by
            have hdecomp := Nat.mod_add_div q 3
            omega
          simp [runStatsData, step, h1, hplusmod, hplusdiv, k]
        · have hplusmod : (q + 1) % 3 = 0 := by
            have hdecomp := Nat.mod_add_div q 3
            omega
          have hplusdiv : (q + 1) / 3 = k + 1 := by
            have hdecomp := Nat.mod_add_div q 3
            omega
          have htailBound : k + 1 < 3 ^ n := by
            have hdecomp := Nat.mod_add_div q 3
            rw [Nat.pow_succ] at hq
            omega
          have htail := ih.1 k htailBound
          simpa [runStatsData, step, h2, hplusmod, hplusdiv, k] using
            congrArg (fun t : Int × Nat × Nat => (2 + 3 * t.1, t.2.1, t.2.2 + 1)) htail

theorem runStats_offset_BA (n q : Nat) (hq : q + 1 < 3 ^ n) :
    (runStats n (q + 1) B).output = (runStats n q A).output ∧
    (runStats n (q + 1) B).ones = (runStats n q A).ones ∧
    (runStats n (q + 1) B).twos = (runStats n q A).twos := by
  have h := (runStatsData_offset_identities n).1 q hq
  rw [runStatsData_eq, runStatsData_eq] at h
  exact ⟨congrArg Prod.fst h,
    congrArg Prod.fst (congrArg Prod.snd h),
    congrArg Prod.snd (congrArg Prod.snd h)⟩

theorem runStats_offset_AC (n q : Nat) (hq : q + 1 < 3 ^ n) :
    (runStats n (q + 1) A).output = (runStats n q C).output ∧
    (runStats n (q + 1) A).ones = (runStats n q C).ones ∧
    (runStats n (q + 1) A).twos = (runStats n q C).twos := by
  have h := (runStatsData_offset_identities n).2 q hq
  rw [runStatsData_eq, runStatsData_eq] at h
  exact ⟨congrArg Prod.fst h,
    congrArg Prod.fst (congrArg Prod.snd h),
    congrArg Prod.snd (congrArg Prod.snd h)⟩

#print axioms runStatsData_offset_identities
#print axioms runStats_offset_BA
#print axioms runStats_offset_AC
