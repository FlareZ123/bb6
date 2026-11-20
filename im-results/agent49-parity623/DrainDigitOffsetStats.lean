import DrainDigitTransducerCarry

open DrainState

/-!
# Offset identities for the three-state drain transducer

The two paired runs below read the same ternary suffix after their first
symbol.  Their output digit counts and, under the strict n-digit bound, their
exact terminal states agree.  The excluded overflow case q+1=3^n can have a
different terminal state.  This is the finite-state offset interface needed
when a root-sector drain input changes by one.
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
integer and the counts of output digits 1 and 2 unchanged.  The exact terminal
state equality is proved separately by the companion mutual induction below.
-/
theorem runStatsData_offset_identities (n : Nat) :
    (∀ q, q + 1 ≤ 3 ^ n →
      runStatsData n (q + 1) B = runStatsData n q A) ∧
    (∀ q, q + 1 ≤ 3 ^ n →
      runStatsData n (q + 1) A = runStatsData n q C) := by
  induction n with
  | zero =>
      constructor <;> intro q hq <;> simp [runStatsData]
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
          have htailBound : k + 1 ≤ 3 ^ n := by
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
          have htailBound : k + 1 ≤ 3 ^ n := by
            have hdecomp := Nat.mod_add_div q 3
            rw [Nat.pow_succ] at hq
            omega
          have htail := ih.1 k htailBound
          simpa [runStatsData, step, h2, hplusmod, hplusdiv, k] using
            congrArg (fun t : Int × Nat × Nat => (2 + 3 * t.1, t.2.1, t.2.2 + 1)) htail


/--
The same paired induction also preserves the exact terminal transducer
state when the increment stays inside the n-digit range.  The exceptional
carry across the n-digit boundary is excluded by `q+1<3^n`.
-/
theorem runFinalState_offset_identities (n : Nat) :
    (∀ q, q + 1 < 3 ^ n →
      (run n (q + 1) B).2 = (run n q A).2) ∧
    (∀ q, q + 1 < 3 ^ n →
      (run n (q + 1) A).2 = (run n q C).2) := by
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
          simp [run, step, h0, hplusmod, hplusdiv, k]
        · have hplusmod : (q + 1) % 3 = 2 := by
            have hdecomp := Nat.mod_add_div q 3
            omega
          have hplusdiv : (q + 1) / 3 = k := by
            have hdecomp := Nat.mod_add_div q 3
            omega
          simp [run, step, h1, hplusmod, hplusdiv, k]
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
          simpa [run, step, h2, hplusmod, hplusdiv, k] using htail
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
          simp [run, step, h0, hplusmod, hplusdiv, k]
        · have hplusmod : (q + 1) % 3 = 2 := by
            have hdecomp := Nat.mod_add_div q 3
            omega
          have hplusdiv : (q + 1) / 3 = k := by
            have hdecomp := Nat.mod_add_div q 3
            omega
          simp [run, step, h1, hplusmod, hplusdiv, k]
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
          simpa [run, step, h2, hplusmod, hplusdiv, k] using htail

theorem runStats_offset_finalState_BA (n q : Nat) (hq : q + 1 < 3 ^ n) :
    (runStats n (q + 1) B).finalState = (runStats n q A).finalState := by
  rw [runStats_finalState_eq n (q + 1) B, runStats_finalState_eq n q A]
  exact (runFinalState_offset_identities n).1 q hq

theorem runStats_offset_finalState_AC (n q : Nat) (hq : q + 1 < 3 ^ n) :
    (runStats n (q + 1) A).finalState = (runStats n q C).finalState := by
  rw [runStats_finalState_eq n (q + 1) A, runStats_finalState_eq n q C]
  exact (runFinalState_offset_identities n).2 q hq

#print axioms runFinalState_offset_identities
#print axioms runStats_offset_finalState_BA
#print axioms runStats_offset_finalState_AC

theorem runStats_offset_BA (n q : Nat) (hq : q + 1 ≤ 3 ^ n) :
    (runStats n (q + 1) B).output = (runStats n q A).output ∧
    (runStats n (q + 1) B).ones = (runStats n q A).ones ∧
    (runStats n (q + 1) B).twos = (runStats n q A).twos := by
  have h := (runStatsData_offset_identities n).1 q hq
  have h' : ((runStats n (q + 1) B).output, (runStats n (q + 1) B).ones, (runStats n (q + 1) B).twos) =
      ((runStats n q A).output, (runStats n q A).ones, (runStats n q A).twos) := by
    simpa only [runStatsData_eq] using h
  exact ⟨congrArg Prod.fst h',
    congrArg Prod.fst (congrArg Prod.snd h'),
    congrArg Prod.snd (congrArg Prod.snd h')⟩

theorem runStats_offset_AC (n q : Nat) (hq : q + 1 ≤ 3 ^ n) :
    (runStats n (q + 1) A).output = (runStats n q C).output ∧
    (runStats n (q + 1) A).ones = (runStats n q C).ones ∧
    (runStats n (q + 1) A).twos = (runStats n q C).twos := by
  have h := (runStatsData_offset_identities n).2 q hq
  have h' : ((runStats n (q + 1) A).output, (runStats n (q + 1) A).ones, (runStats n (q + 1) A).twos) =
      ((runStats n q C).output, (runStats n q C).ones, (runStats n q C).twos) := by
    simpa only [runStatsData_eq] using h
  exact ⟨congrArg Prod.fst h',
    congrArg Prod.fst (congrArg Prod.snd h),
    congrArg Prod.snd (congrArg Prod.snd h)⟩

#print axioms runStatsData_offset_identities
#print axioms runStats_offset_BA
#print axioms runStats_offset_AC

theorem runStats_offset_phase_BA (n q : Nat) (hq : q + 1 < 3 ^ n) :
    phaseBit (runStats n (q + 1) B).finalState =
      phaseBit (runStats n q A).finalState := by
  have hleft := run_phase n (q + 1) B hq
  have hright := run_phase n q A (by omega)
  rw [runStats_finalState_eq n (q + 1) B, runStats_finalState_eq n q A]
  simp [phaseBit] at hleft hright
  omega

theorem runStats_offset_phase_AC (n q : Nat) (hq : q + 1 < 3 ^ n) :
    phaseBit (runStats n (q + 1) A).finalState =
      phaseBit (runStats n q C).finalState := by
  have hleft := run_phase n (q + 1) A hq
  have hright := run_phase n q C (by omega)
  rw [runStats_finalState_eq n (q + 1) A, runStats_finalState_eq n q C]
  simp [phaseBit] at hleft hright
  omega

#print axioms runStats_offset_phase_BA
#print axioms runStats_offset_phase_AC

theorem runStats_offset_BA_full (n q : Nat) (hq : q + 1 < 3 ^ n) :
    runStats n (q + 1) B = runStats n q A := by
  rcases runStats_offset_BA n q (by omega) with ⟨hout, hones, htwos⟩
  have hstate := runStats_offset_finalState_BA n q hq
  cases hleft : runStats n (q + 1) B with
  | mk outL onesL twosL stateL =>
      cases hright : runStats n q A with
      | mk outR onesR twosR stateR =>
          simp [hleft, hright] at hout hones htwos hstate
          simp [hleft, hright, hout, hones, htwos, hstate]

theorem runStats_offset_AC_full (n q : Nat) (hq : q + 1 < 3 ^ n) :
    runStats n (q + 1) A = runStats n q C := by
  rcases runStats_offset_AC n q (by omega) with ⟨hout, hones, htwos⟩
  have hstate := runStats_offset_finalState_AC n q hq
  cases hleft : runStats n (q + 1) A with
  | mk outL onesL twosL stateL =>
      cases hright : runStats n q C with
      | mk outR onesR twosR stateR =>
          simp [hleft, hright] at hout hones htwos hstate
          simp [hleft, hright, hout, hones, htwos, hstate]

#print axioms runStats_offset_BA_full
#print axioms runStats_offset_AC_full


/--
At the overflow boundary q+1=3^n, the paired output/count data still agree,
but the terminal states alternate through the indicated two-state pairs.
-/
theorem run_overflow_final_state_pairs (n : Nat) :
    (run n (3 ^ n) B).2 = (if n % 2 = 1 then A else B) ∧
    (run n (3 ^ n - 1) A).2 = (if n % 2 = 1 then C else A) ∧
    (run n (3 ^ n) A).2 = (if n % 2 = 1 then B else A) ∧
    (run n (3 ^ n - 1) C).2 = (if n % 2 = 1 then A else C) := by
  induction n with
  | zero =>
      simp [run]
  | succ n ih =>
      rcases ih with ⟨hBAleft, hBAright, hACleft, hACright⟩
      have hpow : 3 ^ (n + 1) = 3 * 3 ^ n := by
        simp [Nat.pow_succ, Nat.mul_comm]
      have hpos : 0 < 3 ^ n := by positivity
      have hsub : 3 ^ (n + 1) - 1 = 3 * (3 ^ n - 1) + 2 := by
        rw [hpow]
        omega
      have hmod0 : (3 * 3 ^ n) % 3 = 0 := by omega
      have hdiv0 : (3 * 3 ^ n) / 3 = 3 ^ n := by omega
      have hmod2 : (3 * (3 ^ n - 1) + 2) % 3 = 2 := by omega
      have hdiv2 : (3 * (3 ^ n - 1) + 2) / 3 = 3 ^ n - 1 := by omega
      have hparityFlip : (n + 1) % 2 = (if n % 2 = 1 then 0 else 1) := by
        have hlt : n % 2 < 2 := Nat.mod_lt _ (by decide)
        omega
      constructor
      · rw [hpow]
        simp [run, step, hmod0, hdiv0]
        rw [hACleft]
        simp [hparityFlip]
      · constructor
        · rw [hsub]
          simp [run, step, hmod2, hdiv2]
          rw [hACright]
          simp [hparityFlip]
        · constructor
          · rw [hpow]
            simp [run, step, hmod0, hdiv0]
            rw [hBAleft]
            simp [hparityFlip]
          · rw [hsub]
            simp [run, step, hmod2, hdiv2]
            rw [hBAright]
            simp [hparityFlip]

/-- The strict range condition is essential: at the first overflow boundary,
the paired terminal states can differ. -/
#print axioms run_overflow_final_state_pairs

theorem run_offset_overflow_BA_final_state_differs :
    (run 1 3 B).2 ≠ (run 1 2 A).2 := by decide

theorem run_offset_overflow_AC_final_state_differs :
    (run 1 3 A).2 ≠ (run 1 2 C).2 := by decide

#print axioms run_offset_overflow_BA_final_state_differs
#print axioms run_offset_overflow_AC_final_state_differs
