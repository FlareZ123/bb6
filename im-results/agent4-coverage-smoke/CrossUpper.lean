import CrossCoverage
namespace BB6.CoverageAdapter

/-- Every canonical simple action has a raw 28-choice representative. -/
def toAgent13Raw (m : BB6Coverage.Machine) : BB6.Coverage.RawMachine :=
  fun q b => BB6.Coverage.liftInstruction (toAgent13Machine m q b)

private theorem normalize_toAgent13Raw (m : BB6Coverage.Machine) :
    BB6.Coverage.normalize (toAgent13Raw m) = toAgent13Machine m := by
  funext q b
  simp [BB6.Coverage.normalize, toAgent13Raw, BB6.Coverage.normalize_liftInstruction]

/-- Raw universal runtime bounds are equivalent in both implementations. -/
theorem universal_raw_upper_iff (B : Nat) :
    (∀ m : BB6Coverage.Machine, ∀ n : Nat,
       BB6Coverage.HaltsAfter m n → n+1 ≤ B) ↔
    (∀ m : BB6.Coverage.RawMachine, ∀ n : Nat,
       BB6.Coverage.HaltsAt (BB6.Coverage.tickRaw m) n → n ≤ B) := by
  constructor
  · intro h m n hn
    cases n with
    | zero =>
      exact False.elim (BB6.Coverage.haltsAt_zero_impossible _ hn)
    | succ k =>
      have h13 : BB6.Coverage.HaltsAt
          (BB6.Coverage.tick (BB6.Coverage.normalize m)) (k+1) := by
        simpa only [BB6.Coverage.tickRaw] using hn
      exact h (toAgent8Machine (BB6.Coverage.normalize m)) k
        ((halts_agree (BB6.Coverage.normalize m) k).mp h13)
  · intro h m n hn
    have h13 : BB6.Coverage.HaltsAt
        (BB6.Coverage.tickRaw (toAgent13Raw m)) (n+1) := by
      change BB6.Coverage.HaltsAt
        (BB6.Coverage.tick (BB6.Coverage.normalize (toAgent13Raw m))) (n+1)
      rw [normalize_toAgent13Raw]
      apply (halts_agree (toAgent13Machine m) n).mpr
      simpa only [toAgent8_toAgent13] using hn
    exact h (toAgent13Raw m) (n+1) h13

/-- Agent13's 25-code full-table runtime bound is precisely Agent8's
    full-table bound, with no missing or duplicated machine outcomes. -/
theorem universal_code_upper_iff (B : Nat) :
    (∀ m : BB6Coverage.Machine, ∀ n : Nat,
       BB6Coverage.HaltsAfter m n → n+1 ≤ B) ↔
    (∀ m : BB6.Coverage.CodeMachine, ∀ n : Nat,
       BB6.Coverage.HaltsAt (BB6.Coverage.tick (BB6.Coverage.decodeMachine m)) n → n ≤ B) :=
  (universal_raw_upper_iff B).trans (BB6.Coverage.universal_bound_iff B)

/-- A fully checked Agent8 Cover cert bounds every Agent13 raw six-state machine. -/
theorem cover_gives_agent13_raw_upper (B : Nat)
    (cert : BB6Coverage.Cover (BB6Coverage.DecidedBelow B) BB6Coverage.emptyTable) :
    ∀ m : BB6.Coverage.RawMachine, ∀ n : Nat,
      BB6.Coverage.HaltsAt (BB6.Coverage.tickRaw m) n → n ≤ B := by
  apply (universal_raw_upper_iff B).mp
  intro m n hn
  exact BB6Coverage.maximal_runtime_if_cover B cert (n+1) ⟨m,n,hn,rfl⟩

end BB6.CoverageAdapter
