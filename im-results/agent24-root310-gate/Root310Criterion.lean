import Root310Gate

namespace BB6Coverage

/-- Exact and all-time reduction of the nonhalting problem for this root to
    exclusion of the unique C/0 and marked-left-pair gate. -/
theorem root310_never_iff_forbid_gate :
    NeverHalts root310 ↔
      ∀ n : Nat, ∀ c : Config, run root310 n blank = some c → ¬ gate310 c := by
  constructor
  · intro hnever n c hrun hgate
    obtain ⟨t, _, hhalt⟩ := (root310_halts_iff_gate).mpr ⟨n,c,hrun,hgate⟩
    have hs := hnever (t+1)
    simp [hhalt] at hs
  · intro hforbid n
    induction n with
    | zero => rfl
    | succ n ih =>
      cases hn : run root310 (n+1) blank with
      | some d => rfl
      | none =>
        obtain ⟨k,c,hreach,hgate⟩ :=
          (root310_halts_iff_gate).mp ⟨n,ih,hn⟩
        exact False.elim (hforbid k c hreach hgate)

#print axioms root310_never_iff_forbid_gate
end BB6Coverage
