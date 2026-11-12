import Lean.Elab.Tactic.Omega
import PacketRank

namespace BB6.Agent2PacketSafe
open BB6.Agent31PacketRank

/-- A guarded B/E packet step preserves the counter p modulo three. -/
theorem advance_pmod {c d : Packet} (h : advance c = some d) :
    d.p % 3 = c.p % 3 := by
  unfold advance at h
  split at h
  · split at h
    · contradiction
    · injection h with heq
      subst d
      rfl
  · split at h
    · split at h
      · contradiction
      · injection h with heq
        subst d
        change (c.p-3)%3 = c.p%3
        omega
    · contradiction

/-- Guarded packet steps preserve the physically source-valid a≥4 regime. -/
theorem advance_amin {c d : Packet}
  (h : advance c = some d) (_hc : c.a ≥ 4) : d.a ≥ 4 := by
  unfold advance at h
  split at h
  · split at h
    · contradiction
    · injection h with heq
      subst d
      change 8*((c.a-2)/3)+10≥4
      omega
  · split at h
    · split at h
      · contradiction
      · injection h with heq
        subst d
        change 8*((c.a-4)/3)+9≥4
        omega
    · contradiction

/-- Across the complete well-founded guarded normalization, p mod 3 is fixed. -/
theorem normalize_pmod (c : Packet) :
    (normalizeWithCount c).2.p % 3 = c.p % 3 := by
  rw [normalizeWithCount]
  split
  · rfl
  · rename_i d h
    have hr := advance_pmod h
    have ih := normalize_pmod d
    cases hrec : normalizeWithCount d with
    | mk n e =>
      simpa [hrec] using ih.trans hr
termination_by rank c
decreasing_by
  rename_i _ih d _h1 _h2 heq
  have hs := advance_rank heq
  omega

/-- Normalization of a source-valid unary block never creates the a=1 hole. -/
theorem normalize_amin (c : Packet) (hc : c.a ≥ 4) :
    (normalizeWithCount c).2.a ≥ 4 := by
  rw [normalizeWithCount]
  split
  · exact hc
  · rename_i d h
    have hd := advance_amin h hc
    have ih := normalize_amin d hd
    cases hrec : normalizeWithCount d with
    | mk n e => simpa [hrec] using ih
termination_by rank c
decreasing_by
  rename_i _ih d _h1 _h2 heq
  have hs := advance_rank heq
  omega

/-- The normalizer reaches an actual terminal guarded-packet state. -/
theorem normalize_terminal (c : Packet) :
    advance (normalizeWithCount c).2 = none := by
  rw [normalizeWithCount]
  split
  · assumption
  · rename_i d h
    have ih := normalize_terminal d
    cases hrec : normalizeWithCount d with
    | mk n e => simpa [hrec] using ih
termination_by rank c
decreasing_by
  rename_i _ih d _h1 _h2 heq
  have hs := advance_rank heq
  omega

theorem normalize_nonlow_two (c : Packet) (hp : c.p % 3 ≠ 2) :
    (normalizeWithCount c).2.p ≠ 2 := by
  intro heq
  have hmod := normalize_pmod c
  rw [heq] at hmod
  omega

/-- The p≠2 (mod 3) subgrammar can only leave its guarded phase by A,
    B with q=0, or E with p=0/1. In particular it never enters the
    exceptional E,p=2 suffix reset, for any unbounded unary parameter. -/
theorem normalize_safe_exit (c : Packet) (ha : c.a ≥ 4)
    (hp : c.p % 3 ≠ 2) :
    let d := (normalizeWithCount c).2
    d.a % 3 = 0 ∨ (d.a % 3 = 2 ∧ d.q = 0) ∨
      (d.a % 3 = 1 ∧ (d.p = 0 ∨ d.p = 1)) := by
  let d := (normalizeWithCount c).2
  change d.a % 3 = 0 ∨ (d.a % 3 = 2 ∧ d.q = 0) ∨
    (d.a % 3 = 1 ∧ (d.p = 0 ∨ d.p = 1))
  have he : advance d = none := normalize_terminal c
  have hamin : d.a ≥ 4 := normalize_amin c ha
  have hpnot : d.p ≠ 2 := normalize_nonlow_two c hp
  by_cases h2 : d.a % 3 = 2
  · have hq : d.q = 0 := by
      by_cases hq : d.q = 0
      · exact hq
      · unfold advance at he
        simp [h2, hq] at he
    exact Or.inr (Or.inl ⟨h2,hq⟩)
  by_cases h1 : d.a % 3 = 1
  · have hlt : d.p < 3 := by
      by_cases hlt : d.p < 3
      · exact hlt
      · unfold advance at he
        have ha : ¬ d.a < 4 := by omega
        simp [h1,ha,hlt] at he
    have hsmall : d.p=0 ∨ d.p=1 := by omega
    exact Or.inr (Or.inr ⟨h1,hsmall⟩)
  have hzero : d.a % 3 = 0 := by omega
  exact Or.inl hzero

/-- For p≡2 (mod 3), the guarded normalizer can only terminate
    at A, at B with q=0, or at the exceptional E,p=2 boundary. -/
theorem normalize_p2_exit (c : Packet) (ha : c.a ≥ 4)
    (hp : c.p % 3 = 2) :
    let d := (normalizeWithCount c).2
    d.a % 3 = 0 ∨ (d.a % 3 = 2 ∧ d.q = 0) ∨
      (d.a % 3 = 1 ∧ d.p = 2) := by
  let d := (normalizeWithCount c).2
  change d.a % 3 = 0 ∨ (d.a % 3 = 2 ∧ d.q = 0) ∨
    (d.a % 3 = 1 ∧ d.p = 2)
  have he : advance d = none := normalize_terminal c
  have hamin : d.a ≥ 4 := normalize_amin c ha
  have hpmod : d.p % 3 = 2 := by
    simpa [d,hp] using normalize_pmod c
  by_cases h2 : d.a % 3 = 2
  · have hq : d.q = 0 := by
      by_contra hq
      unfold advance at he
      simp [h2,hq] at he
    exact Or.inr (Or.inl ⟨h2,hq⟩)
  by_cases h1 : d.a % 3 = 1
  · have hp2 : d.p = 2 := by
      by_contra hp2
      have hge : 3 ≤ d.p := by omega
      have ha' : ¬ d.a < 4 := by omega
      unfold advance at he
      simp [h1,ha',hge] at he
    exact Or.inr (Or.inr ⟨h1,hp2⟩)
  have hzero : d.a % 3 = 0 := by omega
  exact Or.inl hzero

#print axioms normalize_p2_exit

#print axioms advance_pmod
#print axioms normalize_pmod
#print axioms normalize_amin
#print axioms normalize_terminal
#print axioms normalize_safe_exit

end BB6.Agent2PacketSafe
