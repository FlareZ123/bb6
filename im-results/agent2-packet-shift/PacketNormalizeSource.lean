import Lean.Elab.Tactic.Omega
import PacketRank
import PacketPaths
import PacketSafeExit

namespace BB6.Agent2PacketNormalizeSource

open BB6.Agent31PacketRank BB6.Agent31PacketPaths

def toState (c : Packet) : State := ⟨c.a,c.q,c.p⟩

/-- Every accepted abstract guard is an exact source-connected B/E edge. -/
theorem advance_edge {c d : Packet}
    (h : advance c = some d) (_ha : c.a ≥ 4) :
    ∃ T, Edge (toState c) T (toState d) := by
  unfold advance at h
  split at h
  · split at h
    · contradiction
    · injection h with hd
      subst d
      let k : Nat := (c.a-2)/3
      have hn : c.a = 3*k+2 := by
        dsimp [k]
        omega
      have hp : c.q = (c.q-1)+1 := by omega
      refine ⟨12*k*k+49*k+40, ?_⟩
      simpa only [toState,←hn,←hp] using
        (Edge.b k (c.q-1) c.p)
  · split at h
    · split at h
      · contradiction
      · injection h with hd
        subst d
        let k : Nat := (c.a-4)/3
        have hn : c.a = 3*k+4 := by
          dsimp [k]
          omega
        have hpb : c.p = (c.p-3)+3 := by omega
        refine ⟨12*k*k+49*k+58+6*c.q, ?_⟩
        simpa only [toState,←hn,←hpb] using
          (Edge.e k c.q (c.p-3))
    · contradiction

/-- The all-parameter well-founded abstract normalizer has a real exact
    source path; this bridges the previously separate rank/path artifacts. -/
theorem normalized_path (c : Packet) (ha : c.a ≥ 4) :
    ∃ T, Path (toState c) (normalizeWithCount c).1
      T (toState (normalizeWithCount c).2) := by
  rw [normalizeWithCount]
  split
  · exact ⟨0, Path.nil (toState c)⟩
  · rename_i d h
    obtain ⟨edgeCost,hedge⟩ := advance_edge h ha
    have hd := BB6.Agent2PacketSafe.advance_amin h ha
    obtain ⟨restCost,hpath⟩ := normalized_path d hd
    cases hrec : normalizeWithCount d with
    | mk n e =>
      refine ⟨edgeCost+restCost, ?_⟩
      exact Path.cons hedge (by simpa [hrec] using hpath)
termination_by rank c
decreasing_by
  rename_i _ih d _h1 _h2 heq
  have hs := advance_rank heq
  omega

/-- Exact original six-state-machine guarded-phase source equality,
    including every arbitrary binary tail and all primitive runtime costs. -/
theorem normalized_original_source (c : Packet) (ha : c.a ≥ 4)
    (ys : List Bool) :
    ∃ T,
      CryptidBoundary.run T
        (physical (toState c) ys) =
      physical (toState (normalizeWithCount c).2) ys := by
  obtain ⟨T,hpath⟩ := normalized_path c ha
  exact ⟨T, path_sound hpath ys⟩

/-- The literal source machine reaches a safe *packet boundary* whenever
    the initial p residue excludes two. This does not yet compose the
    final A/B/E exit macro or claim genuine blank-tape nonhalting. -/
theorem normalized_source_safe_boundary (c : Packet) (ha : c.a ≥ 4)
    (hp : c.p % 3 ≠ 2) (ys : List Bool) :
    let d := (normalizeWithCount c).2
    ∃ T, CryptidBoundary.run T (physical (toState c) ys) =
      physical (toState d) ys ∧
      (d.a % 3 = 0 ∨ (d.a % 3 = 2 ∧ d.q = 0) ∨
        (d.a % 3 = 1 ∧ (d.p = 0 ∨ d.p = 1))) := by
  obtain ⟨T,ht⟩ := normalized_original_source c ha ys
  exact ⟨T,ht,BB6.Agent2PacketSafe.normalize_safe_exit c ha hp⟩

#print axioms advance_edge
#print axioms normalized_path
#print axioms normalized_original_source
#print axioms normalized_source_safe_boundary

end BB6.Agent2PacketNormalizeSource
