import SourceRawHalt86
import BB429ForcedNormalize

namespace BB429SourceForcedNormalize
open BusyBeaver.M_1RB0LF_1RC1RA_0RD0RB_1LEHHH_0LA1LE_1RD1LA

/-- Computable original-source all-time blank-root nonreachability test. -/
theorem source_forcedExcluded_sound (a b : Nat)
    (h : BB429ForcedNormalize.forcedExcluded a b = true) :
    ∀ n, BB429SourceLadder.sourceRun n highLevelStart ≠ some (.J a b) := by
  intro n hn
  have hl : BB429.run n (0,0)=some (a,b) :=
    BB429SourceMod16.source_run_to_local n a b hn
  exact (BB429ForcedNormalize.forcedExcluded_sound a b h n) hl


/-- Exact reachability, transported to the unchanged Cryptids high-level
    blank-root source: normalizing an arbitrary finite state preserves
    existential orbit reachability in both directions. -/
theorem source_blank_reach_iff_normalized (a b : Nat) :
    (∃ n, BB429SourceLadder.sourceRun n highLevelStart =
      some (.J a b)) ↔
    (∃ n, BB429SourceLadder.sourceRun n highLevelStart =
      some (.J (BB429ForcedNormalize.forcedNormalize a b).1
                (BB429ForcedNormalize.forcedNormalize a b).2)) := by
  have hlocal := BB429ForcedNormalize.blank_reach_iff_normalized a b
  constructor
  · rintro ⟨n,hn⟩
    have hl : BB429.run n (0,0)=some (a,b) :=
      BB429SourceMod16.source_run_to_local n a b hn
    obtain ⟨k,hk⟩ := hlocal.mp ⟨n,hl⟩
    refine ⟨k,?_⟩
    have hb := BB429SourceLadder.source_run_eq k (0,0)
    simpa [BB429SourceLadder.lift, highLevelStart, hk] using hb
  · rintro ⟨n,hn⟩
    have hl : BB429.run n (0,0)=
        some (BB429ForcedNormalize.forcedNormalize a b) :=
      BB429SourceMod16.source_run_to_local n
        (BB429ForcedNormalize.forcedNormalize a b).1
        (BB429ForcedNormalize.forcedNormalize a b).2 hn
    obtain ⟨k,hk⟩ := hlocal.mpr ⟨n,hl⟩
    refine ⟨k,?_⟩
    have hb := BB429SourceLadder.source_run_eq k (0,0)
    simpa [BB429SourceLadder.lift, highLevelStart, hk] using hb


/-- Complete original-source indexed reachability criterion, with an exact
    forced inverse macro-time shift and a proof that no earlier target
    occurrence can precede the forced depth. This counts high-level
    accelerated transitions, not raw head movements. -/
theorem source_blank_run_iff_normalized_exact (a b n : Nat) :
    BB429SourceLadder.sourceRun n highLevelStart=some (.J a b) ↔
    BB429ForcedNormalize.forcedDepth a b ≤ n ∧
      BB429SourceLadder.sourceRun
        (n-BB429ForcedNormalize.forcedDepth a b) highLevelStart =
          some (.J (BB429ForcedNormalize.forcedNormalize a b).1
                    (BB429ForcedNormalize.forcedNormalize a b).2) := by
  constructor
  · intro hr
    have hl : BB429.run n (0,0)=some (a,b) :=
      BB429SourceMod16.source_run_to_local n a b hr
    obtain ⟨hle,hnorm⟩ :=
      (BB429ForcedNormalize.blank_run_iff_normalized_exact a b n).mp hl
    refine ⟨hle,?_⟩
    have hs := BB429SourceLadder.source_run_eq
      (n-BB429ForcedNormalize.forcedDepth a b) (0,0)
    simpa [BB429SourceLadder.lift,highLevelStart,hnorm] using hs
  · rintro ⟨hle,hnorm⟩
    have hl : BB429.run
        (n-BB429ForcedNormalize.forcedDepth a b) (0,0) =
          some (BB429ForcedNormalize.forcedNormalize a b) :=
      BB429SourceMod16.source_run_to_local
        (n-BB429ForcedNormalize.forcedDepth a b)
        (BB429ForcedNormalize.forcedNormalize a b).1
        (BB429ForcedNormalize.forcedNormalize a b).2 hnorm
    have he : BB429.run n (0,0)=some (a,b) :=
      (BB429ForcedNormalize.blank_run_iff_normalized_exact a b n).mpr
        ⟨hle,hl⟩
    have hs := BB429SourceLadder.source_run_eq n (0,0)
    simpa [BB429SourceLadder.lift,highLevelStart,he] using hs

#print axioms source_blank_run_iff_normalized_exact

#print axioms source_blank_reach_iff_normalized

#print axioms source_forcedExcluded_sound
end BB429SourceForcedNormalize
