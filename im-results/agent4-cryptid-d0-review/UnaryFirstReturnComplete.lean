import Lean.Elab.Tactic.Omega
import AZeroOneFirstReturn
import ELowCanonicalBlankFirst
import BFirstReturn

/-!
# All canonical pure-unary D0 sections have exact first physical returns

A source-compositional theorem across all three residues a mod 3.
The final state and return duration are inherited from original-source
A/B/E endpoint theorems. The new content is universal exclusion of
earlier F/0 configurations with TapeEq-empty physical left half-tape,
including all implicit-blank cases.  These are exact source statements,
not a proof that any particular blank-root orbit remains in this family.
-/

set_option maxHeartbeats 10000000
set_option maxRecDepth 4096
set_option linter.unusedSimpArgs false

namespace BB6.Agent4UnaryFirstReturnComplete

open CryptidBoundary
open BB6.BoundaryPadding
open BB6.CryptidPrefixFirstReturn
open BB6.CryptidFirstReturn
open BB6.CryptidELowCanonicalFirst

private theorem b_unary_noF (k t : Nat)
    (htpos : 0<t) (ht : t<12*k*k+49*k+40) :
    (run t (init (List.replicate (3*k) true))).st ≠ 5 := by
  let xs := List.replicate (3*k) true
  have hpad := (BB6.BoundaryPadding.source_init_pad t 1 xs).2.2.2
  change (run t (init xs)).st =
    (run t (init (xs ++ [false]))).st at hpad
  rw [hpad]
  have hend : run (12*k*k+41*k+31)
      (BB6.CryptidBFirstReturn.bStart k []) =
      sweepB (4*k+3) [] := by
    change run (12*k*k+41*k+31)
      (init (List.replicate (3*k) true ++ false::[])) = _
    rw [prefix_B]
    rfl
  change (run t (BB6.CryptidBFirstReturn.bStart k [])).st ≠ 5
  by_cases hsmall : t<12*k*k+41*k+31
  · exact prefixB_positive_noF k [] t htpos hsmall
  · have htstep : t=(12*k*k+41*k+31)+
        (t-(12*k*k+41*k+31)) := by omega
    rw [htstep,run_add,hend]
    exact sweepB_firstF (4*k+3) []
      (t-(12*k*k+41*k+31)) (by omega)

/-- All canonical (q=b=0) pure-unary source sections, for any a>=2:
at their modeled next-state time they are observationally equivalent to
the original six-state machine section and **no strictly earlier positive
time is a physically blank-left F/0 return**.

The source section grammar covers A, B, and E residues uniformly. -/
theorem unary_source_first_return (a : Nat) (ha : 2 ≤ a) :
    ∃ out : DRegular.L,
      DRegular.next ⟨a,0,0⟩ = some out ∧
      ObsEq
        (run (DRegular.duration ⟨a,0,0⟩)
          (DRegularSource.sourceSection ⟨a,0,0⟩))
        (DRegularSource.sourceSection out) ∧
      ∀ t, 0<t → t<DRegular.duration ⟨a,0,0⟩ →
        ¬BlankLeftF
          (run t (DRegularSource.sourceSection ⟨a,0,0⟩)) := by
  have hmod : a%3=0 ∨ a%3=1 ∨ a%3=2 := by omega
  rcases hmod with hA | hE | hB
  · let k := a/3-1
    have hnum : a=3*k+3 := by
      dsimp [k]
      omega
    have h2 : (3*k+3)%3=0 := by omega
    have hd : (3*k+3)/3-1=k := by omega
    have htime : DRegular.duration ⟨3*k+3,0,0⟩ =
        12*k*k+49*k+44 := by
      simp [DRegular.duration,h2,hd]
    have hstart : DRegularSource.sourceSection ⟨3*k+3,0,0⟩ =
        init (List.replicate (3*k+1) true) := by
      have hn : (3*k+3)-2=3*k+1 := by omega
      simp [DRegularSource.sourceSection,hn,oppairs]
    refine ⟨⟨8*k+11,0,0⟩, ?_, ?_, ?_⟩
    · rw [hnum]
      simp [DRegular.next,h2,hd]
    · rw [hnum]
      simpa [htime] using (BB6.AZeroSource.a_zero_model k)
    · intro t htpos ht hblank
      rw [hnum,htime] at ht
      rw [hnum,hstart] at hblank
      exact (BB6.CryptidARegularFirstReturn.full_A_zero_first_return
        k t htpos ht) hblank.1
  · let k := a/3-1
    have hnum : a=3*k+4 := by
      dsimp [k]
      omega
    have h2 : (3*k+4)%3=1 := by omega
    have hd : (3*k+4)/3-1=k := by omega
    have htime : DRegular.duration ⟨3*k+4,0,0⟩ =
        12*k*k+49*k+50 := by
      simp [DRegular.duration,h2,hd]
    have hstart : DRegularSource.sourceSection ⟨3*k+4,0,0⟩ =
        init (List.replicate (3*k+2) true) := by
      have hn : (3*k+4)-2=3*k+2 := by omega
      simp [DRegularSource.sourceSection,hn,oppairs]
    refine ⟨⟨8*k+5,1,5⟩, ?_, ?_, ?_⟩
    · rw [hnum]
      simp [DRegular.next,h2,hd]
    · rw [hnum]
      simpa [htime] using (BB6.EZeroSource.e_zero_model k)
    · intro t htpos ht hblank
      rw [hnum,htime] at ht
      rw [hnum,hstart] at hblank
      have hnoblank :=
        (canonical_E_low_no_early_blank k 0) t htpos
          (by simpa using ht)
      exact hnoblank (by simpa [oppairs] using hblank)
  · let k := a/3
    have hnum : a=3*k+2 := by
      dsimp [k]
      omega
    have h2 : (3*k+2)%3=2 := by omega
    have hd : (3*k+2)/3=k := by omega
    have htime : DRegular.duration ⟨3*k+2,0,0⟩ =
        12*k*k+49*k+40 := by
      simp [DRegular.duration,h2,hd]
    have hstart : DRegularSource.sourceSection ⟨3*k+2,0,0⟩ =
        init (List.replicate (3*k) true) := by
      have hn : (3*k+2)-2=3*k := by omega
      simp [DRegularSource.sourceSection,hn,oppairs]
    refine ⟨⟨8*k+9,0,0⟩, ?_, ?_, ?_⟩
    · rw [hnum]
      simp [DRegular.next,h2,hd]
    · rw [hnum]
      exact BB6.BRegularSource.original_B_row
        ⟨3*k+2,0,0⟩ ⟨8*k+9,0,0⟩
        (by simp [DRegular.Canon])
        (by omega)
        (by simp [DRegular.next,h2,hd])
    · intro t htpos ht hblank
      rw [hnum,htime] at ht
      rw [hnum,hstart] at hblank
      exact (b_unary_noF k t htpos ht) hblank.1

#print axioms b_unary_noF
#print axioms unary_source_first_return
end BB6.Agent4UnaryFirstReturnComplete
