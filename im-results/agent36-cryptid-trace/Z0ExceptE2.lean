import Lean.Elab.Tactic.Omega
import AZ0P2
import ZSafeNormalizer

namespace BB6.Agent36Z0ExceptE2
open CryptidBoundary BB6.Agent31PacketSource BB6.Agent31PacketRank
open BB6.Agent2PacketNormalizeSource BB6.Agent2BoundaryBZero
open BB6.Agent2MarkerZero BB6.Agent36ZSafeNormalizer
open BB6.Agent36EZeroZ BB6.BoundaryPadding

set_option maxHeartbeats 10000000
set_option maxRecDepth 8192

/-- The entire depth-zero Z packet grammar has a source-certified
    regular return except when guarded B/E normalization ends precisely
    at the exceptional E/p=2 shape. This is an exhaustive terminal
    classification for arbitrary q and arbitrarily long B/E phases. -/
theorem all_Z0_except_E2 (c : Packet) (ha : c.a ≥ 4)
    (hn : let d := (normalizeWithCount c).2
      ¬ (d.a % 3 = 1 ∧ d.p = 2)) :
    ∃ T a q b,
      ObsEq
        (run T (packet c.a c.q c.p (BB6.Agent2MarkerZero.marker 0)))
        (regularSection a q b) := by
  let d : Packet := (normalizeWithCount c).2
  have hd : d.a ≥ 4 :=
    BB6.Agent2PacketSafe.normalize_amin c ha
  have hnone : advance d = none :=
    BB6.Agent2PacketSafe.normalize_terminal c
  have hno : ¬ (d.a % 3 = 1 ∧ d.p = 2) := hn
  obtain ⟨Tp,hraw⟩ :=
    normalized_original_source c ha (BB6.Agent2MarkerZero.marker 0)
  change run Tp (packet c.a c.q c.p
    (BB6.Agent2MarkerZero.marker 0)) =
      packet d.a d.q d.p (BB6.Agent2MarkerZero.marker 0) at hraw
  have hterm :
      ∃ Te a q b,
        ObsEq
          (run Te (packet d.a d.q d.p (BB6.Agent2MarkerZero.marker 0)))
          (regularSection a q b) := by
    by_cases hA : d.a % 3 = 0
    · by_cases hp2 : d.p % 3 = 2
      · let k : Nat := (d.a-3)/3
        let r : Nat := (d.p-2)/3
        have hka : d.a = 3*k+3 := by dsimp [k]; omega
        have hpr : d.p = 3*r+2 := by dsimp [r]; omega
        refine ⟨BB6.Agent36AZ0P2.twoCost k d.q r,
          BB6.Agent36AZ0P2.twoUnary k d.q r,1,5,?_⟩
        rw [hka,hpr]
        exact BB6.Agent36AZ0P2.a_two_z0_regular k d.q r
      · have hg : terminalSafe d := by
          have hmod : d.p%3=0 ∨ d.p%3=1 := by omega
          rcases hmod with hp0 | hp1
          · exact Or.inr (Or.inl ⟨hA,hp0⟩)
          · exact Or.inl hp1
        exact terminalSafe_source 0 d hd hg
    · by_cases hB : d.a % 3 = 2
      · have hq : d.q=0 := by
          by_contra hq
          simp [advance,hB,hq] at hnone
        exact terminalSafe_source 0 d hd
          (Or.inr (Or.inr ⟨hB,hq⟩))
      · have hE : d.a % 3 = 1 := by omega
        have hp_lt : d.p < 3 := by
          by_contra hge
          have hneB : d.a % 3 ≠ 2 := by omega
          have hmin : ¬ d.a < 4 := by omega
          have hpge : ¬ d.p < 3 := by omega
          simp [advance,hneB,hE,hmin,hpge] at hnone
        have hp0or1 : d.p=0 ∨ d.p=1 := by
          have hpne : d.p≠2 := by
            intro h2
            exact hno ⟨hE,h2⟩
          omega
        rcases hp0or1 with hp0 | hp1
        · let ke : Nat := (d.a-4)/3
          have heq : d.a=3*ke+4 := by dsimp [ke]; omega
          refine ⟨12*ke*ke+49*ke+50+4*d.q,
            8*ke+5,1,2*d.q+5,?_⟩
          rw [heq,hp0]
          exact e_zero_Z0_regular ke d.q
        · exact terminalSafe_source 0 d hd
            (Or.inl (by omega))
  obtain ⟨Te,a,q,b,hterminal⟩ := hterm
  refine ⟨Tp+Te,a,q,b,?_⟩
  rw [run_add,hraw]
  exact hterminal

#print axioms all_Z0_except_E2
end BB6.Agent36Z0ExceptE2
