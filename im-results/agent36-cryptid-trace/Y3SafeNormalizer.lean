import Lean.Elab.Tactic.Omega
import PacketNormalizeSource
import MarkerTowerSource
import MarkerOneSource

/-!
A decidable source-sound sufficient criterion for arbitrary Y3 marker packets.

The rank-decreasing B/E normalizer is already certified on the original
six-state D machine.  A marker packet at its endpoint is closed whenever
it is an A terminal, exhausted B terminal, E/p=1 regular terminal, or
E/p=0 with q divisible by three.  The last case is not included in the
older Y3 terminal classifier: it consumes a marker level and returns
through the source-certified Y_(m+1) E/p0 theorem.

This is an actual-source infinite-parametric decision method, not an
invariant for the authentic blank-tape trajectory.
-/

namespace BB6.Agent36Y3Safe

open CryptidBoundary BB6.Agent31PacketSource
open BB6.Agent31PacketRank BB6.Agent2PacketNormalizeSource
open BB6.BoundaryPadding

set_option maxHeartbeats 12000000
set_option maxRecDepth 8192

/-- Sufficient source-safe exits of the original Y3=(01)^3 11 marker. -/
def terminalY3 (d : Packet) : Prop :=
  (d.a % 3 = 0) ∨
  (d.a % 3 = 2 ∧ d.q = 0) ∨
  (d.a % 3 = 1 ∧
    (d.p = 1 ∨ (d.p = 0 ∧ d.q % 3 = 0)))

theorem terminalY3_source (d : Packet) (ha : d.a ≥ 4)
    (hs : terminalY3 d) :
    ∃ T a q b,
      ObsEq (run T
        (packet d.a d.q d.p BB6.Agent2PacketP2Reset.marker))
        (BB6.Agent2BoundaryBZero.regularSection a q b) := by
  rcases hs with hA | hB | hE
  · let k : Nat := (d.a-3)/3
    have hk : d.a = 3*k+3 := by dsimp [k]; omega
    rw [hk]
    exact BB6.Agent35MarkerOne.a_marker_regular k d.q d.p
  · obtain ⟨hB,hq⟩ := hB
    let k : Nat := (d.a-2)/3
    have hk : d.a = 3*k+2 := by dsimp [k]; omega
    refine ⟨12*k*k+49*k+40,8*k+9+d.p,3,2,?_⟩
    rw [hk,hq]
    have hm : BB6.Agent2PacketP2Reset.marker = BB6.Agent35MarkerOne.marker := by rfl
    rw [hm,BB6.Agent35MarkerOne.b_zero_regular]
    exact BB6.Padding.cfgEq_refl _
  · obtain ⟨hE,hrest⟩ := hE
    rcases hrest with hp1 | ⟨hp0,hq0⟩
    · refine ⟨0,d.a,d.q+4,2,?_⟩
      change ObsEq (packet d.a d.q d.p BB6.Agent2PacketP2Reset.marker)
        (BB6.Agent2BoundaryBZero.regularSection d.a (d.q+4) 2)
      rw [hp1]
      have hm : BB6.Agent2PacketP2Reset.marker = BB6.Agent35MarkerOne.marker := by rfl
      rw [hm,BB6.Agent35MarkerOne.e_one_regular]
      exact BB6.Padding.cfgEq_refl _
    · let k : Nat := (d.a-4)/3
      let u : Nat := d.q/3
      have hk : d.a = 3*k+4 := by dsimp [k]; omega
      have hq : d.q = 3*u := by dsimp [u]; omega
      obtain ⟨T,a,q,b,h⟩ :=
        BB6.Agent2MarkerTower.e_zero_q0_regular k u 2
      refine ⟨T,a,q,b,?_⟩
      rw [hk,hq,hp0]
      have hm : BB6.Agent2PacketP2Reset.marker =
          BB6.Agent2MarkerTower.marker 3 := by decide
      rw [hm]
      exact h

/-- Decidable-by-normalization success condition for the exceptional Y3
    packet: nothing is assumed about the source's blank reachability. -/
def safeY3 (c : Packet) : Prop :=
  terminalY3 ((normalizeWithCount c).2)

/-- Every packet accepted by safeY3 returns on the literal original
    six-state machine, with exact source guards and physical tape semantics. -/
theorem safeY3_source (c : Packet) (ha : c.a ≥ 4)
    (hs : safeY3 c) :
    ∃ T a q b,
      ObsEq (run T
        (packet c.a c.q c.p BB6.Agent2PacketP2Reset.marker))
        (BB6.Agent2BoundaryBZero.regularSection a q b) := by
  let d : Packet := (normalizeWithCount c).2
  have hd : d.a ≥ 4 := BB6.Agent2PacketSafe.normalize_amin c ha
  obtain ⟨T,ht⟩ := normalized_original_source c ha
    BB6.Agent2PacketP2Reset.marker
  obtain ⟨Ttail,a,q,b,hreg⟩ := terminalY3_source d hd hs
  refine ⟨T+Ttail,a,q,b,?_⟩
  change run T (packet c.a c.q c.p BB6.Agent2PacketP2Reset.marker) =
    packet d.a d.q d.p BB6.Agent2PacketP2Reset.marker at ht
  rw [run_add,ht]
  exact hreg

/-- This criterion applies directly after the universally source-certified
    E,p=2 reset from the *fixed original suffix* 0 1^6. -/
theorem p2_fixed_safe (k Q : Nat)
    (hs : safeY3 ⟨8*k+5,0,2*Q+6⟩) :
    ∃ T a q b,
      ObsEq
        (run T
          (packet (3*k+4) Q 2 (false::List.replicate 6 true)))
        (BB6.Agent2BoundaryBZero.regularSection a q b) := by
  obtain ⟨T,a,q,b,hreg⟩ :=
    safeY3_source ⟨8*k+5,0,2*Q+6⟩
      (by change 8*k+5 ≥ 4; omega) hs
  refine ⟨BB6.Agent2PacketP2Reset.eTwoTime k Q+T,a,q,b,?_⟩
  rw [run_add,BB6.Agent2PacketP2Reset.e_two_reset]
  exact hreg

#print axioms terminalY3_source
#print axioms safeY3_source
#print axioms p2_fixed_safe
end BB6.Agent36Y3Safe
