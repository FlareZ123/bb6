import I5D3Eleven
import PacketNormalizeSource
import Lean.Elab.Tactic.Omega

set_option maxRecDepth 180000
set_option maxHeartbeats 0

namespace BB6.Agent35I5Twelve
open CryptidBoundary
open BB6.BoundaryPadding
open BB6.Agent19.Physical
open BB6.Agent35I5Continuation
open BB6.Agent35I5Seven
open BB6.Agent35I5Eleven
open BB6.Agent31PacketRank
open BB6.Agent2PacketNormalizeSource

/-- From the authentic D3 root's eleventh pure-unary reentry,
    1771 more regular returns reach an E/E packet with q=8. -/
def raw12 : Option DRegular.L := BB6.DRegularFast.fastRun 1771 s11
def t12 : Nat := ((raw12.getD (⟨0,0,0⟩ : DRegular.L)).a-7)/9
def e12 : DRegular.L := ⟨9*t12+7,8,1⟩
theorem raw12_data : raw12 = some e12 := by decide
def regCost12 : Nat := DRegular.accumulated 1771 s11

private theorem reg12_obs :
    ObsEq (run regCost12 (DRegularSource.sourceSection s11))
      (DRegularSource.sourceSection e12) := by
  have hc : DRegular.Canon s11 := by
    constructor
    · simp [s11,q5FourthOut,q5FourthA] <;> omega
    · simp [s11,q5FourthOut]
  exact regular_source 1771 s11 e12 hc raw12_data

/-- Rank-decreasing packet normalizer: its 8 literal B/E source events
    stop at A(q=6,p=1), not at the exceptional E,p=2 reset. -/
def c12 : BB6.Agent31PacketRank.Packet := ⟨64*t12+33,2,13⟩
def d12 : BB6.Agent31PacketRank.Packet :=
  (BB6.Agent31PacketRank.normalizeWithCount c12).2
def k12 : Nat := (d12.a-3)/3
def s12 : DRegular.L := ⟨8*k12+41,0,0⟩

theorem normalized_terminal12 :
    d12.a = 3*k12+3 ∧ d12.q=6 ∧ d12.p=1 := by decide

/-- The original six-state source machine, not just its model, follows
    the exact E/E source entry, the well-founded B/E packet sequence,
    and the A-unary final return to a normal source section.
    Time is existential because the source normalizer supplies a
    proof-carrying finite duration instead of an evaluated polynomial. -/
theorem exceptional12_source :
    ∃ cost : Nat, ObsEq
      (run cost (DRegularSource.sourceSection e12))
      (DRegularSource.sourceSection s12) := by
  have hamin : c12.a ≥ 4 := by
    dsimp [c12]
    omega
  obtain ⟨packetCost,hN⟩ :=
    BB6.Agent2PacketNormalizeSource.normalized_original_source
      c12 hamin ys
  change run packetCost
    (BB6.Agent31PacketSource.packet c12.a c12.q c12.p ys) =
    (BB6.Agent31PacketSource.packet d12.a d12.q d12.p ys) at hN
  have hshape := normalized_terminal12
  have hn :
      ObsEq
        (run packetCost
          (BB6.Agent31PacketSource.packet (64*t12+33) 2 13 ys))
        (BB6.Agent31PacketSource.packet (3*k12+3) 6 1 ys) := by
    have ha : c12.a = 64*t12+33 := rfl
    have hq : c12.q=2 := rfl
    have hp : c12.p=13 := rfl
    rw [ha,hq,hp,hshape.1,hshape.2.1,hshape.2.2] at hN
    rw [hN]
    exact BB6.Padding.cfgEq_refl _
  have hfirst := two_return_packet t12 5
  have hA :
      ObsEq
        (run (BB6.Agent35APacketUnary.duration k12 6 0)
          (BB6.Agent31PacketSource.packet (3*k12+3) 6 1 ys))
        (DRegularSource.sourceSection s12) := by
    have hout : 8*k12+29+2*6+8*0=8*k12+41 := by omega
    simpa only [s12,hout] using (a_packet_unary_obs k12 6 0)
  let twoTime := BB6.Agent31SecondSource.firstCost t12 5 +
    BB6.Agent31SecondSource.secondCost t12
  let aTime := BB6.Agent35APacketUnary.duration k12 6 0
  have h01 := source_chain twoTime packetCost
    (DRegularSource.sourceSection e12)
    (BB6.Agent31PacketSource.packet (64*t12+33) 2 13 ys)
    (BB6.Agent31PacketSource.packet (3*k12+3) 6 1 ys)
    hfirst hn
  have h02 := source_chain (twoTime+packetCost) aTime
    (DRegularSource.sourceSection e12)
    (BB6.Agent31PacketSource.packet (3*k12+3) 6 1 ys)
    (DRegularSource.sourceSection s12)
    h01 hA
  exact ⟨twoTime+packetCost+aTime,h02⟩

/-- Full authentic blank-root original-machine source composition through
    episode twelve. In particular the source clock is no smaller than
    the already certified eleven-episode clock. -/
theorem root_twelve_source :
    ∃ (elapsed : Nat), sourceElapsedEleven ≤ elapsed ∧
      ObsEq (run elapsed (sourceUnary 5))
        (DRegularSource.sourceSection s12) := by
  obtain ⟨packetCost,hE⟩ := exceptional12_source
  have hR := source_chain sourceElapsedEleven regCost12
    (sourceUnary 5)
    (DRegularSource.sourceSection s11)
    (DRegularSource.sourceSection e12)
    root_source_eleven reg12_obs
  have hFull := source_chain
    (sourceElapsedEleven+regCost12) packetCost
    (sourceUnary 5)
    (DRegularSource.sourceSection e12)
    (DRegularSource.sourceSection s12)
    hR hE
  exact ⟨sourceElapsedEleven+regCost12+packetCost, by omega, hFull⟩

/-- Authentic parsed blank D3 remains physically unfrozen through some
    explicit finite source duration beyond the 11th exception. -/
theorem parsed_D3_no_halt_through_twelve :
    ∃ elapsed : Nat, sourceElapsedEleven ≤ elapsed ∧
      ∀ n : Nat, n ≤ 15+elapsed →
        ¬ BB6.Portfolio.haltsAt
          (BB6.Portfolio.parseRLE BB6.Portfolio.rleD3)
          (0 : BB6.Portfolio.State) n := by
  obtain ⟨elapsed,hold,hRoot⟩ := root_twelve_source
  have hObs := source_congr 1 hRoot
  have hstate := obs_state hObs
  have hrun :
      run (elapsed+1) (sourceUnary 5) =
        run 1 (run elapsed (sourceUnary 5)) := by
    exact CryptidBoundary.run_add _ _ _
  have hRight :
      (run 1 (DRegularSource.sourceSection s12)).st ≠ 6 := by
    simp [CryptidBoundary.run,CryptidBoundary.step,
      DRegularSource.sourceSection,CryptidBoundary.init,goL,s12]
  have hLive : (run (elapsed+1) (sourceUnary 5)).st ≠ 6 := by
    rw [hrun]
    intro hbad
    exact hRight (hstate.symm.trans hbad)
  have hAll (k : Nat) (hk : k ≤ elapsed+1) :
      (run k (sourceUnary 5)).st ≠ 6 :=
    no_frozen_before_live_endpoint
      (sourceUnary 5) (elapsed+1) k hk hLive
  refine ⟨elapsed,hold,?_⟩
  intro n hn
  by_cases hlt : n < 15
  · intro hh
    have hh' : BB6.Portfolio.haltsAt BB6.Portfolio.D3
        (0 : BB6.Portfolio.State) n := by
      simpa only [BB6.Portfolio.parsed_D3_eq] using hh
    have hd0 := BB6.Portfolio.D3_exact_halt_time n
    have hp := BB6.Portfolio.no_halt_before_prefix
      BB6.Portfolio.D0 (BB6.Portfolio.blank (1 : BB6.Portfolio.State))
      (BB6.Portfolio.F0Pure 5 (-3)) 15 n
      BB6.Portfolio.blank_root_B_to_I5 (hd0.mp hh')
    omega
  · have hge : 15 ≤ n := by omega
    let k := n-15
    have hk : k ≤ elapsed := by
      dsimp [k] at *
      omega
    have htime : 15+k=n := by omega
    intro hh
    have hh' : BB6.Portfolio.haltsAt
        (BB6.Portfolio.parseRLE BB6.Portfolio.rleD3)
        (0 : BB6.Portfolio.State) (15+k) := by
      simpa [htime] using hh
    have hfrozen :=
      (BB6.Agent19.Physical.parsed_D3_exact_source_time k).mp hh'
    exact (hAll (k+1) (by omega)) hfrozen.2

#print axioms raw12_data
#print axioms normalized_terminal12
#print axioms exceptional12_source
#print axioms root_twelve_source
#print axioms parsed_D3_no_halt_through_twelve

end BB6.Agent35I5Twelve
