import Lean.Elab.Tactic.Omega
import EChainDoubleBExit
import DObsSourceCandidate
import P2MarkerA

set_option maxHeartbeats 100000000
set_option maxRecDepth 55000

namespace BB6.Agent37EChainDoubleBReentry

open CryptidBoundary BB6.Padding BB6.BoundaryPadding
open BB6.Agent31PacketSource BB6.Agent35K4Shapes
open BB6.Agent37EChainAExit BB6.Agent37EChainBExit

def endpointZero (n : Nat) : CryptidBoundary.Cfg :=
  ⟨[],false,
    List.replicate n true ++
      [true,false,true,false,true,true,true],5⟩

def endpointOne (n : Nat) : CryptidBoundary.Cfg :=
  ⟨[],false,List.replicate n true,5⟩

def endpointTwo (n : Nat) : CryptidBoundary.Cfg :=
  ⟨[],false,
    List.replicate n true ++
      [false,true,false,true,false,true,false,true,false],5⟩


private theorem regularSection_sourceSection (a q b : Nat) (ha : 2 ≤ a) :
    BB6.Agent2BoundaryBZero.regularSection a q b =
      DRegularSource.sourceSection ⟨a,q,b⟩ := by
  simp only [BB6.Agent2BoundaryBZero.regularSection,
    DRegularSource.sourceSection, CryptidBoundary.init]
  have hrepAdd (m n : Nat) :
      List.replicate (m+n) true =
        List.replicate m true ++ List.replicate n true := by
    induction m with
    | zero => simp
    | succ m ih =>
      rw [show Nat.succ m + n = (m+n)+1 by omega]
      rw [List.replicate_succ]
      rw [ih]
      rw [← List.cons_append]
      rw [← List.replicate_succ]
  have hrep : List.replicate a true =
      [true,true] ++ List.replicate (a-2) true := by
    rw [show a = 2+(a-2) by omega, hrepAdd]
    simp
  rw [hrep]
  simp [List.append_assoc]

/-- A regular endpoint together with a unary-prefix lower bound. -/
def regularEndpointFloor (c : CryptidBoundary.Cfg) (floor : Nat) : Prop :=
  ∃ (T n : Nat),
    (CryptidBoundary.run T c = endpointZero n ∨
      CryptidBoundary.run T c = endpointOne n ∨
      CryptidBoundary.run T c = endpointTwo n) ∧
    floor ≤ n

/-- Strengthen the marker-A closure with the explicit unary floor needed
    to enter the canonical DRegular source-section language. -/
theorem all_A_marker_returns_floor (ka q p : Nat) :
    ∃ (T n : Nat),
      (CryptidBoundary.run T
        (BB6.Agent31PacketSource.packet (3*ka+3) q p
          BB6.Agent35K4Shapes.marker) = endpointZero n ∨
       CryptidBoundary.run T
        (BB6.Agent31PacketSource.packet (3*ka+3) q p
          BB6.Agent35K4Shapes.marker) = endpointOne n ∨
       CryptidBoundary.run T
        (BB6.Agent31PacketSource.packet (3*ka+3) q p
          BB6.Agent35K4Shapes.marker) = endpointTwo n) ∧
      2*(4*ka+3)+5 ≤ n := by
  let r := p/3
  have hcases : p = 3*r ∨ p = 3*r+1 ∨ p = 3*r+2 := by
    have hm := Nat.mod_add_div p 3
    dsimp [r]
    omega
  rcases hcases with h0 | h1 | h2
  · refine ⟨BB6.Agent35MarkerA.aTime0 ka q r,
      2*((4*ka+3)+CryptidA.wordInc
        (BB6.Agent35MarkerA.code q r))+5, Or.inl ?_, ?_⟩
    · rw [h0]
      exact BB6.Agent35MarkerA.close_zero ka q r
    · omega
  · refine ⟨BB6.Agent35MarkerA.aTime1 ka q r,
      2*((4*ka+3)+CryptidA.wordInc
        (BB6.Agent35MarkerA.tailCode q r))+5, Or.inr (Or.inl ?_), ?_⟩
    · rw [h1]
      exact BB6.Agent35MarkerA.close_one ka q r
    · omega
  · refine ⟨BB6.Agent35MarkerA.aTime2 ka q r,
      2*((4*ka+3)+CryptidA.wordInc
        (BB6.Agent35MarkerA.code q r))+5, Or.inr (Or.inr ?_), ?_⟩
    · rw [h2]
      exact BB6.Agent35MarkerA.close_two ka q r
    · omega

private theorem canon_nonzero_q (a q b : Nat)
    (ha : 2 ≤ a) (hq : q ≠ 0) : DRegular.Canon ⟨a,q,b⟩ := by
  constructor
  · exact ha
  · exact Or.inl hq

/-- Convert any floor-bounded A-marker endpoint to a canonical
    DRegularSource section, preserving the physical tape semantics. -/
theorem regularEndpointFloor_sourceSection
    (c : CryptidBoundary.Cfg) (floor : Nat) (hfloor : 2 ≤ floor)
    (h : regularEndpointFloor c floor) :
    ∃ (T a q b : Nat),
      ObsEq (CryptidBoundary.run T c)
        (DRegularSource.sourceSection ⟨a,q,b⟩) ∧
      DRegular.Canon ⟨a,q,b⟩ := by
  rcases h with ⟨T,n,hcases,hn⟩
  have hn2 : 2 ≤ n := le_trans hfloor hn
  have hrep : List.replicate (n+1) true =
      List.replicate n true ++ [true] := by
    rw [show n+1 = n+1 by rfl,
      ← List.replicate_append_replicate]
    rfl
  rcases hcases with h0 | h1 | h2
  · refine ⟨T,n+1,2,2,?_,?⟩
    have heq : endpointZero n =
        BB6.Agent2BoundaryBZero.regularSection (n+1) 2 2 := by
      simp [endpointZero,BB6.Agent2BoundaryBZero.regularSection,
        CryptidBoundary.oppairs,hrep,List.append_assoc]
    have hsec :=
      regularSection_sourceSection
        (n+1) 2 2 (by omega)
    rw [h0,heq,hsec]
    exact BB6.Padding.cfgEq_refl _
    exact canon_nonzero_q (n+1) 2 2 (by omega) (by decide)
  · refine ⟨T,n,0,0,?_,?⟩
    have heq : endpointOne n =
        BB6.Agent2BoundaryBZero.regularSection n 0 0 := by
      simp [endpointOne,BB6.Agent2BoundaryBZero.regularSection,
        CryptidBoundary.oppairs]
    have hsec :=
      BB6.Agent2TwentyThirdRoot.regularSection_sourceSection
        n 0 0 hn2
    rw [h1,heq,hsec]
    exact BB6.Padding.cfgEq_refl _
    constructor
    · exact hn2
    · right
      rfl
  · refine ⟨T,n,4,0,?_,?⟩
    have hreg : ObsEq endpointTwo
        (BB6.Agent2BoundaryBZero.regularSection n 4 0) := by
      change BB6.Padding.CfgEq
        (BB6.BoundaryPadding.represent endpointTwo)
        (BB6.BoundaryPadding.represent
          (BB6.Agent2BoundaryBZero.regularSection n 4 0))
      apply BB6.Padding.cfgEq_symm
      simp only [BB6.BoundaryPadding.represent,
        BB6.Agent2BoundaryBZero.regularSection,
        List.replicate_zero]
      have hword : CryptidBoundary.oppairs 4 =
          [false,true,false,true,false,true,false,true] := by decide
      rw [hword]
      refine ⟨BB6.Padding.tapeEq_refl _,rfl,?_,rfl⟩
      simpa [List.append_assoc] using
        (BB6.Padding.tapeEq_pad
          (List.replicate n true ++
            [false,true,false,true,false,true,false,true]) 1)
    have hsec :=
      BB6.Agent2TwentyThirdRoot.regularSection_sourceSection
        n 4 0 hn2
    rw [h2]
    rw [hsec] at hreg
    exact hreg
    exact canon_nonzero_q n 4 0 hn2 (by decide)

/-- Two consecutive B packets, with the second consuming the p+3 suffix
    produced by the first, followed by a source-certified A-marker return. -/
def bTwiceTime (t : Nat) : Nat :=
  BB6.Agent37EChainBExit.bTime (9*t+5) +
    BB6.Agent37EChainBExit.bTime (24*t+16)

theorem double_B_to_A_source_reentry (t q p : Nat) :
    ∃ (T a q' b : Nat),
      ObsEq
        (CryptidBoundary.run T
          (BB6.Agent31PacketSource.packet (27*t+17) (q+2) p
            BB6.Agent35K4Shapes.marker))
        (DRegularSource.sourceSection ⟨a,q',b⟩) ∧
      DRegular.Canon ⟨a,q',b⟩ := by
  let ka := 64*t+45
  obtain ⟨ta,n,hA,hn⟩ :=
    all_A_marker_returns_floor ka q (p+6)
  have hB :
      CryptidBoundary.run (bTwiceTime t)
        (BB6.Agent31PacketSource.packet (27*t+17) (q+2) p
          BB6.Agent35K4Shapes.marker) =
      BB6.Agent31PacketSource.packet (3*ka+3) q (p+6)
        BB6.Agent35K4Shapes.marker := by
    simpa [bTwiceTime,ka] using
      (BB6.Agent37EChainDoubleBExit.b_twice t q p
        BB6.Agent35K4Shapes.marker)
  have hfloor : regularEndpointFloor
      (BB6.Agent31PacketSource.packet (27*t+17) (q+2) p
        BB6.Agent35K4Shapes.marker)
      (2*(4*ka+3)+5) := by
    refine ⟨bTwiceTime t+ta,n,?_,hn⟩
    rw [CryptidBoundary.run_add,hB]
    exact hA
  exact regularEndpointFloor_sourceSection
    (BB6.Agent31PacketSource.packet (27*t+17) (q+2) p
      BB6.Agent35K4Shapes.marker)
    (2*(4*ka+3)+5) (by omega) hfloor

/-- An arbitrary E-chain ending in the double-B cylinder now returns
    directly to a canonical DRegularSource section. -/
theorem chain_double_B_to_A_source_reentry
    (d h t q p : Nat) (hh : 1 ≤ h) (hd : 1 ≤ d)
    (ha : 1+4*8^d*h = 27*t+17) :
    ∃ (T a q' b : Nat),
      ObsEq
        (CryptidBoundary.run T
          (BB6.Agent31PacketSource.packet
            (1+4*3^d*h) q (3*d+p) BB6.Agent35K4Shapes.marker))
        (DRegularSource.sourceSection ⟨a,q',b⟩) ∧
      DRegular.Canon ⟨a,q',b⟩ := by
  have hE := BB6.Agent37EChain.chain_return d h q p
    BB6.Agent35K4Shapes.marker hh
  rw [ha] at hE
  have hqq : (q+2*d-2)+2 = q+2*d := by omega
  obtain ⟨Ttail,a,q',b,hB,hcanon⟩ :=
    double_B_to_A_source_reentry t (q+2*d-2) p
  have hB' : ObsEq
      (CryptidBoundary.run Ttail
        (BB6.Agent31PacketSource.packet (27*t+17) (q+2*d) p
          BB6.Agent35K4Shapes.marker))
      (DRegularSource.sourceSection ⟨a,q',b⟩) := by
    simpa [hqq] using hB
  have hEobs : ObsEq
      (CryptidBoundary.run (BB6.Agent37EChain.chainTime d h q)
        (BB6.Agent31PacketSource.packet
          (1+4*3^d*h) q (3*d+p) BB6.Agent35K4Shapes.marker))
      (BB6.Agent31PacketSource.packet (27*t+17) (q+2*d) p
        BB6.Agent35K4Shapes.marker) := by
    rw [hE]
    exact BB6.Padding.cfgEq_refl _
  have hcombined := BB6.BoundaryPadding.source_chain
    (BB6.Agent37EChain.chainTime d h q) Ttail
    (BB6.Agent31PacketSource.packet
      (1+4*3^d*h) q (3*d+p) BB6.Agent35K4Shapes.marker)
    (BB6.Agent31PacketSource.packet (27*t+17) (q+2*d) p
      BB6.Agent35K4Shapes.marker)
    (DRegularSource.sourceSection ⟨a,q',b⟩)
    hEobs hB'
  exact ⟨BB6.Agent37EChain.chainTime d h q+Ttail,a,q',b,
    hcombined,hcanon⟩


/-- The P2 reset cylinder, arbitrary-depth E chain, two B packets, and
    marker-A closure now return directly to a canonical DRegular section. -/
theorem reset_double_B_to_A_source_reentry (d k h t Q : Nat)
    (hh : 1 ≤ h) (hd : 1 ≤ d)
    (hk : 2*k+1=3^d*h)
    (ha : 1+4*8^d*h=27*t+17)
    (hQ : 3*d ≤ 2*Q+6) :
    ∃ (T a q b : Nat),
      ObsEq
        (CryptidBoundary.run T
          (BB6.Agent31PacketSource.packet (3*k+4) Q 2
            (false::List.replicate 6 true)))
        (DRegularSource.sourceSection ⟨a,q,b⟩) ∧
      DRegular.Canon ⟨a,q,b⟩ := by
  have hp : 2*Q+6=3*d+(2*Q+6-3*d) := by omega
  have hprefix : 8*k+5=1+4*3^d*h := by
    calc
      8*k+5=4*(2*k+1)+1 := by omega
      _ = 4*(3^d*h)+1 := by rw [hk]
      _ = 1+4*3^d*h := by ac_rfl
  have hm : BB6.Agent2PacketP2Reset.marker =
      BB6.Agent35K4Shapes.marker := by decide
  have hreset :
      CryptidBoundary.run (BB6.Agent2PacketP2Reset.eTwoTime k Q)
        (BB6.Agent31PacketSource.packet (3*k+4) Q 2
          (false::List.replicate 6 true)) =
      BB6.Agent31PacketSource.packet (1+4*3^d*h) 0
        (3*d+(2*Q+6-3*d)) BB6.Agent35K4Shapes.marker := by
    rw [BB6.Agent2PacketP2Reset.e_two_reset,hprefix,hp,hm]
  have hresetObs : ObsEq
      (CryptidBoundary.run (BB6.Agent2PacketP2Reset.eTwoTime k Q)
        (BB6.Agent31PacketSource.packet (3*k+4) Q 2
          (false::List.replicate 6 true)))
      (BB6.Agent31PacketSource.packet (1+4*3^d*h) 0
        (3*d+(2*Q+6-3*d)) BB6.Agent35K4Shapes.marker) := by
    rw [hreset]
    exact BB6.Padding.cfgEq_refl _
  obtain ⟨Ttail,a,q,b,htail,hcanon⟩ :=
    chain_double_B_to_A_source_reentry d h t 0
      (2*Q+6-3*d) hh hd ha
  have hcombined := BB6.BoundaryPadding.source_chain
    (BB6.Agent2PacketP2Reset.eTwoTime k Q) Ttail
    (BB6.Agent31PacketSource.packet (3*k+4) Q 2
      (false::List.replicate 6 true))
    (BB6.Agent31PacketSource.packet (1+4*3^d*h) 0
      (3*d+(2*Q+6-3*d)) BB6.Agent35K4Shapes.marker)
    (DRegularSource.sourceSection ⟨a,q,b⟩)
    hresetObs htail
  exact ⟨BB6.Agent2PacketP2Reset.eTwoTime k Q+Ttail,
    a,q,b,hcombined,hcanon⟩

#print axioms all_A_marker_returns_floor
#print axioms regularEndpointFloor_sourceSection
#print axioms double_B_to_A_source_reentry
#print axioms chain_double_B_to_A_source_reentry
#print axioms reset_double_B_to_A_source_reentry

end BB6.Agent37EChainDoubleBReentry
