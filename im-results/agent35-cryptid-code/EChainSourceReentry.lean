import Lean.Elab.Tactic.Omega
import EChainDoubleBReentry
import EChainBResidues

namespace BB6.Agent35EChainSourceReentry

open CryptidBoundary BB6.BoundaryPadding BB6.Padding
open BB6.Agent31PacketSource
open BB6.Agent37EChain
open BB6.Agent37EChainResidues
open BB6.Agent37EChainBResidues
open BB6.Agent37EChainBExit
open BB6.Agent37EChainDoubleBReentry
open BB6.Agent2PacketP2Reset

set_option maxHeartbeats 100000000
set_option maxRecDepth 55000

private theorem marker_eq :
    BB6.Agent2PacketP2Reset.marker = BB6.Agent35K4Shapes.marker := by
  decide

/-- Arbitrary-depth E-chain followed by an A-marker terminal, lifted all
    the way to a canonical DRegularSource section. The unary floor is the
    one supplied by Agent35MarkerA, not an inferred lower bound. -/
theorem chain_A_source_reentry (d h ka q p : Nat)
    (hh : 1 ≤ h)
    (ha : 1+4*8^d*h=3*ka+3) :
    ∃ (T a q' b : Nat),
      ObsEq
        (CryptidBoundary.run T
          (packet (1+4*3^d*h) q (3*d+p)
            BB6.Agent35K4Shapes.marker))
        (DRegularSource.sourceSection ⟨a,q',b⟩) ∧
      DRegular.Canon ⟨a,q',b⟩ := by
  obtain ⟨ta,n,hA,hn⟩ :=
    BB6.Agent37EChainDoubleBReentry.all_A_marker_returns_floor
      ka (q+2*d) p
  have hfloor :
      BB6.Agent37EChainDoubleBReentry.regularEndpointFloor
        (packet (1+4*3^d*h) q (3*d+p)
          BB6.Agent35K4Shapes.marker)
        (2*(4*ka+3)+5) := by
    refine ⟨chainTime d h q+ta,n,?_,hn⟩
    rw [CryptidBoundary.run_add,
      chain_return d h q p BB6.Agent35K4Shapes.marker hh, ha]
    exact hA
  exact BB6.Agent37EChainDoubleBReentry.regularEndpointFloor_sourceSection
    (packet (1+4*3^d*h) q (3*d+p)
      BB6.Agent35K4Shapes.marker)
    (2*(4*ka+3)+5) (by omega) hfloor

/-- The original E,p=2 reset followed by an arbitrary-depth E-chain and
    A exit has a canonical physical DRegularSource endpoint. -/
theorem reset_A_source_reentry (d k h ka Q p : Nat)
    (hh : 1 ≤ h)
    (hk : 2*k+1=3^d*h)
    (ha : 1+4*8^d*h=3*ka+3)
    (hp : 2*Q+6=3*d+p) :
    ∃ (T a q' b : Nat),
      ObsEq
        (CryptidBoundary.run T
          (packet (3*k+4) Q 2 (false::List.replicate 6 true)))
        (DRegularSource.sourceSection ⟨a,q',b⟩) ∧
      DRegular.Canon ⟨a,q',b⟩ := by
  have hprefix : 8*k+5=1+4*3^d*h := by
    calc
      8*k+5 = 4*(2*k+1)+1 := by omega
      _ = 4*(3^d*h)+1 := by rw [hk]
      _ = 1+4*3^d*h := by omega
  obtain ⟨T,a,q',b,hobs,hcanon⟩ :=
    chain_A_source_reentry d h ka 0 p hh ha
  have hreset :
      CryptidBoundary.run (eTwoTime k Q)
        (packet (3*k+4) Q 2 (false::List.replicate 6 true)) =
      packet (1+4*3^d*h) 0 (3*d+p)
        BB6.Agent35K4Shapes.marker := by
    rw [e_two_reset,hprefix,hp,marker_eq]
  have hresetObs : ObsEq
      (CryptidBoundary.run (eTwoTime k Q)
        (packet (3*k+4) Q 2 (false::List.replicate 6 true)))
      (packet (1+4*3^d*h) 0 (3*d+p)
        BB6.Agent35K4Shapes.marker) := by
    rw [hreset]
    exact BB6.Padding.cfgEq_refl _
  have hcombined := BB6.BoundaryPadding.source_chain
    (eTwoTime k Q) T
    (packet (3*k+4) Q 2 (false::List.replicate 6 true))
    (packet (1+4*3^d*h) 0 (3*d+p)
      BB6.Agent35K4Shapes.marker)
    (DRegularSource.sourceSection ⟨a,q',b⟩)
    hresetObs hobs
  exact ⟨eTwoTime k Q+T,a,q',b,hcombined,hcanon⟩

/-- Even-depth A-exit cylinders are now canonical source-section returns,
    not merely raw endpoint words. -/
theorem reset_even_depth_A_source_reentry (n s Q : Nat)
    (hQ : 3*(2*n) ≤ 2*Q+6) :
    ∃ (T a q b : Nat),
      ObsEq
        (CryptidBoundary.run T
          (packet (3*evenK n s+4) Q 2
            (false::List.replicate 6 true)))
        (DRegularSource.sourceSection ⟨a,q,b⟩) ∧
      DRegular.Canon ⟨a,q,b⟩ := by
  obtain ⟨ka,ha⟩ := even_A_index n (2*s+1)
  have hv : 3*(2*s+1)+2=6*s+5 := by omega
  rw [hv] at ha
  have hp : 2*Q+6 =
      3*(2*n)+(2*Q+6-3*(2*n)) := by omega
  exact reset_A_source_reentry (2*n) (evenK n s) (6*s+5) ka Q
    (2*Q+6-3*(2*n)) (by omega) (evenK_root n s) ha hp

/-- Odd-depth A-exit cylinders are now canonical source-section returns. -/
theorem reset_odd_depth_A_source_reentry (n s Q : Nat)
    (hQ : 3*(2*n+1) ≤ 2*Q+6) :
    ∃ (T a q b : Nat),
      ObsEq
        (CryptidBoundary.run T
          (packet (3*oddK n s+4) Q 2
            (false::List.replicate 6 true)))
        (DRegularSource.sourceSection ⟨a,q,b⟩) ∧
      DRegular.Canon ⟨a,q,b⟩ := by
  obtain ⟨ka,ha⟩ := odd_A_index n (2*s)
  have hv : 3*(2*s)+1=6*s+1 := by omega
  rw [hv] at ha
  have hp : 2*Q+6 =
      3*(2*n+1)+(2*Q+6-3*(2*n+1)) := by omega
  exact reset_A_source_reentry (2*n+1) (oddK n s) (6*s+1) ka Q
    (2*Q+6-3*(2*n+1)) (by omega) (oddK_root n s) ha hp

/-- A B packet after an arbitrary-depth E prefix, followed by A-marker
    completion, also lifts to a canonical DRegularSource section. -/
theorem chain_B_to_A_source_reentry (d h kb ka q p : Nat)
    (hh : 1 ≤ h)
    (hq : 1 ≤ q+2*d)
    (hb : 1+4*8^d*h=3*kb+2)
    (ha : 8*kb+10=3*ka+3) :
    ∃ (T a q' b : Nat),
      ObsEq
        (CryptidBoundary.run T
          (packet (1+4*3^d*h) q (3*d+p)
            BB6.Agent35K4Shapes.marker))
        (DRegularSource.sourceSection ⟨a,q',b⟩) ∧
      DRegular.Canon ⟨a,q',b⟩ := by
  obtain ⟨ta,n,hA,hn⟩ :=
    BB6.Agent37EChainDoubleBReentry.all_A_marker_returns_floor
      ka (q+2*d-1) p
  have hB :
      CryptidBoundary.run (bTime kb)
        (packet (3*kb+2) (q+2*d) p
          BB6.Agent35K4Shapes.marker) =
      packet (3*ka+3) (q+2*d-1) p
        BB6.Agent35K4Shapes.marker := by
    have hqeq : q+2*d=(q+2*d-1)+1 := by omega
    rw [hqeq,←ha]
    exact BB6.Agent31PacketSource.b_packet kb (q+2*d-1) p
      BB6.Agent35K4Shapes.marker
  have hfloor :
      BB6.Agent37EChainDoubleBReentry.regularEndpointFloor
        (packet (3*kb+2) (q+2*d) p
          BB6.Agent35K4Shapes.marker)
        (2*(4*ka+3)+5) := by
    refine ⟨bTime kb+ta,n,?_,hn⟩
    rw [CryptidBoundary.run_add,hB]
    exact hA
  obtain ⟨Ttail,a,q',b,hBAobs,hcanon⟩ :=
    BB6.Agent37EChainDoubleBReentry.regularEndpointFloor_sourceSection
      (packet (3*kb+2) (q+2*d) p
        BB6.Agent35K4Shapes.marker)
      (2*(4*ka+3)+5) (by omega) hfloor
  have hE :
      CryptidBoundary.run (chainTime d h q)
        (packet (1+4*3^d*h) q (3*d+p)
          BB6.Agent35K4Shapes.marker) =
      packet (3*kb+2) (q+2*d) p
        BB6.Agent35K4Shapes.marker := by
    rw [chain_return d h q p BB6.Agent35K4Shapes.marker hh,hb]
  have hEobs : ObsEq
      (CryptidBoundary.run (chainTime d h q)
        (packet (1+4*3^d*h) q (3*d+p)
          BB6.Agent35K4Shapes.marker))
      (packet (3*kb+2) (q+2*d) p
        BB6.Agent35K4Shapes.marker) := by
    rw [hE]
    exact BB6.Padding.cfgEq_refl _
  have hcombined := BB6.BoundaryPadding.source_chain
    (chainTime d h q) Ttail
    (packet (1+4*3^d*h) q (3*d+p)
      BB6.Agent35K4Shapes.marker)
    (packet (3*kb+2) (q+2*d) p
      BB6.Agent35K4Shapes.marker)
    (DRegularSource.sourceSection ⟨a,q',b⟩)
    hEobs hBAobs
  exact ⟨chainTime d h q+Ttail,a,q',b,hcombined,hcanon⟩

/-- Original E,p=2 reset followed by the B-to-A corridor has a canonical
    source-section endpoint. -/
theorem reset_B_to_A_source_reentry (d k h kb ka Q p : Nat)
    (hh : 1 ≤ h) (hd : 1 ≤ d)
    (hk : 2*k+1=3^d*h)
    (hb : 1+4*8^d*h=3*kb+2)
    (ha : 8*kb+10=3*ka+3)
    (hp : 2*Q+6=3*d+p) :
    ∃ (T a q b : Nat),
      ObsEq
        (CryptidBoundary.run T
          (packet (3*k+4) Q 2 (false::List.replicate 6 true)))
        (DRegularSource.sourceSection ⟨a,q,b⟩) ∧
      DRegular.Canon ⟨a,q,b⟩ := by
  have hprefix : 8*k+5=1+4*3^d*h := by
    calc
      8*k+5 = 4*(2*k+1)+1 := by omega
      _ = 4*(3^d*h)+1 := by rw [hk]
      _ = 1+4*3^d*h := by omega
  obtain ⟨T,a,q',b,hobs,hcanon⟩ :=
    chain_B_to_A_source_reentry d h kb ka 0 p hh
      (by omega) hb ha
  have hreset :
      CryptidBoundary.run (eTwoTime k Q)
        (packet (3*k+4) Q 2 (false::List.replicate 6 true)) =
      packet (1+4*3^d*h) 0 (3*d+p)
        BB6.Agent35K4Shapes.marker := by
    rw [e_two_reset,hprefix,hp,marker_eq]
  have hresetObs : ObsEq
      (CryptidBoundary.run (eTwoTime k Q)
        (packet (3*k+4) Q 2 (false::List.replicate 6 true)))
      (packet (1+4*3^d*h) 0 (3*d+p)
        BB6.Agent35K4Shapes.marker) := by
    rw [hreset]
    exact BB6.Padding.cfgEq_refl _
  have hcombined := BB6.BoundaryPadding.source_chain
    (eTwoTime k Q) T
    (packet (3*k+4) Q 2 (false::List.replicate 6 true))
    (packet (1+4*3^d*h) 0 (3*d+p)
      BB6.Agent35K4Shapes.marker)
    (DRegularSource.sourceSection ⟨a,q',b⟩)
    hresetObs hobs
  exact ⟨eTwoTime k Q+T,a,q',b,hcombined,hcanon⟩

/-- Even-depth B-to-A cylinders are canonical source-section returns. -/
theorem reset_even_depth_BA_source_reentry (n s Q : Nat)
    (hn : 1 ≤ n)
    (hQ : 3*(2*n) ≤ 2*Q+6) :
    ∃ (T a q b : Nat),
      ObsEq
        (CryptidBoundary.run T
          (packet (3*evenBK n s+4) Q 2
            (false::List.replicate 6 true)))
        (DRegularSource.sourceSection ⟨a,q,b⟩) ∧
      DRegular.Canon ⟨a,q,b⟩ := by
  obtain ⟨kb,ka,hb,ha⟩ := even_BA_index n (2*s)
  have hv : 9*(2*s)+1=18*s+1 := by omega
  rw [hv] at hb
  have hp : 2*Q+6 =
      3*(2*n)+(2*Q+6-3*(2*n)) := by omega
  exact reset_B_to_A_source_reentry (2*n) (evenBK n s) (18*s+1)
    kb ka Q (2*Q+6-3*(2*n))
    (by omega) (by omega) (evenBK_root n s) hb ha hp

/-- Odd-depth B-to-A cylinders are canonical source-section returns. -/
theorem reset_odd_depth_BA_source_reentry (n s Q : Nat)
    (hQ : 3*(2*n+1) ≤ 2*Q+6) :
    ∃ (T a q b : Nat),
      ObsEq
        (CryptidBoundary.run T
          (packet (3*oddBK n s+4) Q 2
            (false::List.replicate 6 true)))
        (DRegularSource.sourceSection ⟨a,q,b⟩) ∧
      DRegular.Canon ⟨a,q,b⟩ := by
  obtain ⟨kb,ka,hb,ha⟩ := odd_BA_index n (2*s+1)
  have hv : 9*(2*s+1)+8=18*s+17 := by omega
  rw [hv] at hb
  have hp : 2*Q+6 =
      3*(2*n+1)+(2*Q+6-3*(2*n+1)) := by omega
  exact reset_B_to_A_source_reentry (2*n+1) (oddBK n s) (18*s+17)
    kb ka Q (2*Q+6-3*(2*n+1))
    (by omega) (by omega) (oddBK_root n s) hb ha hp

#print axioms chain_A_source_reentry
#print axioms reset_A_source_reentry
#print axioms reset_even_depth_A_source_reentry
#print axioms reset_odd_depth_A_source_reentry
#print axioms chain_B_to_A_source_reentry
#print axioms reset_B_to_A_source_reentry
#print axioms reset_even_depth_BA_source_reentry
#print axioms reset_odd_depth_BA_source_reentry

end BB6.Agent35EChainSourceReentry
