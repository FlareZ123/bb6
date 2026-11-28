import Lean.Elab.Tactic.Omega
import EChainDoubleBReentry
import Seed24956SecondReentry

set_option maxRecDepth 180000
set_option maxHeartbeats 100000000

namespace BB6.Agent37OddDepthSecondReturn

open CryptidBoundary BB6.BoundaryPadding
open BB6.Agent31PacketSource
open BB6.Agent2Seed24956SecondReentry

/-- The canonical regular-section index produced by the odd-depth
    P2-reset / E-chain / B / B / A route.  Writing d=2n+1 makes the
    closed endpoint 512*t+4*d+376 = 512*t+8*n+380. -/
def oddEndpoint (n t : Nat) : Nat := 512*t + 8*n + 380

def oddEndpointState (n t : Nat) : DRegular.L :=
  ⟨oddEndpoint n t,2,2⟩

/-- Exact primitive time through the reset, odd E-chain, two B packets,
    and the p=3 marker-A close. -/
def oddResetTime (n k h t : Nat) : Nat :=
  BB6.Agent2PacketP2Reset.eTwoTime k (3*n) +
    BB6.Agent37EChain.chainTime (2*n+1) h 0 +
    BB6.Agent37EChainDoubleBReentry.bTwiceTime t +
    BB6.Agent35MarkerA.aTime0 (64*t+45) (4*n) 1

/-- The marker code after the two B edges has 4n pair symbols and one
    triple symbol, hence exact A-counter increment 4n+4. -/
theorem markerCodeIncOne (q : Nat) :
    CryptidA.wordInc (BB6.Agent35MarkerA.code q 1) = q+4 := by
  induction q with
  | zero => rfl
  | succ q ih =>
    change 1 + CryptidA.wordInc (BB6.Agent35MarkerA.code q 1) =
      Nat.succ q + 4
    rw [ih]
    omega


private theorem regularSection_sourceSection
    (a q b : Nat) (ha : 2 ≤ a) :
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

/-- Exact physical bridge for the marker-A zero endpoint. -/
theorem endpointZero_sourceSection_exact (m : Nat) (hm : 1 ≤ m) :
    ObsEq (BB6.Agent37EChainDoubleBReentry.endpointZero m)
      (DRegularSource.sourceSection ⟨m+1,2,2⟩) := by
  have hrep : List.replicate (m+1) true =
      List.replicate m true ++ [true] := by
    rw [show m+1 = m+1 by rfl,
      ← List.replicate_append_replicate]
    rfl
  have heq :
      BB6.Agent37EChainDoubleBReentry.endpointZero m =
        BB6.Agent2BoundaryBZero.regularSection (m+1) 2 2 := by
    simp [BB6.Agent37EChainDoubleBReentry.endpointZero,
      BB6.Agent2BoundaryBZero.regularSection,
      CryptidBoundary.oppairs,hrep,List.append_assoc]
  have hsec := regularSection_sourceSection (m+1) 2 2 (by omega)
  rw [heq,hsec]
  exact BB6.Padding.cfgEq_refl _

/-- All odd E-chain depths have one exact source endpoint formula.
    For d=2n+1 and Q=3n, if the reset and double-B congruence identities
    hold, the literal original six-state machine reaches
    L(512*t+8*n+380,2,2).  No blank-root reachability is assumed. -/
theorem odd_depth_reset_exact
    (n k h t : Nat) (hh : 1 ≤ h)
    (hk : 2*k+1 = 3^(2*n+1)*h)
    (ha : 1+4*8^(2*n+1)*h = 27*t+17) :
    ObsEq
      (CryptidBoundary.run (oddResetTime n k h t)
        (packet (3*k+4) (3*n) 2
          (false::List.replicate 6 true)))
      (DRegularSource.sourceSection (oddEndpointState n t)) := by
  have hmarker :
      BB6.Agent2PacketP2Reset.marker = BB6.Agent35K4Shapes.marker := by
    decide
  have hprefix : 8*k+5 = 1+4*3^(2*n+1)*h := by
    calc
      8*k+5 = 4*(2*k+1)+1 := by omega
      _ = 4*(3^(2*n+1)*h)+1 := by rw [hk]
      _ = 1+4*3^(2*n+1)*h := by
        rw [Nat.mul_assoc, Nat.add_comm]
  have hp : 2*(3*n)+6 = 3*(2*n+1)+3 := by omega
  have hq : 2*(2*n+1) = 4*n+2 := by omega
  have hresetRaw :
      CryptidBoundary.run (BB6.Agent2PacketP2Reset.eTwoTime k (3*n))
        (packet (3*k+4) (3*n) 2
          (false::List.replicate 6 true)) =
      packet (1+4*3^(2*n+1)*h) 0
        (3*(2*n+1)+3) BB6.Agent35K4Shapes.marker := by
    have h0 := BB6.Agent2PacketP2Reset.e_two_reset k (3*n)
    rw [hprefix,hmarker,hp] at h0
    exact h0
  have hchainRaw :
      CryptidBoundary.run
        (BB6.Agent37EChain.chainTime (2*n+1) h 0)
        (packet (1+4*3^(2*n+1)*h) 0
          (3*(2*n+1)+3) BB6.Agent35K4Shapes.marker) =
      packet (27*t+17) (4*n+2) 3 BB6.Agent35K4Shapes.marker := by
    have h0 := BB6.Agent37EChain.chain_return
      (2*n+1) h 0 3 BB6.Agent35K4Shapes.marker hh
    rw [ha,hq] at h0
    simpa using h0
  have hBRaw :
      CryptidBoundary.run
        (BB6.Agent37EChainDoubleBReentry.bTwiceTime t)
        (packet (27*t+17) (4*n+2) 3 BB6.Agent35K4Shapes.marker) =
      packet (3*(64*t+45)+3) (4*n) 3 BB6.Agent35K4Shapes.marker := by
    have h0 := BB6.Agent37EChainDoubleBExit.b_twice
      t (4*n) 3 BB6.Agent35K4Shapes.marker
    simpa [BB6.Agent37EChainDoubleBReentry.bTwiceTime] using h0
  have hinc :
      CryptidA.wordInc (BB6.Agent35MarkerA.code (4*n) 1) = 4*n+4 := by
    simpa using markerCodeIncOne (4*n)
  have hN :
      2*((4*(64*t+45)+3) +
        CryptidA.wordInc (BB6.Agent35MarkerA.code (4*n) 1))+5 =
      512*t+8*n+379 := by
    rw [hinc]
    omega
  have hARaw :
      CryptidBoundary.run
        (BB6.Agent35MarkerA.aTime0 (64*t+45) (4*n) 1)
        (packet (3*(64*t+45)+3) (4*n) 3
          BB6.Agent35K4Shapes.marker) =
      BB6.Agent37EChainDoubleBReentry.endpointZero
        (512*t+8*n+379) := by
    have h0 := BB6.Agent35MarkerA.close_zero (64*t+45) (4*n) 1
    rw [hN] at h0
    simpa only [BB6.Agent37EChainDoubleBReentry.endpointZero] using h0
  have hreset : ObsEq
      (CryptidBoundary.run (BB6.Agent2PacketP2Reset.eTwoTime k (3*n))
        (packet (3*k+4) (3*n) 2
          (false::List.replicate 6 true)))
      (packet (1+4*3^(2*n+1)*h) 0
        (3*(2*n+1)+3) BB6.Agent35K4Shapes.marker) := by
    rw [hresetRaw]
    exact BB6.Padding.cfgEq_refl _
  have hchain : ObsEq
      (CryptidBoundary.run
        (BB6.Agent37EChain.chainTime (2*n+1) h 0)
        (packet (1+4*3^(2*n+1)*h) 0
          (3*(2*n+1)+3) BB6.Agent35K4Shapes.marker))
      (packet (27*t+17) (4*n+2) 3 BB6.Agent35K4Shapes.marker) := by
    rw [hchainRaw]
    exact BB6.Padding.cfgEq_refl _
  have hB : ObsEq
      (CryptidBoundary.run
        (BB6.Agent37EChainDoubleBReentry.bTwiceTime t)
        (packet (27*t+17) (4*n+2) 3 BB6.Agent35K4Shapes.marker))
      (packet (3*(64*t+45)+3) (4*n) 3
        BB6.Agent35K4Shapes.marker) := by
    rw [hBRaw]
    exact BB6.Padding.cfgEq_refl _
  have hA : ObsEq
      (CryptidBoundary.run
        (BB6.Agent35MarkerA.aTime0 (64*t+45) (4*n) 1)
        (packet (3*(64*t+45)+3) (4*n) 3
          BB6.Agent35K4Shapes.marker))
      (DRegularSource.sourceSection (oddEndpointState n t)) := by
    rw [hARaw]
    have hs := endpointZero_sourceSection_exact
      (512*t+8*n+379) (by omega)
    simpa [oddEndpointState,oddEndpoint] using hs
  have h01 := BB6.BoundaryPadding.source_chain
    (BB6.Agent2PacketP2Reset.eTwoTime k (3*n))
    (BB6.Agent37EChain.chainTime (2*n+1) h 0)
    (packet (3*k+4) (3*n) 2 (false::List.replicate 6 true))
    (packet (1+4*3^(2*n+1)*h) 0
      (3*(2*n+1)+3) BB6.Agent35K4Shapes.marker)
    (packet (27*t+17) (4*n+2) 3 BB6.Agent35K4Shapes.marker)
    hreset hchain
  have h012 := BB6.BoundaryPadding.source_chain
    (BB6.Agent2PacketP2Reset.eTwoTime k (3*n) +
      BB6.Agent37EChain.chainTime (2*n+1) h 0)
    (BB6.Agent37EChainDoubleBReentry.bTwiceTime t)
    (packet (3*k+4) (3*n) 2 (false::List.replicate 6 true))
    (packet (27*t+17) (4*n+2) 3 BB6.Agent35K4Shapes.marker)
    (packet (3*(64*t+45)+3) (4*n) 3
      BB6.Agent35K4Shapes.marker)
    h01 hB
  have h0123 := BB6.BoundaryPadding.source_chain
    (BB6.Agent2PacketP2Reset.eTwoTime k (3*n) +
      BB6.Agent37EChain.chainTime (2*n+1) h 0 +
      BB6.Agent37EChainDoubleBReentry.bTwiceTime t)
    (BB6.Agent35MarkerA.aTime0 (64*t+45) (4*n) 1)
    (packet (3*k+4) (3*n) 2 (false::List.replicate 6 true))
    (packet (3*(64*t+45)+3) (4*n) 3
      BB6.Agent35K4Shapes.marker)
    (DRegularSource.sourceSection (oddEndpointState n t))
    h012 hA
  simpa [oddResetTime,Nat.add_assoc] using h0123

/-- If an odd-depth endpoint lies in the 3^87 lift of L(24956,2,2),
    its authenticated 86-step DRegular transport lands in the same q=5
    safe-E family as the base seed.  Hence the prepared packet has a
    second source-certified return to a canonical regular section. -/
theorem odd_depth_aligned_second_reentry
    (n k h t r : Nat) (hh : 1 ≤ h)
    (hk : 2*k+1 = 3^(2*n+1)*h)
    (ha : 1+4*8^(2*n+1)*h = 27*t+17)
    (halign : oddEndpoint n t = 24956 + 3^87*r) :
    ∃ T a q b,
      ObsEq
        (CryptidBoundary.run
          (oddResetTime n k h t +
            DRegular.accumulated 86 (oddEndpointState n t) + T)
          (packet (3*k+4) (3*n) 2
            (false::List.replicate 6 true)))
        (DRegularSource.sourceSection ⟨a,q,b⟩) ∧
      DRegular.Canon ⟨a,q,b⟩ := by
  let shiftedK : Nat := exitK + 8^86*r
  have hpow : 3^87 = 3^86*3 := by decide
  have hin :
      BB6.DRegularSourceShift.inputLift seed24956 86 (3*r) =
        oddEndpointState n t := by
    simp only [BB6.DRegularSourceShift.inputLift,
      BB6.DRegularShift.shiftNat,seed24956,oddEndpointState]
    congr 1
    rw [halign,hpow]
    omega
  have hbase :
      107283033157493534200791430928221345342090 =
        3*exitK+4 := by
    decide
  have hout :
      BB6.DRegularSourceShift.outputLift seed24956Exit 86 (3*r) =
        (⟨3*shiftedK+4,5,1⟩ : DRegular.L) := by
    simp only [BB6.DRegularSourceShift.outputLift,
      BB6.DRegularShift.shiftNat,seed24956Exit]
    congr 1
    rw [hbase]
    dsimp [shiftedK]
    omega
  have hreg :=
    (BB6.DRegularSourceShift.paired_original_run
      seed24956 seed24956Exit 86 (3*r)
      seed24956_canon seed24956_run86).2
  rw [hin,hout] at hreg
  obtain ⟨S,a,q,b,hSafe,hcanon⟩ :=
    BB6.Agent37ExceptionalESafeCanonical.all_E_safe_reentry_canonical
      shiftedK 5 (by omega) (by omega)
  have h01 := BB6.BoundaryPadding.source_chain
    (oddResetTime n k h t)
    (DRegular.accumulated 86 (oddEndpointState n t))
    (packet (3*k+4) (3*n) 2 (false::List.replicate 6 true))
    (DRegularSource.sourceSection (oddEndpointState n t))
    (DRegularSource.sourceSection ⟨3*shiftedK+4,5,1⟩)
    (odd_depth_reset_exact n k h t hh hk ha)
    hreg
  have h012 := BB6.BoundaryPadding.source_chain
    (oddResetTime n k h t +
      DRegular.accumulated 86 (oddEndpointState n t))
    (BB6.Agent32EAll.duration shiftedK 4 + S)
    (packet (3*k+4) (3*n) 2 (false::List.replicate 6 true))
    (DRegularSource.sourceSection ⟨3*shiftedK+4,5,1⟩)
    (DRegularSource.sourceSection ⟨a,q,b⟩)
    h01 hSafe
  exact ⟨BB6.Agent32EAll.duration shiftedK 4 + S,a,q,b,
    by simpa [Nat.add_assoc] using h012,hcanon⟩

#print axioms markerCodeIncOne
#print axioms endpointZero_sourceSection_exact
#print axioms odd_depth_reset_exact
#print axioms odd_depth_aligned_second_reentry

end BB6.Agent37OddDepthSecondReturn
