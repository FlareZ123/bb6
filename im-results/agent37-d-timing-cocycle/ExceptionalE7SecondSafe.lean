import Lean.Elab.Tactic.Omega
import EAllDouble
import CryptidThree
import DObsSourceCandidate
import PacketSafeReentry

set_option maxHeartbeats 100000000
set_option maxRecDepth 16384

namespace BB6.Agent2E7SecondSafe

open CryptidBoundary BB6.BoundaryPadding BB6.Padding

private def suffix2 (q : Nat) : List Bool :=
  List.replicate (2*q-3) true ++ (false :: List.replicate 6 true)

def sourceStart (u q : Nat) : Cfg :=
  DRegularSource.sourceSection ⟨27*u+25,q,1⟩

def eTime (u q : Nat) : Nat :=
  BB6.Agent32EAll.duration (9*u+7) (q-1)

def middleTime (u : Nat) : Nat :=
  12*(24*u+19)*(24*u+19)+49*(24*u+19)+58

private theorem e_start_shape (u q : Nat) (hq : 3 ≤ q) :
    sourceStart u q =
      init (List.replicate (3*(9*u+7)+2) true ++
        false :: (pairs (q-1) ++ [true,true])) := by
  have hn : 27*u+25-2=3*(9*u+7)+2 := by omega
  have ho : CryptidBoundary.oppairs q =
      CryptidBoundary.oppairs (q-1+1) := by
    congr 1
    omega
  simp only [sourceStart,DRegularSource.sourceSection,init,hn,
    List.replicate_one]
  rw [List.append_assoc,ho,BB6.Agent25BGeneral.oppairs_last]

private theorem first_mid_shape (u q : Nat) (hq : 3 ≤ q) :
    BB6.Agent32EAll.output (9*u+7) (q-1) [] =
      init (List.replicate (3*(24*u+19)+2) true ++
        false :: ([true,true,true] ++ suffix2 q)) := by
  have hn : 8*(9*u+7)+5=3*(24*u+19)+4 := by omega
  have hqrep : 2*(q-1)+2=3+(2*q-3) := by omega
  have hrep : List.replicate (8*(9*u+7)+5) true =
      true::true::List.replicate (3*(24*u+19)+2) true := by
    rw [hn,show 3*(24*u+19)+4=2+(3*(24*u+19)+2) by omega]
    rw [←List.replicate_append_replicate]
    rfl
  have hp : List.replicate (2*(q-1)+2) true =
      [true,true,true] ++ List.replicate (2*q-3) true := by
    rw [hqrep,←List.replicate_append_replicate]
    rfl
  simp only [BB6.Agent32EAll.output,List.append_nil]
  rw [hrep,hp]
  simp [init,suffix2,List.append_assoc]

private def secondOutput (u q : Nat) : Cfg :=
  ⟨[],false,List.replicate (8*(24*u+19)+9) true ++
    (CryptidBoundary.packetThree ++ suffix2 q),5⟩

private theorem second_return (u q : Nat) (hq : 3 ≤ q) :
    run (middleTime u) (BB6.Agent32EAll.output (9*u+7) (q-1) []) =
      secondOutput u q := by
  rw [first_mid_shape u q hq]
  exact CryptidBoundary.full_E_three (24*u+19) (suffix2 q)

private theorem second_packet_shape (u q : Nat) (hq : 3 ≤ q) :
    secondOutput u q =
      BB6.Agent31PacketSource.packet (192*u+161) 2 (2*q-3)
        BB6.Agent2PacketOneReentry.fixedTail := by
  have ha : 8*(24*u+19)+9=192*u+161 := by omega
  have hword :
      CryptidBoundary.packetThree ++ suffix2 q =
        BB6.Agent31PacketSource.word 2 (2*q-3)
          BB6.Agent2PacketOneReentry.fixedTail := by
    simp [CryptidBoundary.packetThree,suffix2,
      BB6.Agent31PacketSource.word,
      BB6.Agent2PacketOneReentry.fixedTail,
      CryptidBoundary.oppairs]
  simp [secondOutput,ha,hword,BB6.Agent31PacketSource.packet]

private theorem first_return (u q : Nat) (hq : 3 ≤ q) :
    BB6.BoundaryPadding.ObsEq
      (run (eTime u q) (sourceStart u q))
      (BB6.Agent32EAll.output (9*u+7) (q-1) []) := by
  rw [e_start_shape u q hq]
  exact BB6.Agent32EAll.all_e_double_implicit_blank (9*u+7) (q-1)

/-- For q≥3 with q≡2 (mod 3), two original-source E returns from
    L(27u+25,q,1) reach a fixed-tail packet with p=2q-3≡1 (mod 3).
    The source-certified safe-packet theorem then returns to regular L. -/
theorem exceptional_EE_safe (u q : Nat) (hq : 3 ≤ q)
    (hmod : q % 3 = 2) :
    ∃ T a Q b,
      BB6.BoundaryPadding.ObsEq
        (run (eTime u q + middleTime u + T) (sourceStart u q))
        (BB6.Agent2BoundaryBZero.regularSection a Q b) := by
  obtain ⟨T,a,Q,b,hsafe⟩ :=
    BB6.Agent2PacketSafeReentry.all_safe_packets_regular
      ⟨192*u+161,2,2*q-3⟩ (by omega) (by omega)
  have h2 : BB6.BoundaryPadding.ObsEq
      (run (middleTime u) (BB6.Agent32EAll.output (9*u+7) (q-1) []))
      (secondOutput u q) := by
    rw [second_return u q hq]
    exact cfgEq_refl _
  have h23 := source_chain (middleTime u) T
    (BB6.Agent32EAll.output (9*u+7) (q-1) [])
    (secondOutput u q)
    (BB6.Agent2BoundaryBZero.regularSection a Q b) h2 hsafe
  exact ⟨T,a,Q,b,
    source_chain (eTime u q) (middleTime u+T)
      (sourceStart u q)
      (BB6.Agent32EAll.output (9*u+7) (q-1) [])
      (BB6.Agent2BoundaryBZero.regularSection a Q b)
      (first_return u q hq) h23⟩

#print axioms exceptional_EE_safe

end BB6.Agent2E7SecondSafe
