import I5D3Continuation
import PacketAZero
import Lean.Elab.Tactic.Omega

set_option maxRecDepth 180000
set_option maxHeartbeats 0

namespace BB6.Agent35DAllQK0
open CryptidBoundary
open BB6.BoundaryPadding
open BB6.Agent35I5Continuation

/-- All q≥3 on the t≡0 (mod3) E/E exceptional cylinder source-return
    in three original-machine F/0 endpoints. The three residue branches
    here are complete, closed-form, with primitive times. -/
def k (v : Nat) : Nat := 64*v+10
def preCost (v h : Nat) : Nat :=
  BB6.Agent31SecondSource.firstCost (3*v) h +
    BB6.Agent31SecondSource.secondCost (3*v)

theorem ee_to_a (v h : Nat) :
    ObsEq (run (preCost v h)
      (DRegularSource.sourceSection ⟨9*(3*v)+7,h+3,1⟩))
      (BB6.Agent31PacketSource.packet (3*k v+3) 2 (2*h+3) ys) := by
  have ha : 64*(3*v)+33 = 3*k v+3 := by
    dsimp [k]
    omega
  simpa only [preCost,ha] using (two_return_packet (3*v) h)

/-- Initial q = 3u+3: A-terminal p=3(2u+1), pure-unary destination. -/
def costZero (v u : Nat) : Nat :=
  preCost v (3*u) + BB6.Agent35PacketAZero.duration (k v) 2 (2*u+1)
def outZero (v u : Nat) : DRegular.L := ⟨512*v+109+16*u,0,0⟩

theorem q_mod0_source (v u : Nat) :
    ObsEq
      (run (costZero v u)
        (DRegularSource.sourceSection ⟨9*(3*v)+7,3*u+3,1⟩))
      (DRegularSource.sourceSection (outZero v u)) := by
  have hpre := ee_to_a v (3*u)
  have hA :
      ObsEq
        (run (BB6.Agent35PacketAZero.duration (k v) 2 (2*u+1))
          (BB6.Agent31PacketSource.packet (3*k v+3) 2 (2*(3*u)+3) ys))
        (DRegularSource.sourceSection (outZero v u)) := by
    have hp : 2*(3*u)+3 = 3*(2*u+1) := by omega
    rw [hp]
    have hout : 8*k v+17+2*2+8*(2*u+1) =
        512*v+109+16*u := by dsimp [k]; omega
    have hAraw := BB6.Agent35PacketAZero.source_a_packet_zero
      (k v) 2 (2*u+1)
    have hAobs :
        ObsEq
          (run (BB6.Agent35PacketAZero.duration (k v) 2 (2*u+1))
            (BB6.Agent31PacketSource.packet (3*k v+3) 2 (3*(2*u+1)) ys))
          (DRegularSource.sourceSection
            ⟨8*k v+17+2*2+8*(2*u+1),0,0⟩) := by
      rw [hAraw]
      exact BB6.Padding.cfgEq_refl _
    simpa only [outZero,hout] using hAobs
  simpa [costZero,Nat.add_assoc] using
    (source_chain
      (preCost v (3*u))
      (BB6.Agent35PacketAZero.duration (k v) 2 (2*u+1))
      (DRegularSource.sourceSection ⟨9*(3*v)+7,3*u+3,1⟩)
      (BB6.Agent31PacketSource.packet (3*k v+3) 2 (2*(3*u)+3) ys)
      (DRegularSource.sourceSection (outZero v u))
      hpre hA)

/-- Initial q=3u+4: A-terminal p=3(2u+1)+2, regular (q,b)=(3,2). -/
def costOne (v u : Nat) : Nat :=
  preCost v (3*u+1) + BB6.Agent35APacketGeneral.duration (k v) 2 (2*u+1)
def outOne (v u : Nat) : DRegular.L := ⟨512*v+103+16*u,3,2⟩

theorem q_mod1_source (v u : Nat) :
    ObsEq
      (run (costOne v u)
        (DRegularSource.sourceSection ⟨9*(3*v)+7,3*u+4,1⟩))
      (DRegularSource.sourceSection (outOne v u)) := by
  have hpre := ee_to_a v (3*u+1)
  have hA :
      ObsEq
        (run (BB6.Agent35APacketGeneral.duration (k v) 2 (2*u+1))
          (BB6.Agent31PacketSource.packet (3*k v+3) 2 (2*(3*u+1)+3) ys))
        (DRegularSource.sourceSection (outOne v u)) := by
    have hp : 2*(3*u+1)+3 = 3*(2*u+1)+2 := by omega
    rw [hp]
    have hout : 8*k v+11+2*2+8*(2*u+1) =
        512*v+103+16*u := by dsimp [k]; omega
    simpa only [outOne,hout] using
      (a_packet_regular_obs (k v) 2 (2*u+1))
  simpa [costOne,Nat.add_assoc] using
    (source_chain
      (preCost v (3*u+1))
      (BB6.Agent35APacketGeneral.duration (k v) 2 (2*u+1))
      (DRegularSource.sourceSection ⟨9*(3*v)+7,3*u+4,1⟩)
      (BB6.Agent31PacketSource.packet (3*k v+3) 2 (2*(3*u+1)+3) ys)
      (DRegularSource.sourceSection (outOne v u))
      hpre hA)

/-- Initial q=3u+5: A-terminal p=3(2u+2)+1, pure-unary. -/
def costTwo (v u : Nat) : Nat :=
  preCost v (3*u+2) + BB6.Agent35APacketUnary.duration (k v) 2 (2*u+2)
def outTwo (v u : Nat) : DRegular.L := ⟨512*v+129+16*u,0,0⟩

theorem q_mod2_source (v u : Nat) :
    ObsEq
      (run (costTwo v u)
        (DRegularSource.sourceSection ⟨9*(3*v)+7,3*u+5,1⟩))
      (DRegularSource.sourceSection (outTwo v u)) := by
  have hpre := ee_to_a v (3*u+2)
  have hA :
      ObsEq
        (run (BB6.Agent35APacketUnary.duration (k v) 2 (2*u+2))
          (BB6.Agent31PacketSource.packet (3*k v+3) 2 (2*(3*u+2)+3) ys))
        (DRegularSource.sourceSection (outTwo v u)) := by
    have hp : 2*(3*u+2)+3 = 3*(2*u+2)+1 := by omega
    rw [hp]
    have hout : 8*k v+29+2*2+8*(2*u+2) =
        512*v+129+16*u := by dsimp [k]; omega
    simpa only [outTwo,hout] using
      (a_packet_unary_obs (k v) 2 (2*u+2))
  simpa [costTwo,Nat.add_assoc] using
    (source_chain
      (preCost v (3*u+2))
      (BB6.Agent35APacketUnary.duration (k v) 2 (2*u+2))
      (DRegularSource.sourceSection ⟨9*(3*v)+7,3*u+5,1⟩)
      (BB6.Agent31PacketSource.packet (3*k v+3) 2 (2*(3*u+2)+3) ys)
      (DRegularSource.sourceSection (outTwo v u))
      hpre hA)

#print axioms ee_to_a
#print axioms q_mod0_source
#print axioms q_mod1_source
#print axioms q_mod2_source

end BB6.Agent35DAllQK0
