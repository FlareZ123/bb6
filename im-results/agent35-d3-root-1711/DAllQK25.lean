import I5D3Continuation
import PacketAZero
import Lean.Elab.Tactic.Omega

set_option maxRecDepth 180000
set_option maxHeartbeats 0

namespace BB6.Agent35DAllQK25
open CryptidBoundary
open BB6.BoundaryPadding
open BB6.Agent35I5Continuation

/-- A genuinely source-proved, closed-form four-return family for
    every E/E regular exceptional input with t = 9v+8 and q≥3.
    The three residue families exhaust q≥3. -/
def t (v : Nat) : Nat := 9*v+8
def kB (v : Nat) : Nat := 192*v+181
def kA (v : Nat) : Nat := 512*v+485

def bCost (v : Nat) : Nat :=
  12*kB v*kB v + 49*kB v+40
def preCost (v h : Nat) : Nat :=
  BB6.Agent31SecondSource.firstCost (t v) h +
  BB6.Agent31SecondSource.secondCost (t v) + bCost v

theorem b_to_a_packet (v h : Nat) :
    ObsEq
      (run (bCost v)
        (BB6.Agent31PacketSource.packet (64*t v+33) 2 (2*h+3) ys))
      (BB6.Agent31PacketSource.packet (3*kA v+3) 1 (2*h+3) ys) := by
  have hin : 64*t v+33 = 3*kB v+2 := by
    dsimp [t,kB]
    omega
  have hout : 8*kB v+10 = 3*kA v+3 := by
    dsimp [kB,kA]
    omega
  rw [hin]
  change ObsEq
    (run (12*kB v*kB v+49*kB v+40)
      (BB6.Agent31PacketSource.packet (3*kB v+2) 2 (2*h+3) ys))
    (BB6.Agent31PacketSource.packet (3*kA v+3) 1 (2*h+3) ys)
  rw [BB6.Agent31PacketSource.b_packet (kB v) 1 (2*h+3) ys, hout]
  exact BB6.Padding.cfgEq_refl _

theorem ee_b_packet (v h : Nat) :
    ObsEq
      (run (preCost v h)
        (DRegularSource.sourceSection ⟨9*t v+7,h+3,1⟩))
      (BB6.Agent31PacketSource.packet (3*kA v+3) 1 (2*h+3) ys) := by
  have hTwo := two_return_packet (t v) h
  have hB := b_to_a_packet v h
  simpa [preCost,Nat.add_assoc] using
    (source_chain
      (BB6.Agent31SecondSource.firstCost (t v) h +
       BB6.Agent31SecondSource.secondCost (t v))
      (bCost v)
      (DRegularSource.sourceSection ⟨9*t v+7,h+3,1⟩)
      (BB6.Agent31PacketSource.packet (64*t v+33) 2 (2*h+3) ys)
      (BB6.Agent31PacketSource.packet (3*kA v+3) 1 (2*h+3) ys)
      hTwo hB)

/-- For q=3u+3, the packet terminates in an A p≡0 (mod3) return. -/
def costZero (v u : Nat) : Nat :=
  preCost v (3*u) + BB6.Agent35PacketAZero.duration (kA v) 1 (2*u+1)
def outZero (v u : Nat) : DRegular.L := ⟨4096*v+3907+16*u,0,0⟩

theorem q_mod0_source (v u : Nat) :
    ObsEq
      (run (costZero v u)
        (DRegularSource.sourceSection ⟨9*t v+7,3*u+3,1⟩))
      (DRegularSource.sourceSection (outZero v u)) := by
  have hpre := ee_b_packet v (3*u)
  have hA :
      ObsEq
        (run (BB6.Agent35PacketAZero.duration (kA v) 1 (2*u+1))
          (BB6.Agent31PacketSource.packet (3*kA v+3) 1 (2*(3*u)+3) ys))
        (DRegularSource.sourceSection (outZero v u)) := by
    have hp : 2*(3*u)+3 = 3*(2*u+1) := by omega
    rw [hp]
    have heq : 8*kA v+17+2*1+8*(2*u+1) =
        4096*v+3907+16*u := by dsimp [kA]; omega
    have hAraw := BB6.Agent35PacketAZero.source_a_packet_zero
      (kA v) 1 (2*u+1)
    have hAobs :
        ObsEq
          (run (BB6.Agent35PacketAZero.duration (kA v) 1 (2*u+1))
            (BB6.Agent31PacketSource.packet (3*kA v+3) 1 (3*(2*u+1)) ys))
          (DRegularSource.sourceSection
            ⟨8*kA v+17+2*1+8*(2*u+1),0,0⟩) := by
      rw [hAraw]
      exact BB6.Padding.cfgEq_refl _
    simpa only [outZero,heq] using hAobs
  simpa [costZero,Nat.add_assoc] using
    (source_chain
      (preCost v (3*u))
      (BB6.Agent35PacketAZero.duration (kA v) 1 (2*u+1))
      (DRegularSource.sourceSection ⟨9*t v+7,3*u+3,1⟩)
      (BB6.Agent31PacketSource.packet (3*kA v+3) 1 (2*(3*u)+3) ys)
      (DRegularSource.sourceSection (outZero v u))
      hpre hA)

/-- For q=3u+4, the packet terminates in A p≡2 (mod3). -/
def costOne (v u : Nat) : Nat :=
  preCost v (3*u+1) +
    BB6.Agent35APacketGeneral.duration (kA v) 1 (2*u+1)
def outOne (v u : Nat) : DRegular.L := ⟨4096*v+3901+16*u,3,2⟩

theorem q_mod1_source (v u : Nat) :
    ObsEq
      (run (costOne v u)
        (DRegularSource.sourceSection ⟨9*t v+7,3*u+4,1⟩))
      (DRegularSource.sourceSection (outOne v u)) := by
  have hpre := ee_b_packet v (3*u+1)
  have hA :
      ObsEq
        (run (BB6.Agent35APacketGeneral.duration (kA v) 1 (2*u+1))
          (BB6.Agent31PacketSource.packet (3*kA v+3) 1 (2*(3*u+1)+3) ys))
        (DRegularSource.sourceSection (outOne v u)) := by
    have hp : 2*(3*u+1)+3 = 3*(2*u+1)+2 := by omega
    rw [hp]
    have hout : 8*kA v+11+2*1+8*(2*u+1) =
        4096*v+3901+16*u := by dsimp [kA]; omega
    simpa only [outOne,hout] using
      (a_packet_regular_obs (kA v) 1 (2*u+1))
  simpa [costOne,Nat.add_assoc] using
    (source_chain
      (preCost v (3*u+1))
      (BB6.Agent35APacketGeneral.duration (kA v) 1 (2*u+1))
      (DRegularSource.sourceSection ⟨9*t v+7,3*u+4,1⟩)
      (BB6.Agent31PacketSource.packet (3*kA v+3) 1 (2*(3*u+1)+3) ys)
      (DRegularSource.sourceSection (outOne v u))
      hpre hA)

/-- For q=3u+5, the packet terminates in A p≡1 (mod3). -/
def costTwo (v u : Nat) : Nat :=
  preCost v (3*u+2) +
    BB6.Agent35APacketUnary.duration (kA v) 1 (2*u+2)
def outTwo (v u : Nat) : DRegular.L := ⟨4096*v+3927+16*u,0,0⟩

theorem q_mod2_source (v u : Nat) :
    ObsEq
      (run (costTwo v u)
        (DRegularSource.sourceSection ⟨9*t v+7,3*u+5,1⟩))
      (DRegularSource.sourceSection (outTwo v u)) := by
  have hpre := ee_b_packet v (3*u+2)
  have hA :
      ObsEq
        (run (BB6.Agent35APacketUnary.duration (kA v) 1 (2*u+2))
          (BB6.Agent31PacketSource.packet (3*kA v+3) 1 (2*(3*u+2)+3) ys))
        (DRegularSource.sourceSection (outTwo v u)) := by
    have hp : 2*(3*u+2)+3 = 3*(2*u+2)+1 := by omega
    rw [hp]
    have hout : 8*kA v+29+2*1+8*(2*u+2) =
        4096*v+3927+16*u := by dsimp [kA]; omega
    simpa only [outTwo,hout] using
      (a_packet_unary_obs (kA v) 1 (2*u+2))
  simpa [costTwo,Nat.add_assoc] using
    (source_chain
      (preCost v (3*u+2))
      (BB6.Agent35APacketUnary.duration (kA v) 1 (2*u+2))
      (DRegularSource.sourceSection ⟨9*t v+7,3*u+5,1⟩)
      (BB6.Agent31PacketSource.packet (3*kA v+3) 1 (2*(3*u+2)+3) ys)
      (DRegularSource.sourceSection (outTwo v u))
      hpre hA)

#print axioms ee_b_packet
#print axioms q_mod0_source
#print axioms q_mod1_source
#print axioms q_mod2_source

end BB6.Agent35DAllQK25
