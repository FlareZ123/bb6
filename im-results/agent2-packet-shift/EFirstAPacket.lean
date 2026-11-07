import EAllDouble
import ExceptionalBGeneral
import PacketSource

set_option maxRecDepth 55000
set_option maxHeartbeats 100000000

namespace BB6.Agent2EFirstAPacket

open CryptidBoundary BB6.BoundaryPadding BB6.Padding

def fixedTail : List Bool := false :: List.replicate 6 true

def sourceStart (t q : Nat) : Cfg :=
  DRegularSource.sourceSection ⟨9*t+10,q,1⟩

def duration (t q : Nat) : Nat :=
  BB6.Agent32EAll.duration (3*t+2) (q-1)

def packetOutput (t q : Nat) : Cfg :=
  BB6.Agent31PacketSource.packet (24*t+21) 0 (2*q) fixedTail

private theorem input_shape (t q : Nat) (hq : 2 ≤ q) :
    sourceStart t q =
      init (List.replicate (3*(3*t+2)+2) true ++
        false :: (CryptidBoundary.pairs (q-1) ++ [true,true])) := by
  have hlen : (9*t+10)-2 = 3*(3*t+2)+2 := by omega
  have hq' : (q-1)+1 = q := by omega
  simp only [sourceStart, DRegularSource.sourceSection, init, hlen,
    List.replicate_one]
  have ho : CryptidBoundary.oppairs (q-1+1) ++ [true] =
      false :: (CryptidBoundary.pairs (q-1) ++ [true,true]) := by
    simpa using (BB6.Agent25BGeneral.oppairs_last (q-1))
  rw [hq'] at ho
  rw [List.append_assoc, ho]

private theorem output_shape (t q : Nat) (hq : 2 ≤ q) :
    BB6.Agent32EAll.output (3*t+2) (q-1) [] = packetOutput t q := by
  have hlen : 2*(q-1)+2 = 2*q := by omega
  have ha : 8*(3*t+2)+5 = 24*t+21 := by omega
  simp [packetOutput, BB6.Agent32EAll.output,
    BB6.Agent31PacketSource.packet, BB6.Agent31PacketSource.word,
    fixedTail, hlen, ha, CryptidBoundary.oppairs]

/--
One E-double return sends every source section of shape
L(9*t+10,q,1), with q at least two, to an A-boundary packet
M(24*t+21,0,2*q; 0 1^6).
-/
theorem exceptional_EA_packet (t q : Nat) (hq : 2 ≤ q) :
    ObsEq (run (duration t q) (sourceStart t q)) (packetOutput t q) := by
  have hraw :=
    BB6.Agent32EAll.all_e_double_implicit_blank (3*t+2) (q-1)
  rw [input_shape t q hq]
  simpa [duration, output_shape t q hq] using hraw

end BB6.Agent2EFirstAPacket
