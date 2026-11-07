import Lean.Elab.Tactic.Omega
import BlankTwentiethEscape
import PacketSource

set_option maxHeartbeats 100000000
set_option maxRecDepth 8192

namespace BB6.Agent2TwentiethRejoin

open CryptidBoundary BB6.Agent31PacketSource
open BB6.BoundaryPadding BB6.Padding

/-- The twentieth exceptional source has t20 = 4 (mod 27), so the
    ensuing E/E/E word is in the 3v+1 unary residue. -/
def v20 : Nat := (BB6.Agent2TwentiethEscape.u20 - 1)/3

theorem u20_eq : BB6.Agent2TwentiethEscape.u20 = 3*v20+1 := by
  have hm := BB6.Agent2TwentiethEscape.t20_mod27
  dsimp [BB6.Agent2TwentiethEscape.u20, v20]
  omega

def k20 : Nat := 512*v20+255

/-- Literal source-tape identity: the off-L twentieth endpoint is an
    original-machine E-packet with q=4, p=4 and a fixed trailing word. -/
private theorem source_end_packet :
    BB6.Agent2E7ThirdReturnEscape.sourceEnd
      BB6.Agent2TwentiethEscape.u20 5 =
    packet (3*k20+4) 4 4 (false :: List.replicate 6 true) := by
  have hlen :
      8*(64*BB6.Agent2TwentiethEscape.u20+31)+9=3*k20+4 := by
    rw [u20_eq]
    dsimp [k20]
    omega
  simp only [BB6.Agent2E7ThirdReturnEscape.sourceEnd,
    packet, word, hlen]
  rfl

/-- One source-certified guarded E edge normalizes the suffix back to L. -/
private theorem packet_regular :
    packet (8*k20+9) 6 1 (false :: List.replicate 6 true) =
      DRegularSource.sourceSection ⟨8*k20+9,8,5⟩ := by
  have hw : word 6 1 (false :: List.replicate 6 true) =
      oppairs 8 ++ List.replicate 5 true := by decide
  have hfront : List.replicate (8*k20+9) true =
      true :: true :: List.replicate (8*k20+7) true := by
    rw [show 8*k20+9=2+(8*k20+7) by omega,
      ←List.replicate_append_replicate]
    rfl
  simp only [packet, hw, hfront, DRegularSource.sourceSection, init]
  have hlen : 8*k20+9-2=8*k20+7 := by omega
  rw [hlen]
  simp [List.append_assoc]

def return20Time : Nat := 12*k20*k20+49*k20+82

/-- Exact physical original-source return from the off-regular packet.
    Uses the existing universal guarded E source transition. -/
theorem from_packet_regular :
    ObsEq
      (run return20Time
        (BB6.Agent2E7ThirdReturnEscape.sourceEnd
          BB6.Agent2TwentiethEscape.u20 5))
      (DRegularSource.sourceSection ⟨8*k20+9,8,5⟩) := by
  rw [source_end_packet]
  change ObsEq
    (run (12*k20*k20+49*k20+58+6*4)
      (packet (3*k20+4) 4 (1+3)
        (false :: List.replicate 6 true))) _
  rw [BB6.Agent31PacketSource.e_packet]
  rw [packet_regular]
  exact BB6.Padding.cfgEq_refl _

def reentry20Time : Nat :=
  BB6.Agent2TwentiethEscape.escape20Time + return20Time

/-- A genuine-blank twenty-first regular section, CONDITIONAL ON the
    original-source certification of all preceding exceptional episodes.
    This is one finite reentry and does not establish nonhalting. -/
theorem blank_twentieth_reentry :
    ObsEq (run reentry20Time blank)
      (DRegularSource.sourceSection ⟨8*k20+9,8,5⟩) := by
  exact source_chain
    BB6.Agent2TwentiethEscape.escape20Time return20Time blank
    (BB6.Agent2E7ThirdReturnEscape.sourceEnd
      BB6.Agent2TwentiethEscape.u20 5)
    (DRegularSource.sourceSection ⟨8*k20+9,8,5⟩)
    BB6.Agent2TwentiethEscape.blank_twentieth_escape
    from_packet_regular

#print axioms u20_eq
#print axioms from_packet_regular
#print axioms blank_twentieth_reentry

end BB6.Agent2TwentiethRejoin
