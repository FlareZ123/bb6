import Lean.Elab.Tactic.Omega
import ExternalCall107Prefix
import EQ1TerminalBlank

set_option maxHeartbeats 100000000
set_option maxRecDepth 30000

namespace BB6.Agent37ExternalTerminalHalt

open CryptidBoundary BB6.Agent31PacketSource
open BB6.Agent37ExternalCall99
open BB6.Agent37ExternalCall107

def finalK (s : Nat) : Nat :=
  1897137590064188545819787018382342682267975428761855001222473056385648716020711424*s+
  294853502963384192348157653050604257879822431777379944359784019685582418815621370

def terminalInput (s : Nat) : Cfg :=
  packet (call107OutputA (3*s)) 1 2 call99Tail

/-- The call-107 packet is exactly Agent32's source-certified
    01011011 terminal E cylinder after the final ternary refinement. -/
theorem terminalInput_eq_start (s : Nat) :
    terminalInput s = BB6.Agent32EQ1TerminalBlank.start (finalK s) := by
  have hn : call107OutputA (3*s) = 3*finalK s+4 := by
    simp [call107OutputA,finalK]
    omega
  rw [hn]
  simp [terminalInput,BB6.Agent32EQ1TerminalBlank.start,
    packet,word,call99Tail,CryptidBoundary.oppairs,
    CryptidBoundary.init,List.append_assoc]

/-- The exact 3^90 refinement of the externally selected P2 cylinder
    reaches frozen halt in the original six-state source semantics.
    This closes the internally source-composed call-17..terminal route;
    it is a prepared-packet cylinder and by itself is not a blank-root
    reachability theorem. -/
theorem external169_terminal_halts (s : Nat) :
    ∃ T c,
      ObsEq
        (run T
          (packet
            (3*(8727963568087712425891397479476727340041449*s+
                1356501840069695579809464475403825451716734)+4)
            0 2 (false :: List.replicate 6 true)))
        c ∧
      c.st = 6 := by
  obtain ⟨t0,h0⟩ := external169_call107_prefix (3*s)
  have hk :
      2909321189362570808630465826492242446680483*(3*s)+
          1356501840069695579809464475403825451716734 =
        8727963568087712425891397479476727340041449*s+
          1356501840069695579809464475403825451716734 := by
    omega
  rw [hk] at h0
  let t1 := BB6.Agent32EQ1TerminalBlank.liveTime (finalK s)+1
  let c := run t1 (terminalInput s)
  have hc : c.st = 6 := by
    dsimp [c,t1]
    rw [terminalInput_eq_start]
    exact BB6.Agent32EQ1TerminalBlank.full_frozen (finalK s)
  have h1 : ObsEq (run t1 (terminalInput s)) c := by
    exact BB6.Padding.cfgEq_refl _
  have hchain := BB6.BoundaryPadding.source_chain
    t0 t1
    (packet
      (3*(8727963568087712425891397479476727340041449*s+
          1356501840069695579809464475403825451716734)+4)
      0 2 (false :: List.replicate 6 true))
    (terminalInput s)
    c
    h0 h1
  exact ⟨t0+t1,c,hchain,hc⟩

#print axioms terminalInput_eq_start
#print axioms external169_terminal_halts

end BB6.Agent37ExternalTerminalHalt
