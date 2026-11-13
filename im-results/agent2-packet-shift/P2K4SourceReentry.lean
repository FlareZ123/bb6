import P2K4Source
import EChainAExit
import EChainBEExit
import BoundaryPadding
import BoundaryBZero

namespace BB6.Agent2P2K4SourceReentry
open CryptidBoundary BB6.Agent31PacketSource
open BB6.Agent35K4 BB6.Agent35K4Shapes BB6.Agent37EChainAExit
open BB6.Agent2PacketP2Reset

set_option maxHeartbeats 12000000
set_option maxRecDepth 8192

/-- Convert Agent 35's exact q≡1 (mod 3) p=2 source return into the
    physical regularSection language used by the blank-root chain. -/
theorem close_one_regular_reentry (t u : Nat) :
    ∃ (T a q b : Nat),
      BB6.BoundaryPadding.ObsEq
        (run T
          (packet (3*firstK t+4) (3*u+1) 2
            (false::List.replicate 6 true)))
        (BB6.Agent2BoundaryBZero.regularSection a q b) := by
  let ka := aK t
  let ws := code u
  let m := 4*ka+3+CryptidA.wordInc ws
  let finalTime := (12*ka*ka+41*ka+32) +
    (CryptidA.wordCost (4*ka+3) ws + (2*m+36))
  let totalTime := twoEsTime t (3*u+1)+finalTime
  have hclose := BB6.Agent35K4.close_one t u
  have hend :
      BB6.Agent37EChainAExit.regularEndpoint
        (run totalTime
          (packet (3*firstK t+4) (3*u+1) 2
            (false::List.replicate 6 true))) := by
    unfold BB6.Agent37EChainAExit.regularEndpoint
    refine ⟨0,2*m+5,Or.inr (Or.inr ?_)⟩
    change run totalTime
      (packet (3*firstK t+4) (3*u+1) 2
        (false::List.replicate 6 true)) =
      (⟨[],false,List.replicate (2*m+5) true ++
        [false,true,false,true,false,true,false,true,false],5⟩ : Cfg)
    simpa [totalTime,finalTime,ka,ws,m] using hclose
  obtain ⟨Ttail,a,q,b,htail⟩ :=
    BB6.Agent37EChainAExit.regularEndpoint_reentry _ hend
  refine ⟨totalTime+Ttail,a,q,b,?_⟩
  rw [run_add]
  exact htail

/-- Root-prefix integration interface for the q≡1 (mod 3) p=2 family. -/
theorem source_chain_close_one (source : Cfg) (Troot t u : Nat)
    (hroot : BB6.BoundaryPadding.ObsEq
      (run Troot source)
      (packet (3*firstK t+4) (3*u+1) 2
        (false::List.replicate 6 true))) :
    ∃ (T a q b : Nat),
      BB6.BoundaryPadding.ObsEq (run T source)
        (BB6.Agent2BoundaryBZero.regularSection a q b) := by
  obtain ⟨Ttail,a,q,b,htail⟩ := close_one_regular_reentry t u
  exact ⟨Troot+Ttail,a,q,b,
    BB6.BoundaryPadding.source_chain Troot Ttail source
      (packet (3*firstK t+4) (3*u+1) 2
        (false::List.replicate 6 true))
      (BB6.Agent2BoundaryBZero.regularSection a q b)
      hroot htail⟩

#print axioms close_one_regular_reentry
#print axioms source_chain_close_one
end BB6.Agent2P2K4SourceReentry
