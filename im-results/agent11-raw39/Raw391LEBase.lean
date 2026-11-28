import Raw39SemanticChunks
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace BB6.Agent11Raw391LE
open BB6Coverage BB6.Agent13BlankDelay BB6.Agent8TNFPath
open BB6.Agent50TNFPilot BB6.Agent31ThreeHole BB6.Agent10ZipAudit
open BB6.Agent10CachedAudit BB6.Agent11SemanticChunks
abbrev p39 : PartialMachine :=
  refine (pathEnd root 2 (path.take 3)).1 (3,true) (some ⟨false,true,0⟩)
abbrev pChild : PartialMachine := refine p39 (0,true) (some ⟨true,false,4⟩)

end BB6.Agent11Raw391LE
