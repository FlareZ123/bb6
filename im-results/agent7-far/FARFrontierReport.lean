import FARFrontier
set_option maxHeartbeats 0
set_option maxRecDepth 12000

-- Exact arithmetic on the proof-carrying audit, evaluated by Lean's VM.
-- The numerical pair is an executable report, not an asserted axiom.
#eval BB6Coverage.FAR.evalReport (BB6Coverage.FAR.depth4 3)
