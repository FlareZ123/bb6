import LiveRankClock
import BitEventCutoffGenerated

namespace BB6.Agent12LiveRank

theorem certified_live_6747765517117253610 :
    ∃ N h, 6747765517117253610≤N ∧
      BB6Coverage.run BB6.Agent47CRaw.cMachine N BB6Coverage.blank =
        some (BB6.Agent47CRaw.embed h (BB6.Agent47CRaw.enc (954556,42914948,0))) :=
  section_reach_live_bound BB6.Agent12BitEventCutoff.live_endpoint

#print axioms certified_live_6747765517117253610
end BB6.Agent12LiveRank
