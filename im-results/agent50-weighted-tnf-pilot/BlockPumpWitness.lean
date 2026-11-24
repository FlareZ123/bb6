import BlockPump
import RootFrontier

set_option maxRecDepth 24000
set_option maxHeartbeats 0

namespace BB6Coverage.Agent50Pump
open BB6Coverage BB6.Agent50RootFrontier

structure CheckedPump where
  table : PackedTable
  cert : Certificate
  checked : cert.check (unpackTable table) = true

theorem CheckedPump.never (w : CheckedPump) (m : Machine) (hm : compatible (unpackTable w.table) m) : NeverHalts m :=
  w.cert.never (unpackTable w.table) w.checked m hm

end BB6Coverage.Agent50Pump
