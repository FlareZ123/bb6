import F412ClockBridge
import F412CountedRoot

namespace BB6.Agent26F412Graft
open BB6Coverage

theorem fClock : HaltsAfter fLiteral fMoves :=
  fClock_of_source Agent26F412.F412_exact_halt.1 Agent26F412.F412_exact_halt.2

#print axioms fClock
end BB6.Agent26F412Graft
