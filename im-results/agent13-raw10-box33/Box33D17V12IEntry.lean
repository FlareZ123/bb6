import Box33D17V12IRelay
namespace MacroI
set_option maxRecDepth 30000
set_option maxHeartbeats 0

/-- Exact finite blank-tape entry into the guarded packet return-map phase. -/
theorem blank_entry :
 run 490 (cfg .A z z) = some (phase 3 (word (bits "1010111") z)) := by
  set_option maxRecDepth 30000 in
   rfl

#print axioms blank_entry
end MacroI
