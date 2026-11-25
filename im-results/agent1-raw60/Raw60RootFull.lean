import Raw60RootAssembly
import Raw60A0LCData
import Raw60A0LFData
import Raw60A1LFData
import Raw60A1REData

set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace BB6.Agent1Raw60Root
open BB6Coverage BB6.Agent13BlankDelay

/-- Full weighted upper bound for every completion of raw60.
The nine previously enumerated ordinary children, four final children,
eleven side-cycle choices and the halt choice exhaust the first hole. -/
theorem all60 (m : Machine) (hm : compatible parent m) :
    WeightedBound 1175 m := by
  refine parent_scoreB 1175 (by decide) ?_ m hm
  intro mv hmv n hn
  simp only [remaining4, List.mem_cons, List.not_mem_nil, or_false] at hmv
  rcases hmv with rfl | rfl | rfl | rfl
  · exact lift (by decide : 251 ≤ 1175) (BB6.Agent1Raw60A0LC.all_closed n hn)
  · exact lift (by decide : 802 ≤ 1175) (BB6.Agent1Raw60A0LF.all_closed n hn)
  · exact BB6.Agent1Raw60A1LF.all_closed n hn
  · exact lift (by decide : 211 ≤ 1175) (BB6.Agent1Raw60A1RE.all_closed n hn)

#print axioms all60
end BB6.Agent1Raw60Root
