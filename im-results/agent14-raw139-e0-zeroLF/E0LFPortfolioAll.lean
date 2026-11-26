import E0LFPortfolio
import Cover3862
namespace BB6.Agent14E0LFPortfolio
open BB6Coverage
def allRows : List PartialMachine := BB6.Agent14ZeroLF3862.ctr :: closedRows
theorem allRows_never (p : PartialMachine) (hp : p ∈ allRows)
    (m : Machine) (hm : compatible p m) : NeverHalts m := by
  simp only [allRows, List.mem_cons] at hp
  rcases hp with rfl | h
  · exact BB6.Agent14ZeroLF3862.never_exact m hm
  · exact closedRows_never p h m hm
#print axioms allRows_never
end BB6.Agent14E0LFPortfolio
