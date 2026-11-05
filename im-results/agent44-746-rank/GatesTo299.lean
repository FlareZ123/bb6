import NewFiniteGates
import Gates270to281
import Gates282to299
namespace CascadeFastReturn
open CascadeSweep CascadeManyShield

/-- The entire remaining fatal index set from n=257 through n=299 has
    been excluded from the actual #746 blank-origin compressed reset orbit. -/
theorem fatal_unreachable_257_to_299 (n:Nat)
    (hn:257≤n) (hu:n≤299) (hres:n%6=4∨n%6=5) :
    ¬ReachC (2,0) (fatal n,0) := by
  by_cases h1 : n≤269
  · exact fatal_unreachable_257_to_269 n hn h1 hres
  · by_cases h2 : n≤281
    · have hlo : 274≤n := by omega
      exact excluded_range_274_281 n hlo h2 hres
    · have hlo : 286≤n := by omega
      exact excluded_range_286_299 n hlo hu hres

#print axioms fatal_unreachable_257_to_299
end CascadeFastReturn
