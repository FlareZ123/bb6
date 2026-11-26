import Raw54RACounter99
namespace BB6.Agent8Raw54.RA.M68
open BB6Coverage
abbrev table : PartialMachine := refine M99.table (0,true) (some ⟨true,true,5⟩)
theorem never (m : Machine) (hm : compatible table m) : NeverHalts m :=
  M99.never m ((compatible_refine_iff M99.table m (0,true) (by rfl) (some ⟨true,true,5⟩)).mp hm).1
#print axioms never
end BB6.Agent8Raw54.RA.M68
