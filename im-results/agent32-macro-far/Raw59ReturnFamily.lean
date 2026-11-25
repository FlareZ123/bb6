import ReturnFamily
import MacroFARBridge
namespace BB6Coverage.Agent32ReturnFamily
def table (v : Fin 7) : PartialMachine := fun s =>
  (Raw59Variant.tab v s.1 s.2).map fun (w,d,q) => some ⟨w,d,q⟩
theorem tab_eq (v : Fin 7) : MacroFARBridge.project (table v) = Raw59Variant.tab v := by
  funext q b
  unfold MacroFARBridge.project table
  cases h : Raw59Variant.tab v q b with
  | none => rfl
  | some t => rcases t with ⟨w,d,q'⟩; rfl
theorem never (v : Fin 7) (m : Machine) (hm : compatible (table v) m) : NeverHalts m :=
  MacroFARBridge.never_of_live (table v) (by rw [tab_eq]; exact Raw59Variant.all_live v) m hm
#print axioms never
end BB6Coverage.Agent32ReturnFamily
