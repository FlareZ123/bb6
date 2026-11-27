import Symmetry
import BlockFARBridge
import ThreeHoleAudit
namespace BB6.Agent3UnaryGrow
open BB6Coverage

def reflectPartial (p : PartialMachine) : PartialMachine := fun s =>
  (p s).map (Option.map reflectMove)

theorem compatible_reflect {p : PartialMachine} {m : Machine} (hm : compatible p m) :
    compatible (reflectPartial p) (reflectTable m) := by
  intro s t ht
  unfold reflectPartial at ht
  cases h : p s with
  | none => simp [h] at ht
  | some u =>
    have he := hm s u h
    simp only [h, Option.map_some, Option.some.injEq] at ht
    subst t
    simp [reflectTable, he]

theorem never_of_reflect (m : Machine) (h : NeverHalts (reflectTable m)) : NeverHalts m := by
  intro n
  have hn := h n
  have he : run (reflectTable m) n blank = (run m n blank).map mirrorConfig := by
    simpa only [mirror_blank] using mirror_run m blank n
  rw [he] at hn
  change ((run m n blank).map mirrorConfig).isSome = true at hn
  change (run m n blank).isSome = true
  cases hr : run m n blank with
  | none => rw [hr] at hn; contradiction
  | some c => rfl

theorem reflected_never (M : BB6BlockFAR.Table) (p : PartialMachine)
    (hp : reflectPartial p = BB6BlockFAR.partialTable M)
    (forever : ∀ k, ∃ c, BB6BlockFAR.run M k BB6BlockFAR.primBlank = some c)
    (m : Machine) (hm : compatible p m) : NeverHalts m := by
  apply never_of_reflect m
  exact BB6BlockFAR.transfer_never M (reflectTable m)
    (by rw [← hp]; exact compatible_reflect hm) forever

#print axioms reflected_never
end BB6.Agent3UnaryGrow
