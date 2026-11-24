import FARSearch
import Symmetry
namespace BB6Coverage.FAR

def reflectPartial (p : PartialMachine) : PartialMachine := fun s =>
  (p s).map (Option.map reflectMove)

theorem reflectCompatible (p : PartialMachine) (m : Machine) (hm : compatible p m) :
    compatible (reflectPartial p) (reflectTable m) := by
  intro s t hs
  cases hp : p s with
  | none => simp [reflectPartial,hp] at hs
  | some tr =>
    have ht : tr.map reflectMove = t := by simpa [reflectPartial,hp] using hs
    simpa [reflectTable,hm s tr hp] using ht

theorem reflectNever (m : Machine) (h : NeverHalts (reflectTable m)) : NeverHalts m := by
  intro n
  have hn := h n
  have he : run (reflectTable m) n blank = (run m n blank).map mirrorConfig := by
    simpa only [mirror_blank] using mirror_run m blank n
  rw [he] at hn
  cases hr : run m n blank <;> simp [hr] at hn ⊢

def oracle (p : PartialMachine) (limit : Nat) : Bool :=
  (search p limit).isSome || (search (reflectPartial p) limit).isSome

theorem oracle_sound (p : PartialMachine) (limit : Nat) (h : oracle p limit = true)
    (m : Machine) (hm : compatible p m) : NeverHalts m := by
  rcases (Bool.or_eq_true _ _).mp h with hl | hr
  · exact search_sound p limit hl m hm
  · exact reflectNever m (search_sound (reflectPartial p) limit hr (reflectTable m) (reflectCompatible p m hm))

#print axioms oracle_sound
end BB6Coverage.FAR
