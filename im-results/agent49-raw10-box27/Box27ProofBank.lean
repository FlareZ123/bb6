import Box27Symmetry
import Box27SliceCore
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace BB6.Agent49.Box27ProofBank
open BB6Coverage BB6.Agent13BlankDelay BB6.Agent49.Box27Slice
open BB6.Agent49.Box27Symmetry BB6.Agent16WeightedSymmetry

structure Certified (B : Nat) where
  p : PartialMachine
  good : Good B p

def fromNever (B : Nat) (p : PartialMachine) (h : ∀ m, compatible p m → NeverHalts m) : Certified B :=
  ⟨p,fun m hm => weighted_of_never B m (h m hm)⟩

theorem renameTwice (p : PartialMachine) : renamePartial ef (renamePartial ef p) = p := by
  funext s
  rcases s with ⟨q,b⟩
  unfold renamePartial
  change ((p (efState (efState q),b)).map (fun t => t.map (renameMove ef))).map (fun t => t.map (renameMove ef)) = _
  rw [ef_involutive]
  cases h : p (q,b) with
  | none => rfl
  | some t =>
    cases t with
    | none => rfl
    | some mv =>
      rcases mv with ⟨w,r,k⟩
      simp only [Option.map_some,renameMove,ef,ef_involutive]

def conjugate (B : Nat) (c : Certified B) : Certified B :=
  ⟨renamePartial ef c.p, weighted_cover_transport B ef (by decide) (renameTwice c.p) c.good⟩

def tables (B : Nat) (bank : Array (Certified B)) : Array PartialMachine := bank.map (·.p)
theorem tables_good (B : Nat) (bank : Array (Certified B)) (i : Nat) (q : PartialMachine)
    (h : (tables B bank)[i]? = some q) : Good B q := by
  unfold tables at h
  rw [Array.getElem?_map] at h
  cases hc : bank[i]? with
  | none => simp [hc] at h
  | some c =>
    have he : c.p=q := Option.some.inj (by simpa [hc] using h)
    rw [← he]
    exact c.good

#print axioms renameTwice
#print axioms conjugate
#print axioms tables_good
end BB6.Agent49.Box27ProofBank
