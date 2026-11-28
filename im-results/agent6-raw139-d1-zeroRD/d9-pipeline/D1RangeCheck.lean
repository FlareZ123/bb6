import BlockFAR2
import BlockFARBridge4

/- Generic finite-range decomposition, adapted from agent13-block-far/RangeCheck.lean. -/
namespace BB6.Agent6D1RangeCheck

def index (d i : Nat) : Fin (d+1) := ⟨i % (d+1), Nat.mod_lt _ (by omega)⟩

def check (d : Nat) (f : Fin (d+1) → Bool) (lo len : Nat) : Bool :=
  (List.range' lo len).all (fun i => f (index d i))

theorem join (d : Nat) (f : Fin (d+1) → Bool) (lo m n : Nat)
    (h1 : check d f lo m = true) (h2 : check d f (lo+m) n = true) :
    check d f lo (m+n) = true := by
  unfold check at h1 h2 ⊢
  rw [← List.range'_append, List.all_append, h1, Nat.one_mul, h2]
  rfl

theorem full (d : Nat) (f : Fin (d+1) → Bool)
    (h : check d f 0 (d+1) = true) : (List.finRange (d+1)).all f = true := by
  apply List.all_eq_true.mpr
  intro l _
  have hm : l.val ∈ List.range' 0 (d+1) := by simp [List.mem_range', l.isLt]
  have he : index d l.val = l := Fin.ext (Nat.mod_eq_of_lt l.isLt)
  simpa only [he] using List.all_eq_true.mp h l.val hm

#print axioms join
#print axioms full
end BB6.Agent6D1RangeCheck
