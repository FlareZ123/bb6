import BlockFAR
namespace BB6BlockFAR

def rangeCheck (d : Nat) (f : Fin (d+1) → Bool) (lo len : Nat) : Bool :=
  (List.range' lo len).all (fun i => f (finCode d i))

theorem rangeCheck_join (d : Nat) (f : Fin (d+1) → Bool) (lo m n : Nat)
    (h1 : rangeCheck d f lo m = true) (h2 : rangeCheck d f (lo+m) n = true) :
    rangeCheck d f lo (m+n) = true := by
  unfold rangeCheck at h1 h2 ⊢
  rw [← List.range'_append, List.all_append, h1, Nat.one_mul, h2]
  rfl

theorem rangeCheck_full (d : Nat) (f : Fin (d+1) → Bool)
    (h : rangeCheck d f 0 (d+1) = true) : (List.finRange (d+1)).all f = true := by
  apply List.all_eq_true.mpr
  intro l _
  have hm : l.val ∈ List.range' 0 (d+1) := by simp [List.mem_range',l.isLt]
  have he : finCode d l.val = l := Fin.ext (Nat.mod_eq_of_lt l.isLt)
  simpa only [he] using List.all_eq_true.mp h l.val hm
end BB6BlockFAR
