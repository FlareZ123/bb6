import Std
import Lean.Elab.Tactic.Omega

namespace BB6.Agent47Direct

inductive Chain (f : Nat × Nat → Option (Nat × Nat)) :
    Nat → (Nat × Nat) → (Nat × Nat) → Prop where
  | refl (s : Nat × Nat) : Chain f 0 s s
  | snoc (n : Nat) (s t u : Nat × Nat) :
      Chain f n s t → f t = some u → Chain f (n+1) s u

/-- A general lower bound on inverse depth from a direct transition branch. -/
theorem abstract_long_chain (f : Nat × Nat → Option (Nat × Nat))
    (hdir : ∀ x k : Nat, 0 < k → f (x + 2*k,k) = some (x,2*k+2))
    (r u x : Nat) (hu : 4 ≤ u) :
    ∃ s, Chain f r s (x,2^r*u-2) := by
  induction r generalizing x with
  | zero =>
      refine ⟨(x,u-2),?_⟩
      simpa using Chain.refl (f:=f) (x,u-2)
  | succ r ih =>
      let y := 2^r*u-2
      have hpow : 1 ≤ 2^r := by
        have hh : 0 < (2:Nat)^r := Nat.pow_pos (by decide)
        omega
      have hle := Nat.mul_le_mul_right u hpow
      have hle2 : u ≤ 2^r*u := by simpa using hle
      have hmul : 4 ≤ 2^r*u := by omega
      have hy : 0 < y := by dsimp [y]; omega
      obtain ⟨s,hs⟩ := ih (x+2*y)
      have hp : 2^(r+1)*u = 2*(2^r*u) := by
        rw [Nat.pow_succ]
        ac_rfl
      have hq : y+2 = 2^r*u := Nat.sub_add_cancel (by omega : 2 ≤ 2^r*u)
      have hgoal : 2^(r+1)*u-2 = 2*y+2 := by omega
      refine ⟨s,?_⟩
      simpa only [← hgoal] using
        (Chain.snoc (f:=f) r s (x+2*y,y) (x,2*y+2) hs (hdir x y hy))

end BB6.Agent47Direct
