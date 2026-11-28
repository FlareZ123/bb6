import PeriodicMacroTransfer

/-!
The exact transfer coefficient cone for positive exponent signed E/S pair words.
Paper strict extension when some exponent exceeds one is separate.
-/
namespace PeriodicMacro

/-- Recursive nonnegative coefficient gap, the finite strict-cone
    invariant. This is the weighted prefix sum of 4^j-4. -/
def coefficientGap : List Letter → Nat
| [] => 0
| x::xs => (scale x-4)+scale x*coefficientGap xs

theorem coefficient_gap_identity (xs : List Letter)
    (hj : ∀ x : Letter, x∈xs → 0<x.j) :
    M xs = 3*A xs+1+coefficientGap xs := by
  induction xs with
  | nil => simp [M,A,coefficientGap]
  | cons x xs ih =>
    have hx : 0<x.j := hj x (by simp)
    have htail : ∀ y : Letter, y∈xs → 0<y.j := by
      intro y hy
      exact hj y (by simp [hy])
    have hi := ih htail
    have hs : 4≤scale x := scale_ge_four x hx
    have hscale : scale x=(scale x-4)+4 := by omega
    change scale x*M xs =
      3*(1+scale x*A xs)+1+
        ((scale x-4)+scale x*coefficientGap xs)
    rw [hi]
    grind

theorem coefficient_weak_cone (xs : List Letter)
    (hj : ∀ x : Letter, x∈xs → 0<x.j) :
    3*A xs+1 ≤ M xs := by
  induction xs with
  | nil => simp [A,M]
  | cons x xs ih =>
    have hx : 0<x.j := hj x (by simp)
    have htail : ∀ y : Letter, y∈xs → 0<y.j := by
      intro y hy
      exact hj y (by simp [hy])
    have ht := ih htail
    have hs : 4≤scale x := scale_ge_four x hx
    have hm := Nat.mul_le_mul_left (scale x) ht
    simp only [A,M]
    have heq : 3*(1+scale x*A xs)+1 =
        4+scale x*(3*A xs) := by grind
    rw [heq]
    have hr : 4+scale x*(3*A xs) ≤
        scale x*(3*A xs+1) := by
      have hd : scale x*(3*A xs+1) =
          scale x*(3*A xs)+scale x := by grind
      rw [hd]
      omega
    omega

theorem scale_gt_four (x : Letter) (hj : 1<x.j) :
    4<scale x := by
  cases h : x.j with
  | zero => omega
  | succ n =>
    cases n with
    | zero => omega
    | succ m =>
      have hp : 0<4^m := Nat.pow_pos (by omega)
      unfold scale
      rw [h]
      simp only [Nat.pow_succ]
      omega

/-- Strict transfer coefficient cone as soon as any pair macro contains
    a positive F-run (j>1). The finite slope consequence is 3*s<T. -/
theorem coefficient_strict_cone (xs : List Letter)
    (hj : ∀ x : Letter, x∈xs → 0<x.j)
    (hlarge : ∃ x : Letter, x∈xs ∧ 1<x.j) :
    3*A xs+1<M xs := by
  induction xs with
  | nil =>
    obtain ⟨x,hx,_⟩ := hlarge
    simp at hx
  | cons x xs ih =>
    have hx : 0<x.j := hj x (by simp)
    have htail : ∀ y : Letter, y∈xs → 0<y.j := by
      intro y hy
      exact hj y (by simp [hy])
    have hweak := coefficient_weak_cone xs htail
    have hs : 4≤scale x := scale_ge_four x hx
    have heq : 3*(1+scale x*A xs)+1 =
        4+scale x*(3*A xs) := by grind
    have hdist : scale x*(3*A xs+1) =
        scale x*(3*A xs)+scale x := by grind
    by_cases hhead : 1<x.j
    · have hsstrict := scale_gt_four x hhead
      have hmul := Nat.mul_le_mul_left (scale x) hweak
      have hc : 4+scale x*(3*A xs) <
          scale x*(3*A xs+1) := by
        rw [hdist]
        omega
      simp only [A,M]
      rw [heq]
      omega
    · obtain ⟨y,hy,hylarge⟩ := hlarge
      have hiny : y∈xs := by
        have hh : y=x ∨ y∈xs := List.mem_cons.mp hy
        cases hh with
        | inl he =>
          rw [he] at hylarge
          omega
        | inr he => exact he
      have hstrict := ih htail ⟨y,hiny,hylarge⟩
      have hmul :=
        Nat.mul_lt_mul_of_pos_left hstrict (scale_pos x)
      have hc : 4+scale x*(3*A xs) ≤
          scale x*(3*A xs+1) := by
        rw [hdist]
        omega
      simp only [A,M]
      rw [heq]
      omega

#print axioms coefficient_gap_identity
#print axioms coefficient_weak_cone
#print axioms coefficient_strict_cone
end PeriodicMacro
