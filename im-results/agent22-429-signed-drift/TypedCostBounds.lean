import PeriodicMacroTransfer

namespace PeriodicMacro

def J : List Letter → Nat
| [] => 0
| x::xs => x.j + J xs

theorem T_lower_length (xs : List Letter) :
    3*J xs + 2*xs.length ≤ T xs := by
  induction xs with
  | nil => simp [J,T]
  | cons x xs ih =>
    simp only [J,T,List.length_cons,rankCost]
    cases x.isE <;> simp_all <;> omega

theorem T_upper_length (xs : List Letter) :
    T xs ≤ 3*J xs + 4*xs.length := by
  induction xs with
  | nil => simp [J,T]
  | cons x xs ih =>
    simp only [J,T,List.length_cons,rankCost]
    cases x.isE <;> simp_all <;> omega

theorem length_le_J (xs : List Letter)
    (hj : ∀ x : Letter, x∈xs → 0<x.j) :
    xs.length ≤ J xs := by
  induction xs with
  | nil => simp [J]
  | cons x xs ih =>
    have hx : 0<x.j := hj x (by simp)
    have ht : ∀ y : Letter, y∈xs → 0<y.j := by
      intro y hy
      exact hj y (by simp [hy])
    have hi := ih ht
    simp only [J,List.length_cons]
    omega

theorem length_add_one_le_J_of_large (xs : List Letter)
    (hj : ∀ x : Letter, x∈xs → 0<x.j)
    (hlarge : ∃ x : Letter, x∈xs ∧ 1<x.j) :
    xs.length+1 ≤ J xs := by
  induction xs with
  | nil =>
    obtain ⟨x,hx,_⟩ := hlarge
    simp at hx
  | cons x xs ih =>
    have hx : 0<x.j := hj x (by simp)
    have ht : ∀ y : Letter, y∈xs → 0<y.j := by
      intro y hy
      exact hj y (by simp [hy])
    have hlen := length_le_J xs ht
    simp only [J,List.length_cons]
    by_cases hxlarge : 1<x.j
    · omega
    · obtain ⟨y,hy,hylarge⟩ := hlarge
      have hytail : y∈xs := by
        rcases List.mem_cons.mp hy with hxy | hmem
        · rw [hxy] at hylarge
          omega
        · exact hmem
      have hi := ih ht ⟨y,hytail,hylarge⟩
      omega

theorem typed_cost_lower (x : Letter) (xs : List Letter)
    (hj : ∀ y : Letter, y∈x::xs → 0<y.j) :
    3*J (x::xs)+2 ≤ T (x::xs) := by
  have hlen : 1≤(x::xs).length := by simp
  have h := T_lower_length (x::xs)
  omega

theorem typed_cost_upper_strict (xs : List Letter)
    (hj : ∀ x : Letter, x∈xs → 0<x.j)
    (hlarge : ∃ x : Letter, x∈xs ∧ 1<x.j) :
    T xs+4 ≤ 7*J xs := by
  have hu := T_upper_length xs
  have hl := length_add_one_le_J_of_large xs hj hlarge
  omega

#print axioms typed_cost_lower
#print axioms typed_cost_upper_strict
end PeriodicMacro
