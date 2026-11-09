import Std

namespace BB6.Agent9CrossFeeder

/-- Every positive natural number has a unique odd part after removing a
power of two (existence suffices for the source theorem). -/
theorem natural_odd_factor (n : Nat) (hn : 0<n) :
    ∃ (e k : Nat), k%2=1 ∧ n=2^e*k := by
  induction n using Nat.strongRecOn with
  | ind n ih =>
      by_cases hod : n%2=1
      · refine ⟨0,n,hod,?_⟩
        simp
      · have hmod : n%2=0 := by omega
        let m := n/2
        have hmEq : 2*m=n := by dsimp [m]; omega
        have hmpos : 0<m := by dsimp [m]; omega
        have hmlt : m<n := by dsimp [m]; omega
        obtain ⟨e,k,hodd,heq⟩ := ih m hmlt hmpos
        refine ⟨e+1,k,hodd,?_⟩
        have hh : n=2*(2^e*k) := by rw [← hmEq,heq]
        rw [hh]
        simp only [Nat.pow_succ]
        ac_rfl

/-- Every nonzero integer is a dyadic power times an odd integer, including
negative offsets. -/
theorem integer_odd_factor (C : Int) (hne : C≠0) :
    ∃ (e : Nat) (B : Int), B%2=1 ∧ C=(2:Int)^e*B := by
  have habs : 0<C.natAbs := Int.natAbs_pos.mpr hne
  obtain ⟨e,k,hodd,heq⟩ := natural_odd_factor C.natAbs habs
  have hCast : (C.natAbs:Int)=(2:Int)^e*(k:Int) := by
    exact_mod_cast heq
  rcases Int.natAbs_eq C with hpos | hneg
  · refine ⟨e,(k:Int),?_,?_⟩
    · exact_mod_cast hodd
    · omega
  · refine ⟨e,-(k:Int),?_,?_⟩
    · have hmod : (k:Int)%2=1 := by exact_mod_cast hodd
      omega
    · rw [hneg] at hCast
      have he : -((2:Int)^e*(k:Int))=(2:Int)^e*(-(k:Int)) := by
        simp [Int.mul_neg]
      omega

#print axioms natural_odd_factor
#print axioms integer_odd_factor
end BB6.Agent9CrossFeeder
