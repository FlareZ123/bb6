import SourceMacro

namespace CascadeSource

/-- Root-invariant phase language, definitionally the same predicate as
CascadeSweep.Well from SweepInvariant. -/
def WellState (a b : Nat) : Prop :=
  b=0 ∨ b=2 ∨ ∃m, a+2=4*2^m ∧ b%2=1

/-- A fully quantified, source-Cstep-checked exhaustive classification
of any predecessor within the reachable phase language. This is
particularly useful for reverse exploration of the two unresolved
fatal-gate classes. -/
theorem source_well_inverse_cases (a b u v : Nat)
  (hw : WellState a b) (he : Cstep a b = some (u,v)) :
  (b=0 ∧ u=2 ∧ v=2*a+1) ∨
  (b=2 ∧ a=0 ∧ u=2 ∧ v=0) ∨
  (b=2 ∧ 1≤a ∧ 6*a+8=4*u+v ∧ (v=0 ∨ v=2)) ∨
  (∃m, a+2=4*2^m ∧ b%2=1 ∧ 3≤b ∧
    ((u=2*a+2 ∧ b=u+v ∧ v%2=1) ∨
     (4*u+v=6*a+b+3 ∧ (v=0∨v=2) ∧ b≤2*a+1 ∧
       2^m≤u+2))) := by
  rcases hw with hb | hb | ⟨m,ha,hodd⟩
  · subst b
    simp [Cstep] at he
    rcases he with ⟨rfl,rfl⟩
    exact Or.inl ⟨rfl,rfl,rfl⟩
  · subst b
    by_cases ha0 : a=0
    · subst a
      simp [Cstep] at he
      rcases he with ⟨rfl,rfl⟩
      exact Or.inr (Or.inl ⟨rfl,rfl,rfl,rfl⟩)
    · have hapos : 1≤a := by omega
      have hd : ¬(2*a≤0) := by omega
      have he' : some ((6*a+8)/4,(6*a+8)%4)=some (u,v) := by
        simpa [Cstep,ha0,hd] using he
      have huv : u=(6*a+8)/4 ∧ v=(6*a+8)%4 := by simpa using he'.symm
      rcases huv with ⟨rfl,rfl⟩
      have hr : (6*a+8)%4=0 ∨ (6*a+8)%4=2 := by omega
      right;right;left
      refine ⟨rfl,hapos,?_,hr⟩
      omega
  · have hp : 1≤2^m := Nat.one_le_pow m 2 (by omega)
    have haeven : a%2=0 := by
      have hm : (4*2^m)%2=0 := by simp [Nat.mul_mod]
      omega
    have hapos : 2≤a := by
      have hm : 4≤4*2^m := by simpa using Nat.mul_le_mul_left 4 hp
      omega
    have hb0 : b≠0 := by omega
    have hb1 : b≠1 := by
      intro h1
      subst b
      simp [Cstep] at he
    have hb3 : 3≤b := by omega
    let d := b-2
    have hdd : d%2=1 := by dsimp [d]; omega
    by_cases hlarge : 2*a≤d
    · have he' : some (2*a+2,d-2*a)=some (u,v) := by
        simpa [Cstep,hb0,hb1,d,hlarge] using he
      have huv : u=2*a+2 ∧ v=d-2*a := by simpa using he'.symm
      rcases huv with ⟨rfl,rfl⟩
      right;right;right
      refine ⟨m,ha,hodd,hb3,Or.inl ⟨rfl,?_,?_⟩⟩
      · dsimp [d]
        omega
      · dsimp [d]
        omega
    · have ht : (6*a+d+5)%2=0 := by dsimp [d]; omega
      have hre : (6*a+d+5)%4=0 ∨ (6*a+d+5)%4=2 := by omega
      have he' : some ((6*a+d+5)/4,(6*a+d+5)%4)=some (u,v) := by
        simpa [Cstep,hb0,hb1,d,hlarge,hdd] using he
      have huv : u=(6*a+d+5)/4 ∧ v=(6*a+d+5)%4 := by simpa using he'.symm
      rcases huv with ⟨hu,hv⟩
      have hdiv : 6*a+d+5=4*u+v := by omega
      have hv2 : v=0 ∨ v=2 := by omega
      have hbelow : b≤2*a+1 := by dsimp [d] at hlarge; omega
      have hmass : 2^m≤u+2 := by
        dsimp [d] at hdiv
        omega
      right;right;right
      refine ⟨m,ha,hodd,hb3,Or.inr ⟨?_,hv2,hbelow,hmass⟩⟩
      dsimp [d] at hdiv
      omega

#print axioms source_well_inverse_cases
end CascadeSource
