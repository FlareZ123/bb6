import GenericAffineRight
import Lean.Elab.Tactic.Omega

namespace BB6.Agent3
open BB6.Agent46

private theorem pull_one_generic (start : Nat × Nat) (time x y : Nat)
    (hy : 4≤y) (he : y%2=0) (hs : (x+y)%4=1)
    (h : BB6.Agent8Section.run secNext (time+1) (some start)=some (x,y)) :
    BB6.Agent8Section.run secNext time (some start) = some (x+y-2,(y-2)/2) := by
  cases hp : BB6.Agent8Section.run secNext time (some start) with
  | none => simp [BB6.Agent8Section.run,hp] at h
  | some p =>
      rcases p with ⟨a,k⟩
      have heq : secNext (a,k)=some (x,y) := by
        simpa [BB6.Agent8Section.run,hp] using h
      obtain ⟨ha,hk⟩ := (BB6.Agent15.section_sum_one_even_iff_affine a k x y hy he hs).mp heq
      simpa [ha,hk] using hp

private theorem gen_right_even_all (seed d : Nat) (hs : seed%4=0) : affineRightSeed seed d%2=0 := by
  induction d with
  | zero => change (seed)%2=0; omega
  | succ d ih => change (2*affineRightSeed seed d+2)%2=0; omega

private theorem gen_right_large_all (seed d : Nat) (hl : 32≤seed) : 32≤affineRightSeed seed d := by
  induction d with
  | zero => change 32≤seed; exact hl
  | succ d ih => change 32≤2*affineRightSeed seed d+2; omega

/-- All-start source-exact affine inverse pullback, for every forced depth. -/
theorem gen_right_pull_d (start : Nat × Nat) (seed d a time : Nat) (hs : seed%4=0) (hl : 32≤seed)
    (ha : a%4=3)
    (h : BB6.Agent8Section.run secNext (time+d) (some start)=
      some (a,affineRightSeed seed d)) :
    BB6.Agent8Section.run secNext time (some start)=
      some (BB6.Agent15.affineNormalize a (affineRightSeed seed d)) := by
  induction d generalizing a with
  | zero =>
      have hn : ¬(4≤seed ∧ (seed)%2=0 ∧
        (a+(seed))%4=1) := by omega
      have heq : BB6.Agent15.affineNormalize a (affineRightSeed seed 0) =
          (a,affineRightSeed seed 0) := by
        change BB6.Agent15.affineNormalize a (seed) = (a,seed)
        rw [BB6.Agent15.affineNormalize,dif_neg hn]
      simpa only [Nat.add_zero,heq] using h
  | succ d ih =>
      have he := gen_right_even_all seed d hs
      have hl := gen_right_large_all seed d hl
      have hg : 4≤affineRightSeed seed (d+1) ∧ affineRightSeed seed (d+1)%2=0 ∧
          (a+affineRightSeed seed (d+1))%4=1 := by
        simp only [affineRightSeed]
        omega
      have ha' : (a+affineRightSeed seed (d+1)-2)%4=3 := by
        simp only [affineRightSeed]
        omega
      have hr : (affineRightSeed seed (d+1)-2)/2=affineRightSeed seed d := by
        simp only [affineRightSeed]
        omega
      have htop : BB6.Agent8Section.run secNext ((time+d)+1) (some start) =
          some (a,affineRightSeed seed (d+1)) := by
        simpa only [show time+(d+1)=(time+d)+1 by omega] using h
      have hp := pull_one_generic start (time+d) a (affineRightSeed seed (d+1))
        hg.1 hg.2.1 hg.2.2 htop
      rw [hr] at hp
      have hprev := ih (a+affineRightSeed seed (d+1)-2) ha' hp
      have heq : BB6.Agent15.affineNormalize a (affineRightSeed seed (d+1)) =
          BB6.Agent15.affineNormalize (a+affineRightSeed seed (d+1)-2) (affineRightSeed seed d) := by
        rw [BB6.Agent15.affineNormalize,dif_pos hg,hr]
      simpa only [heq] using hprev

/-- Every inverse edge is real, so the d-step affine forward path exists. -/
theorem gen_right_forward_d (seed d a : Nat) (hs : seed%4=0) (hl : 32≤seed) (ha : a%4=3) :
    BB6.Agent8Section.run secNext d
      (some (BB6.Agent15.affineNormalize a (affineRightSeed seed d))) =
      some (a,affineRightSeed seed d) := by
  induction d generalizing a with
  | zero =>
      have hn : ¬(4≤seed ∧ (seed)%2=0 ∧
        (a+(seed))%4=1) := by omega
      have heq : BB6.Agent15.affineNormalize a (affineRightSeed seed 0) =
          (a,affineRightSeed seed 0) := by
        change BB6.Agent15.affineNormalize a (seed)=(a,seed)
        rw [BB6.Agent15.affineNormalize,dif_neg hn]
      simpa only [BB6.Agent8Section.run,heq]
  | succ d ih =>
      have he := gen_right_even_all seed d hs
      have hl := gen_right_large_all seed d hl
      have hg : 4≤affineRightSeed seed (d+1) ∧ affineRightSeed seed (d+1)%2=0 ∧
          (a+affineRightSeed seed (d+1))%4=1 := by
        simp only [affineRightSeed]
        omega
      have ha' : (a+affineRightSeed seed (d+1)-2)%4=3 := by
        simp only [affineRightSeed]
        omega
      have hr : (affineRightSeed seed (d+1)-2)/2=affineRightSeed seed d := by
        simp only [affineRightSeed]
        omega
      have heq : BB6.Agent15.affineNormalize a (affineRightSeed seed (d+1)) =
          BB6.Agent15.affineNormalize (a+affineRightSeed seed (d+1)-2) (affineRightSeed seed d) := by
        rw [BB6.Agent15.affineNormalize,dif_pos hg,hr]
      have hstep : secNext (a+affineRightSeed seed (d+1)-2,affineRightSeed seed d)=
          some (a,affineRightSeed seed (d+1)) := by
        apply (BB6.Agent15.section_sum_one_even_iff_affine
          (a+affineRightSeed seed (d+1)-2) (affineRightSeed seed d) a (affineRightSeed seed (d+1))
          hg.1 hg.2.1 hg.2.2).mpr
        exact ⟨rfl,hr.symm⟩
      rw [heq]
      change (BB6.Agent8Section.run secNext d
          (some (BB6.Agent15.affineNormalize
            (a+affineRightSeed seed (d+1)-2) (affineRightSeed seed d)))).bind secNext =
            some (a,affineRightSeed seed (d+1))
      rw [ih (a+affineRightSeed seed (d+1)-2) ha']
      simpa only [Option.bind_some] using hstep


#print axioms gen_right_pull_d
#print axioms gen_right_forward_d
end BB6.Agent3
