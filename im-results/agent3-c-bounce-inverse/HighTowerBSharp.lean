import HighTowerB
import Lean.Elab.Tactic.Omega

namespace BB6.Agent3
open BB6.Agent46

private theorem pull_one_B (start : Nat × Nat) (time x y : Nat)
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

private theorem rightB_even_all (q d : Nat) : rightB q d%2=0 := by
  induction d with
  | zero => change (480*q+256)%2=0; omega
  | succ d ih => change (2*rightB q d+2)%2=0; omega

private theorem rightB_large_all (q d : Nat) : 256≤rightB q d := by
  induction d with
  | zero => change 256≤480*q+256; omega
  | succ d ih => change 256≤2*rightB q d+2; omega

/-- All-start source-exact affine inverse pullback, for every forced depth. -/
theorem towerB_pull_d (start : Nat × Nat) (q d a time : Nat)
    (ha : a%4=3)
    (h : BB6.Agent8Section.run secNext (time+d) (some start)=
      some (a,rightB q d)) :
    BB6.Agent8Section.run secNext time (some start)=
      some (BB6.Agent15.affineNormalize a (rightB q d)) := by
  induction d generalizing a with
  | zero =>
      have hn : ¬(4≤480*q+256 ∧ (480*q+256)%2=0 ∧
        (a+(480*q+256))%4=1) := by omega
      have heq : BB6.Agent15.affineNormalize a (rightB q 0) =
          (a,rightB q 0) := by
        change BB6.Agent15.affineNormalize a (480*q+256) = (a,480*q+256)
        rw [BB6.Agent15.affineNormalize,dif_neg hn]
      simpa only [Nat.add_zero,heq] using h
  | succ d ih =>
      have he := rightB_even_all q d
      have hl := rightB_large_all q d
      have hg : 4≤rightB q (d+1) ∧ rightB q (d+1)%2=0 ∧
          (a+rightB q (d+1))%4=1 := by
        simp only [rightB]
        omega
      have ha' : (a+rightB q (d+1)-2)%4=3 := by
        simp only [rightB]
        omega
      have hr : (rightB q (d+1)-2)/2=rightB q d := by
        simp only [rightB]
        omega
      have htop : BB6.Agent8Section.run secNext ((time+d)+1) (some start) =
          some (a,rightB q (d+1)) := by
        simpa only [show time+(d+1)=(time+d)+1 by omega] using h
      have hp := pull_one_B start (time+d) a (rightB q (d+1))
        hg.1 hg.2.1 hg.2.2 htop
      rw [hr] at hp
      have hprev := ih (a+rightB q (d+1)-2) ha' hp
      have heq : BB6.Agent15.affineNormalize a (rightB q (d+1)) =
          BB6.Agent15.affineNormalize (a+rightB q (d+1)-2) (rightB q d) := by
        rw [BB6.Agent15.affineNormalize,dif_pos hg,hr]
      simpa only [heq] using hprev

/-- Every inverse edge is real, so the d-step affine forward path exists. -/
theorem towerB_forward_d (q d a : Nat) (ha : a%4=3) :
    BB6.Agent8Section.run secNext d
      (some (BB6.Agent15.affineNormalize a (rightB q d))) =
      some (a,rightB q d) := by
  induction d generalizing a with
  | zero =>
      have hn : ¬(4≤480*q+256 ∧ (480*q+256)%2=0 ∧
        (a+(480*q+256))%4=1) := by omega
      have heq : BB6.Agent15.affineNormalize a (rightB q 0) =
          (a,rightB q 0) := by
        change BB6.Agent15.affineNormalize a (480*q+256)=(a,480*q+256)
        rw [BB6.Agent15.affineNormalize,dif_neg hn]
      simpa only [BB6.Agent8Section.run,heq]
  | succ d ih =>
      have he := rightB_even_all q d
      have hl := rightB_large_all q d
      have hg : 4≤rightB q (d+1) ∧ rightB q (d+1)%2=0 ∧
          (a+rightB q (d+1))%4=1 := by
        simp only [rightB]
        omega
      have ha' : (a+rightB q (d+1)-2)%4=3 := by
        simp only [rightB]
        omega
      have hr : (rightB q (d+1)-2)/2=rightB q d := by
        simp only [rightB]
        omega
      have heq : BB6.Agent15.affineNormalize a (rightB q (d+1)) =
          BB6.Agent15.affineNormalize (a+rightB q (d+1)-2) (rightB q d) := by
        rw [BB6.Agent15.affineNormalize,dif_pos hg,hr]
      have hstep : secNext (a+rightB q (d+1)-2,rightB q d)=
          some (a,rightB q (d+1)) := by
        apply (BB6.Agent15.section_sum_one_even_iff_affine
          (a+rightB q (d+1)-2) (rightB q d) a (rightB q (d+1))
          hg.1 hg.2.1 hg.2.2).mpr
        exact ⟨rfl,hr.symm⟩
      rw [heq]
      change (BB6.Agent8Section.run secNext d
          (some (BB6.Agent15.affineNormalize
            (a+rightB q (d+1)-2) (rightB q d)))).bind secNext =
            some (a,rightB q (d+1))
      rw [ih (a+rightB q (d+1)-2) ha']
      simpa only [Option.bind_some] using hstep

private theorem highB_normalized_coordinates (q n : Nat) :
    ∃ u v, BB6.Agent15.affineNormalize
      (2*highJB q n+3) (15*highJB q n+40) =
        (16*u+11,32*v+32) := by
  have hc := highB_normalized_cone q n
  let p := BB6.Agent15.affineNormalize
    (2*highJB q n+3) (15*highJB q n+40)
  let u := p.1/16
  let v := (p.2-32)/32
  have h1 : p.1%16=11 := hc.1
  have h2 : p.2%32=0 := hc.2.1
  have h3 : 32≤p.2 := hc.2.2
  have hx : p.1=16*u+11 := by dsimp [u]; omega
  have hy : p.2=32*v+32 := by dsimp [v]; omega
  exact ⟨u,v,Prod.ext hx hy⟩

/-- Universal sharp upper bound: after 4n+5 or more transitions from ANY
    starting section state, the new high stopping input cannot occur. -/
theorem highB_no_deeper_ancestry (start : Nat × Nat) (q n time : Nat) :
    BB6.Agent8Section.run secNext (time+(4*n+2)+3) (some start) ≠
      some (2*highJB q n+3,15*highJB q n+40) := by
  intro hh
  have hj : highJB q n%4=2 := by
    induction n with
    | zero => change (128*q+66)%4=2; omega
    | succ n ih => change (16*highJB q n+42)%4=2; omega
  have ha : (2*highJB q n+3)%4=3 := by omega
  have hs : BB6.Agent8Section.run secNext ((time+3)+(4*n+2)) (some start)=
      some (2*highJB q n+3,rightB q (4*n+2)) := by
    simpa only [highB_right_tower q n,
      show time+3+(4*n+2)=time+(4*n+2)+3 by omega] using hh
  have hp := towerB_pull_d start q (4*n+2) (2*highJB q n+3) (time+3) ha hs
  obtain ⟨u,v,hco⟩ := highB_normalized_coordinates q n
  rw [highB_right_tower q n,hco] at hp
  exact (child_B_no_three start time u v) hp

/-- Construct the matching longest genuine incoming path of 4n+4 steps
    from an explicitly given (generally nonblank) section start. -/
theorem highB_max_incoming_witness (q n : Nat) :
    ∃ start : Nat × Nat,
      BB6.Agent8Section.run secNext ((4*n+2)+2) (some start) =
        some (2*highJB q n+3,15*highJB q n+40) := by
  have hj : highJB q n%4=2 := by
    induction n with
    | zero => change (128*q+66)%4=2; omega
    | succ n ih => change (16*highJB q n+42)%4=2; omega
  have ha : (2*highJB q n+3)%4=3 := by omega
  obtain ⟨u,v,hco⟩ := highB_normalized_coordinates q n
  let s := (8*u+24*v+26,4*u+20*v+19)
  refine ⟨s,?_⟩
  have hs : BB6.Agent8Section.run secNext 2 (some s)=
      some (16*u+11,32*v+32) := child_B_two_witness u v
  have hf := towerB_forward_d q (4*n+2) (2*highJB q n+3) ha
  rw [highB_right_tower q n] at hf
  rw [hco] at hf
  rw [show (4*n+2)+2=2+(4*n+2) by omega,
    BB6.Agent8Section.run_add,hs]
  exact hf

#print axioms towerB_pull_d
#print axioms towerB_forward_d
#print axioms highB_no_deeper_ancestry
#print axioms highB_max_incoming_witness
end BB6.Agent3
