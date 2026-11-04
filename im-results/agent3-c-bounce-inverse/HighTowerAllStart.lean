import HighTowerTwoParam
import Lean.Elab.Tactic.Omega

namespace BB6.Agent3
open BB6.Agent46

private theorem tower_pull_one (start : Nat × Nat) (time x y : Nat)
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

private theorem tower_right_even (q d : Nat) : affineRight2 q d%2=0 := by
  induction d with
  | zero => change (120*q+52)%2=0; omega
  | succ d ih => change (2*affineRight2 q d+2)%2=0; omega

private theorem tower_right_large (q d : Nat) : 52≤affineRight2 q d := by
  induction d with
  | zero => change 52≤120*q+52; omega
  | succ d ih => change 52≤2*affineRight2 q d+2; omega

/-- Any trajectory reaching the tower after its d forced incoming edges
    must have visited its source-exact affine normalizer d steps earlier.
    Unlike the prior blank-origin iff, this works for ANY starting state. -/
theorem tower_pull_d (start : Nat × Nat) (q d a time : Nat)
    (ha : a%4=3)
    (h : BB6.Agent8Section.run secNext (time+d) (some start)=
      some (a,affineRight2 q d)) :
    BB6.Agent8Section.run secNext time (some start)=
      some (BB6.Agent15.affineNormalize a (affineRight2 q d)) := by
  induction d generalizing a with
  | zero =>
      have hn : ¬(4≤120*q+52 ∧ (120*q+52)%2=0 ∧ (a+(120*q+52))%4=1) := by omega
      have heq : BB6.Agent15.affineNormalize a (affineRight2 q 0)=
          (a,affineRight2 q 0) := by
        change BB6.Agent15.affineNormalize a (120*q+52)=(a,120*q+52)
        rw [BB6.Agent15.affineNormalize,dif_neg hn]
      simpa only [Nat.add_zero,heq] using h
  | succ d ih =>
      have he := tower_right_even q d
      have hl := tower_right_large q d
      have hg : 4≤affineRight2 q (d+1) ∧
          affineRight2 q (d+1)%2=0 ∧
          (a+affineRight2 q (d+1))%4=1 := by
        simp only [affineRight2]
        omega
      have ha' : (a+affineRight2 q (d+1)-2)%4=3 := by
        simp only [affineRight2]
        omega
      have hr : (affineRight2 q (d+1)-2)/2=affineRight2 q d := by
        simp only [affineRight2]
        omega
      have htop : BB6.Agent8Section.run secNext ((time+d)+1) (some start)=
          some (a,affineRight2 q (d+1)) := by
        simpa only [show time+(d+1)=(time+d)+1 by omega] using h
      have hp := tower_pull_one start (time+d) a (affineRight2 q (d+1))
        hg.1 hg.2.1 hg.2.2 htop
      rw [hr] at hp
      have hprev := ih (a+affineRight2 q (d+1)-2) ha' hp
      have heq : BB6.Agent15.affineNormalize a (affineRight2 q (d+1)) =
          BB6.Agent15.affineNormalize (a+affineRight2 q (d+1)-2) (affineRight2 q d) := by
        rw [BB6.Agent15.affineNormalize,dif_pos hg,hr]
      simpa only [heq] using hprev

/-- The d forced inverse edges are real forward section transitions.
    Every tower member has a path of exactly d steps from its normalizer. -/
theorem tower_forward_d (q d a : Nat) (ha : a%4=3) :
    BB6.Agent8Section.run secNext d
      (some (BB6.Agent15.affineNormalize a (affineRight2 q d))) =
      some (a,affineRight2 q d) := by
  induction d generalizing a with
  | zero =>
      have hn : ¬(4≤120*q+52 ∧ (120*q+52)%2=0 ∧ (a+(120*q+52))%4=1) := by omega
      have heq : BB6.Agent15.affineNormalize a (affineRight2 q 0)=
          (a,affineRight2 q 0) := by
        change BB6.Agent15.affineNormalize a (120*q+52)=(a,120*q+52)
        rw [BB6.Agent15.affineNormalize,dif_neg hn]
      simpa only [BB6.Agent8Section.run,heq]
  | succ d ih =>
      have he := tower_right_even q d
      have hl := tower_right_large q d
      have hg : 4≤affineRight2 q (d+1) ∧
          affineRight2 q (d+1)%2=0 ∧
          (a+affineRight2 q (d+1))%4=1 := by
        simp only [affineRight2]
        omega
      have ha' : (a+affineRight2 q (d+1)-2)%4=3 := by
        simp only [affineRight2]
        omega
      have hr : (affineRight2 q (d+1)-2)/2=affineRight2 q d := by
        simp only [affineRight2]
        omega
      have heq : BB6.Agent15.affineNormalize a (affineRight2 q (d+1)) =
          BB6.Agent15.affineNormalize (a+affineRight2 q (d+1)-2) (affineRight2 q d) := by
        rw [BB6.Agent15.affineNormalize,dif_pos hg,hr]
      have hstep : secNext (a+affineRight2 q (d+1)-2,affineRight2 q d)=
          some (a,affineRight2 q (d+1)) := by
        apply (BB6.Agent15.section_sum_one_even_iff_affine
          (a+affineRight2 q (d+1)-2) (affineRight2 q d)
          a (affineRight2 q (d+1)) hg.1 hg.2.1 hg.2.2).mpr
        exact ⟨rfl,hr.symm⟩
      rw [heq]
      change (BB6.Agent8Section.run secNext d
          (some (BB6.Agent15.affineNormalize
            (a+affineRight2 q (d+1)-2) (affineRight2 q d)))).bind secNext =
            some (a,affineRight2 q (d+1))
      rw [ih (a+affineRight2 q (d+1)-2) ha']
      simpa only [Option.bind_some] using hstep

/-- General sharp ancestry theorem for every source-exact affine
    tower whose normalized pair lies in the seven-four cone. -/
theorem affine_tower_general_sharp (q d a : Nat) (ha : a%4=3)
    (hc : let p := BB6.Agent15.affineNormalize a (affineRight2 q d);
      p.1%8=7 ∧ p.2%8=4 ∧ 12≤p.2) :
    (∀ (start : Nat × Nat) (time : Nat),
      BB6.Agent8Section.run secNext (time+d+2) (some start) ≠
        some (a,affineRight2 q d)) ∧
    (let p := BB6.Agent15.affineNormalize a (affineRight2 q d);
      BB6.Agent8Section.run secNext (d+1)
        (some (p.1+p.2-2,p.2/2-1))=some (a,affineRight2 q d)) := by
  constructor
  · intro start time hh
    have hp0 : BB6.Agent8Section.run secNext ((time+2)+d) (some start)=
        some (a,affineRight2 q d) := by
      simpa only [show time+2+d=time+d+2 by omega] using hh
    have hp := tower_pull_d start q d a (time+2) ha hp0
    have hp2 : BB6.Agent8Section.run secNext (time+2) (some start)=
        some ((BB6.Agent15.affineNormalize a (affineRight2 q d)).1,
              (BB6.Agent15.affineNormalize a (affineRight2 q d)).2) := by
      simpa only using hp
    exact (seven_four_no_two start time _ _ hc.1 hc.2.1 hc.2.2) hp2
  · let p := BB6.Agent15.affineNormalize a (affineRight2 q d)
    have hsource : secNext (p.1+p.2-2,p.2/2-1)=some p := by
      exact seven_four_one_witness p.1 p.2 hc.1 hc.2.1 hc.2.2
    have hfwd := tower_forward_d q d a ha
    change BB6.Agent8Section.run secNext (d+1)
      (some (p.1+p.2-2,p.2/2-1))=some (a,affineRight2 q d)
    rw [BB6.Agent8Section.run_succ_head]
    simp only [Option.bind_some,hsource]
    exact hfwd

/-- Source-exact universal ancestry upper bound: at every q,n,
    there is no trajectory from ANY starting section state entering the
    high stopping target after 4n+5 or more section transitions. -/
theorem high2_no_deeper_ancestry (start : Nat × Nat) (q n time : Nat) :
    BB6.Agent8Section.run secNext (time+(4*n+3)+2) (some start) ≠
      some (2*highJ2 q n+3,15*highJ2 q n+40) := by
  intro h
  have hj : highJ2 q n%4=2 := by
    induction n with
    | zero => change (64*q+26)%4=2; omega
    | succ n ih => change (16*highJ2 q n+42)%4=2; omega
  have ha : (2*highJ2 q n+3)%4=3 := by omega
  have hs : BB6.Agent8Section.run secNext ((time+2)+(4*n+3)) (some start)=
      some (2*highJ2 q n+3,affineRight2 q (4*n+3)) := by
    simpa only [high2_right_tower q n,show time+2+(4*n+3)=time+(4*n+3)+2 by omega] using h
  have hp := tower_pull_d start q (4*n+3) (2*highJ2 q n+3) (time+2) ha hs
  rw [high2_right_tower q n] at hp
  have hp2 : BB6.Agent8Section.run secNext (time+2) (some start)=
      some ((BB6.Agent15.affineNormalize (2*highJ2 q n+3) (15*highJ2 q n+40)).1,
            (BB6.Agent15.affineNormalize (2*highJ2 q n+3) (15*highJ2 q n+40)).2) := by
    simpa only using hp
  have hc := high2_normalized_cone q n
  exact (seven_four_no_two start time _ _ hc.1 hc.2.1 hc.2.2) hp2

/-- Sharpness: a concrete genuine predecessor chain of 4n+4 section
    transitions exists from the forbidden cone's unique direct parent.
    Therefore the unrooted maximum incoming ancestry depth is EXACT. -/
theorem high2_max_incoming_witness (q n : Nat) :
    let p := BB6.Agent15.affineNormalize
      (2*highJ2 q n+3) (15*highJ2 q n+40)
    BB6.Agent8Section.run secNext ((4*n+3)+1)
      (some (p.1+p.2-2,p.2/2-1)) =
      some (2*highJ2 q n+3,15*highJ2 q n+40) := by
  let p := BB6.Agent15.affineNormalize
      (2*highJ2 q n+3) (15*highJ2 q n+40)
  have hj : highJ2 q n%4=2 := by
    induction n with
    | zero => change (64*q+26)%4=2; omega
    | succ n ih => change (16*highJ2 q n+42)%4=2; omega
  have ha : (2*highJ2 q n+3)%4=3 := by omega
  have hc := high2_normalized_cone q n
  have hsource : secNext (p.1+p.2-2,p.2/2-1)=some p := by
    exact seven_four_one_witness p.1 p.2 hc.1 hc.2.1 hc.2.2
  have hfwd := tower_forward_d q (4*n+3) (2*highJ2 q n+3) ha
  rw [high2_right_tower q n] at hfwd
  change BB6.Agent8Section.run secNext ((4*n+3)+1)
    (some (p.1+p.2-2,p.2/2-1))=
    some (2*highJ2 q n+3,15*highJ2 q n+40)
  rw [BB6.Agent8Section.run_succ_head]
  simp only [Option.bind_some,hsource]
  exact hfwd

#print axioms tower_pull_d
#print axioms tower_forward_d
#print axioms affine_tower_general_sharp
#print axioms high2_no_deeper_ancestry
#print axioms high2_max_incoming_witness

end BB6.Agent3
