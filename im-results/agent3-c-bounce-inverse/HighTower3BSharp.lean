import HighTower3B
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

private theorem right3B_even_all (q d : Nat) : right3B q d%2=0 := by
  induction d with
  | zero => change (8160*q+7360)%2=0; omega
  | succ d ih => change (2*right3B q d+2)%2=0; omega

private theorem right3B_large_all (q d : Nat) : 7360≤right3B q d := by
  induction d with
  | zero => change 7360≤8160*q+7360; omega
  | succ d ih => change 7360≤2*right3B q d+2; omega

/-- All-start source-exact affine inverse pullback, for every forced depth. -/
theorem tower3B_pull_d (start : Nat × Nat) (q d a time : Nat)
    (ha : a%4=3)
    (h : BB6.Agent8Section.run secNext (time+d) (some start)=
      some (a,right3B q d)) :
    BB6.Agent8Section.run secNext time (some start)=
      some (BB6.Agent15.affineNormalize a (right3B q d)) := by
  induction d generalizing a with
  | zero =>
      have hn : ¬(4≤8160*q+7360 ∧ (8160*q+7360)%2=0 ∧
        (a+(8160*q+7360))%4=1) := by omega
      have heq : BB6.Agent15.affineNormalize a (right3B q 0) =
          (a,right3B q 0) := by
        change BB6.Agent15.affineNormalize a (8160*q+7360) = (a,8160*q+7360)
        rw [BB6.Agent15.affineNormalize,dif_neg hn]
      simpa only [Nat.add_zero,heq] using h
  | succ d ih =>
      have he := right3B_even_all q d
      have hl := right3B_large_all q d
      have hg : 4≤right3B q (d+1) ∧ right3B q (d+1)%2=0 ∧
          (a+right3B q (d+1))%4=1 := by
        simp only [right3B]
        omega
      have ha' : (a+right3B q (d+1)-2)%4=3 := by
        simp only [right3B]
        omega
      have hr : (right3B q (d+1)-2)/2=right3B q d := by
        simp only [right3B]
        omega
      have htop : BB6.Agent8Section.run secNext ((time+d)+1) (some start) =
          some (a,right3B q (d+1)) := by
        simpa only [show time+(d+1)=(time+d)+1 by omega] using h
      have hp := pull_one_B start (time+d) a (right3B q (d+1))
        hg.1 hg.2.1 hg.2.2 htop
      rw [hr] at hp
      have hprev := ih (a+right3B q (d+1)-2) ha' hp
      have heq : BB6.Agent15.affineNormalize a (right3B q (d+1)) =
          BB6.Agent15.affineNormalize (a+right3B q (d+1)-2) (right3B q d) := by
        rw [BB6.Agent15.affineNormalize,dif_pos hg,hr]
      simpa only [heq] using hprev

/-- Every inverse edge is real, so the d-step affine forward path exists. -/
theorem tower3B_forward_d (q d a : Nat) (ha : a%4=3) :
    BB6.Agent8Section.run secNext d
      (some (BB6.Agent15.affineNormalize a (right3B q d))) =
      some (a,right3B q d) := by
  induction d generalizing a with
  | zero =>
      have hn : ¬(4≤8160*q+7360 ∧ (8160*q+7360)%2=0 ∧
        (a+(8160*q+7360))%4=1) := by omega
      have heq : BB6.Agent15.affineNormalize a (right3B q 0) =
          (a,right3B q 0) := by
        change BB6.Agent15.affineNormalize a (8160*q+7360)=(a,8160*q+7360)
        rw [BB6.Agent15.affineNormalize,dif_neg hn]
      simpa only [BB6.Agent8Section.run,heq]
  | succ d ih =>
      have he := right3B_even_all q d
      have hl := right3B_large_all q d
      have hg : 4≤right3B q (d+1) ∧ right3B q (d+1)%2=0 ∧
          (a+right3B q (d+1))%4=1 := by
        simp only [right3B]
        omega
      have ha' : (a+right3B q (d+1)-2)%4=3 := by
        simp only [right3B]
        omega
      have hr : (right3B q (d+1)-2)/2=right3B q d := by
        simp only [right3B]
        omega
      have heq : BB6.Agent15.affineNormalize a (right3B q (d+1)) =
          BB6.Agent15.affineNormalize (a+right3B q (d+1)-2) (right3B q d) := by
        rw [BB6.Agent15.affineNormalize,dif_pos hg,hr]
      have hstep : secNext (a+right3B q (d+1)-2,right3B q d)=
          some (a,right3B q (d+1)) := by
        apply (BB6.Agent15.section_sum_one_even_iff_affine
          (a+right3B q (d+1)-2) (right3B q d) a (right3B q (d+1))
          hg.1 hg.2.1 hg.2.2).mpr
        exact ⟨rfl,hr.symm⟩
      rw [heq]
      change (BB6.Agent8Section.run secNext d
          (some (BB6.Agent15.affineNormalize
            (a+right3B q (d+1)-2) (right3B q d)))).bind secNext =
            some (a,right3B q (d+1))
      rw [ih (a+right3B q (d+1)-2) ha']
      simpa only [Option.bind_some] using hstep

private theorem high3B_normalized_coordinates (q n : Nat) :
    ∃ u v, BB6.Agent15.affineNormalize
      (2*highJ3B q n+3) (255*highJ3B q n+754) =
        (16*u+11,32*v+32) := by
  have hc := high3B_normalized_cone q n
  let p := BB6.Agent15.affineNormalize
    (2*highJ3B q n+3) (255*highJ3B q n+754)
  let u := p.1/16
  let v := (p.2-32)/32
  have h1 : p.1%16=11 := hc.1
  have h2 : p.2%32=0 := hc.2.1
  have h3 : 32≤p.2 := hc.2.2
  have hx : p.1=16*u+11 := by dsimp [u]; omega
  have hy : p.2=32*v+32 := by dsimp [v]; omega
  exact ⟨u,v,Prod.ext hx hy⟩

/-- Universal sharp upper bound: after 8n+6 or more transitions from ANY
    starting section state, the new high stopping input cannot occur. -/
theorem high3B_no_deeper_ancestry (start : Nat × Nat) (q n time : Nat) :
    BB6.Agent8Section.run secNext (time+(8*n+3)+3) (some start) ≠
      some (2*highJ3B q n+3,255*highJ3B q n+754) := by
  intro hh
  have hj : highJ3B q n%4=0 := by
    induction n with
    | zero => change (256*q+228)%4=0; omega
    | succ n ih => change (256*highJ3B q n+756)%4=0; omega
  have ha : (2*highJ3B q n+3)%4=3 := by omega
  have hs : BB6.Agent8Section.run secNext ((time+3)+(8*n+3)) (some start)=
      some (2*highJ3B q n+3,right3B q (8*n+3)) := by
    simpa only [high3B_right_tower q n,
      show time+3+(8*n+3)=time+(8*n+3)+3 by omega] using hh
  have hp := tower3B_pull_d start q (8*n+3) (2*highJ3B q n+3) (time+3) ha hs
  obtain ⟨u,v,hco⟩ := high3B_normalized_coordinates q n
  rw [high3B_right_tower q n,hco] at hp
  exact (child_B_no_three start time u v) hp

/-- Construct the matching longest genuine incoming path of 8n+5 steps
    from an explicitly given (generally nonblank) section start. -/
theorem high3B_max_incoming_witness (q n : Nat) :
    ∃ start : Nat × Nat,
      BB6.Agent8Section.run secNext ((8*n+3)+2) (some start) =
        some (2*highJ3B q n+3,255*highJ3B q n+754) := by
  have hj : highJ3B q n%4=0 := by
    induction n with
    | zero => change (256*q+228)%4=0; omega
    | succ n ih => change (256*highJ3B q n+756)%4=0; omega
  have ha : (2*highJ3B q n+3)%4=3 := by omega
  obtain ⟨u,v,hco⟩ := high3B_normalized_coordinates q n
  let s := (8*u+24*v+26,4*u+20*v+19)
  refine ⟨s,?_⟩
  have hs : BB6.Agent8Section.run secNext 2 (some s)=
      some (16*u+11,32*v+32) := child_B_two_witness u v
  have hf := tower3B_forward_d q (8*n+3) (2*highJ3B q n+3) ha
  rw [high3B_right_tower q n] at hf
  rw [hco] at hf
  rw [show (8*n+3)+2=2+(8*n+3) by omega,
    BB6.Agent8Section.run_add,hs]
  exact hf

#print axioms tower3B_pull_d
#print axioms tower3B_forward_d
#print axioms high3B_no_deeper_ancestry
#print axioms high3B_max_incoming_witness
end BB6.Agent3
