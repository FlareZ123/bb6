import CSixSeventhArithmetic
import CAltSixthStrict
import Lean.Elab.Tactic.Omega

namespace BB6.Agent4Seven
open BB6.Agent46

/-- A point lies in the image of n consecutive original-section returns. -/
def Incoming : Nat → Nat × Nat → Prop
  | 0, _ => True
  | n+1, p => ∃ q, Incoming n q ∧ secNext q = some p

private theorem incoming_drop (n : Nat) (p : Nat × Nat) :
    Incoming (n+1) p → Incoming n p := by
  induction n generalizing p with
  | zero => simp [Incoming]
  | succ n ih =>
      rintro ⟨q,hq,hedge⟩
      exact ⟨q,ih q hq,hedge⟩

private theorem no_two_P3 (u v : Nat) :
    ¬ Incoming 2 (921+544*u+1056*v,424+240*u+496*v) := by
  rintro ⟨⟨a,b⟩,⟨⟨c,d⟩,_,h0⟩,h1⟩
  exact BB6.Agent34Three.all_source_no_two_new c d a b
    (921+544*u+1056*v) (424+240*u+496*v)
    (by omega) (Or.inl (by omega)) h0 h1

private theorem no_two_R (u v : Nat) (hpair : (u+v)%4=0) :
    ¬ Incoming 2 (471+276*u+548*v,644+374*u+750*v) := by
  rintro ⟨⟨a,b⟩,⟨⟨c,d⟩,_,h0⟩,h1⟩
  exact BB6.Agent34Three.all_source_no_two_new c d a b
    (471+276*u+548*v) (644+374*u+750*v)
    (by omega) (Or.inr (by omega)) h0 h1

private theorem no_one_P0 (u v : Nat) :
    ¬ Incoming 1 (518+320*u+576*v,627+352*u+736*v) := by
  rintro ⟨⟨a,b⟩,_,hedge⟩
  have hr := BB6.Agent3.section_odd_image a b
    (518+320*u+576*v) (627+352*u+736*v)
    hedge (by omega) (by omega)
  omega

private theorem no_three_P2 (u v : Nat) (hpair : (u+v)%4=0) :
    ¬ Incoming 3 (128+80*u+144*v,819+472*u+952*v) := by
  rintro ⟨⟨a,k⟩,h2,hstep⟩
  have hinv : sectionPreimageAll a k _ _ :=
    (section_preimage_all_iff a k _ _).mp hstep
  obtain ⟨ha,hk⟩ := high_two_unique a k u v hinv
  rw [ha,hk] at h2
  exact no_two_R u v hpair h2

private theorem no_four_H1 (u v : Nat) (hpair : (u+v)%4=0) :
    ¬ Incoming 4 (301+256*u+256*v,739+384*u+896*v) := by
  rintro ⟨⟨a,k⟩,h3,hstep⟩
  have hinv : sectionPreimageAll a k _ _ :=
    (section_preimage_all_iff a k _ _).mp hstep
  rcases high_one_two_parents a k u v hinv with hp|hq
  · rw [hp.1,hp.2] at h3
    exact no_one_P0 u v (incoming_drop 1 _ (incoming_drop 2 _ h3))
  · rw [hq.1,hq.2] at h3
    exact no_three_P2 u v hpair h3

private theorem no_three_H3 (u v : Nat) :
    ¬ Incoming 3 (73+64*u+64*v,850+480*u+992*v) := by
  rintro ⟨⟨a,k⟩,h2,hstep⟩
  have hinv : sectionPreimageAll a k _ _ :=
    (section_preimage_all_iff a k _ _).mp hstep
  obtain ⟨ha,hk⟩ := BB6.Agent34Three.only_direct a k
    (73+64*u+64*v) (850+480*u+992*v)
    (by omega) (by omega) (Or.inr (by omega)) hinv
  have hx : a=921+544*u+1056*v := by omega
  have hy : k=424+240*u+496*v := by omega
  rw [hx,hy] at h2
  exact no_two_P3 u v h2

private theorem no_six_D (u v : Nat) :
    ¬ Incoming 6 (1213+1024*u+1024*v,286+512*v) := by
  rintro ⟨⟨i,j⟩,⟨⟨g,h⟩,⟨⟨e,f⟩,⟨⟨c,d⟩,⟨⟨a,b⟩,⟨⟨z,w⟩,_,h0⟩,h1⟩,h2⟩,h3⟩,h4⟩,h5⟩
  let r : Nat := 18+16*u+16*v
  let t : Nat := 2+4*v
  have hx : 64*r+61=1213+1024*u+1024*v := by dsimp [r]; omega
  have hy : 128*t+30=286+512*v := by dsimp [t]; omega
  rw [←hx,←hy] at h5
  exact BB6.Agent4Five.six_edges_impossible r t z w a b c d e f g h i j
    (by dsimp [t]; omega) (by dsimp [r,t]; omega)
    h0 h1 h2 h3 h4 h5

/-- No seven original-source returns enter the new 1 mod 4 first-counter band. -/
theorem no_seven_incoming (u v : Nat) (hpair : (u+v)%4=0) :
    ¬ Incoming 7 (641+1024*u,574+1024*v) := by
  rintro ⟨⟨a,k⟩,h6,hstep⟩
  have hinv : sectionPreimageAll a k _ _ :=
    (section_preimage_all_iff a k _ _).mp hstep
  rcases target_three_parents a k u v hinv with hd|hh|hj
  · rw [hd.1,hd.2] at h6
    exact no_six_D u v h6
  · rw [hh.1,hh.2] at h6
    exact no_four_H1 u v hpair (incoming_drop 4 _ (incoming_drop 5 _ h6))
  · rw [hj.1,hj.2] at h6
    exact no_three_H3 u v (incoming_drop 3 _ (incoming_drop 4 _ (incoming_drop 5 _ h6)))

/-- Every state in this band admits six genuine source-return predecessors. -/
theorem six_incoming_exist (u v : Nat) :
    Incoming 6 (641+1024*u,574+1024*v) := by
  let r : Nat := 18+16*u+16*v
  let t : Nat := 2+4*v
  obtain ⟨a0,b0,a1,b1,a2,b2,a3,b3,a4,b4,h0,h1,h2,h3,h4⟩ :=
    BB6.Agent4Five.five_edges_exist r t (by dsimp [t]; omega)
  have hlast : secNext (64*r+61,128*t+30) =
      some (641+1024*u,574+1024*v) := by
    have he := BB6.Agent34ThreeProper.direct_predecessor
      (641+1024*u) (574+1024*v) (by omega) (by omega)
    have hpx : 641+1024*u+(574+1024*v)-2 = 64*r+61 := by dsimp [r]; omega
    have hpy : (574+1024*v-2)/2 = 128*t+30 := by dsimp [t]; omega
    rw [hpx,hpy] at he
    exact he
  exact ⟨(64*r+61,128*t+30),
    ⟨(a4,b4),⟨(a3,b3),⟨(a2,b2),⟨(a1,b1),⟨(a0,b0),trivial,h0⟩,h1⟩,h2⟩,h3⟩,h4⟩,
    hlast⟩

/-- Strict sixth-return image, outside the seventh, for every u,v. -/
theorem exactly_six_not_seven (u v : Nat) (hpair : (u+v)%4=0) :
    Incoming 6 (641+1024*u,574+1024*v) ∧
    ¬ Incoming 7 (641+1024*u,574+1024*v) :=
  ⟨six_incoming_exist u v, no_seven_incoming u v hpair⟩

#print axioms exactly_six_not_seven
end BB6.Agent4Seven
