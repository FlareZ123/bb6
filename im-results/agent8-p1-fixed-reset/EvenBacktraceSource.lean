import PosEvenForm

namespace BB6.Agent8Zero
open BB6.Agent1

theorem even_positive_two_back_exact
    (b d : Nat) (hr : Reach b d)
    (hb : b%2=0) (hdpos : 0<d) (hdeven : d%2=0) (hnot : b≠2) :
    ∃ x y : Nat, Reach x y ∧ x%2=0 ∧ 0<y ∧ y%2=0 ∧
      b=2*x+12 ∧ y=d+x+10 := by
  cases hr with
  | init => omega
  | next a c _ _ hr h =>
      obtain ⟨ha,hc,hb',hd'⟩ :=
        even_target_parent a c b d h hb hdpos hdeven hnot
      obtain ⟨x,y,hrx,hxe,hax,hy⟩ :=
        odd_target_parent a c hr ha (by omega) (by omega)
      refine ⟨x,y,hrx,hxe,by omega,by omega,?_,?_⟩
      · omega
      · omega

#print axioms BB6.Agent8Zero.even_positive_two_back_exact
end BB6.Agent8Zero
