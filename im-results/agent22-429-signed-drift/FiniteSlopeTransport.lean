import PeriodicMacroTransfer

namespace PeriodicMacro

inductive SlopeWalk (K : Nat) : List Letter → Nat → Nat → Prop where
  | nil (d : Nat) : SlopeWalk K [] d d
  | cons {x : Letter} {xs : List Letter} {d e f : Nat}
      (head : scale x*e=d+K) (tail : SlopeWalk K xs e f) :
      SlopeWalk K (x::xs) d f

theorem parallel_step_slope {x : Letter}
    {u r v s u' r' v' s' d K : Nat}
    (h : Step x u r v s) (h' : Step x u' r' v' s')
    (hu : u'=u+d) (hr : r'=r+K) :
    ∃ e : Nat, v'=v+e ∧ s'=s+K ∧ scale x*e=d+K := by
  rcases h with ⟨hv,hs⟩
  rcases h' with ⟨hv',hs'⟩
  have hp := scale_pos x
  have hle : v≤v' := by
    by_cases hle0 : v≤v'
    · exact hle0
    · have hlt : v'<v := by omega
      have hm := Nat.mul_lt_mul_of_pos_left hlt hp
      rw [hv,hv'] at hm
      omega
  let e := v'-v
  have he : v'=v+e := by dsimp [e]; omega
  refine ⟨e,he,?_,?_⟩
  · omega
  · rw [he] at hv'
    rw [Nat.mul_add] at hv'
    omega

theorem parallel_walk_slope {xs : List Letter}
    {u r U R u' r' U' R' d K : Nat}
    (h : Walk xs u r U R) (h' : Walk xs u' r' U' R')
    (hu : u'=u+d) (hr : r'=r+K) :
    ∃ e : Nat, U'=U+e ∧ R'=R+K ∧ SlopeWalk K xs d e := by
  induction h generalizing u' r' U' R' d with
  | nil u r =>
      cases h'
      exact ⟨d,hu,hr,SlopeWalk.nil d⟩
  | @cons x xs u r v s U R hx tail ih =>
      cases h' with
      | @cons _ _ _ _ v' s' _ _ hx' tail' =>
          obtain ⟨e,he,hs,hstep⟩ := parallel_step_slope hx hx' hu hr
          obtain ⟨f,hU,hR,hTail⟩ := ih tail' he hs
          exact ⟨f,hU,hR,SlopeWalk.cons hstep hTail⟩

#print axioms parallel_step_slope
#print axioms parallel_walk_slope
end PeriodicMacro
