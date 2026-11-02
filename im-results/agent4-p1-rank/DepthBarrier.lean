import CriticalDeep
import GInverse

namespace BB6.P1Deep
open BB6.P1Reduction

/-- Depth-indexed closure from the project's two terminal leaf forms and
    a universal G-feeder rule. The actual Blocked rule has extra restrictions. -/
inductive Shallow : Nat → Nat → Nat → Prop where
  | modLeaf (fuel a c : Nat)
      (heven : a%2=0) (hpos : 0<c) (hlarge : 2<a) (hmod : a%4=2) :
      Shallow fuel a c
  | powerLeaf (fuel a c : Nat)
      (heven : a%2=0) (hpos : 0<c) (hceven : c%2=0)
      (hgap : ∀ j : Nat, a+12 ≠ 14*2^j) :
      Shallow fuel a c
  | feeder (fuel b d : Nat)
      (hchildren : ∀ k v, GAncestor b d k v → 2≤v →
        Shallow fuel (2*k-4) (v+4)) :
      Shallow (fuel+1) b d

/-- A larger depth budget preserves any certificate in the relaxed calculus. -/
theorem shallow_weaken (fuel b d : Nat) (h : Shallow fuel b d) :
    Shallow (fuel+1) b d := by
  induction h with
  | modLeaf fuel a c heven hpos hlarge hmod =>
    exact Shallow.modLeaf (fuel+1) a c heven hpos hlarge hmod
  | powerLeaf fuel a c heven hpos hceven hgap =>
    exact Shallow.powerLeaf (fuel+1) a c heven hpos hceven hgap
  | feeder fuel b d hchildren ih =>
    apply Shallow.feeder (fuel+1) b d
    intro k v hanc hv
    exact ih k v hanc hv

theorem shallow_le (cap : Nat) :
    ∀ fuel b d : Nat, fuel≤cap → Shallow fuel b d → Shallow cap b d := by
  induction cap with
  | zero =>
    intro fuel b d hle h
    have hf : fuel=0 := by omega
    simpa only [hf] using h
  | succ cap ih =>
    intro fuel b d hle h
    by_cases hf : fuel=cap+1
    · simpa only [hf] using h
    · exact shallow_weaken cap b d (ih fuel b d (by omega) h)

/-- The next corridor hub is an actual source GAncestor upper feeder. -/
theorem corridor_ancestor (L K i : Nat) (hK : 3≤K) (hi : i<L) :
    ∃ k v : Nat,
      GAncestor (left L K i) (right L K i) k v ∧
      2≤v ∧
      2*k-4 = left L K (i+1) ∧
      v+4 = right L K (i+1) := by
  let x := left L K (i+1)
  let d := right L K i
  let k := x/2+2
  let v := d+x+6
  have hp := left_positive_mod L K (i+1) hK
  have hd := right_odd L K i hK
  have hs := left_step L K i hK hi
  have hfour : 4*k+4=left L K i := by dsimp [k,x]; omega
  have hv : d+2*k+2=v := by dsimp [k,v,x]; omega
  have hk : 2*k-4=x := by dsimp [k,x]; omega
  have hr : v+4=right L K (i+1) := by
    dsimp [v,d,x]
    rw [right]
  have ha : GAncestor (left L K i) (right L K i) k v := by
    rw [←hfour,←hv]
    exact GAncestor.upper k d
  exact ⟨k,v,ha,by dsimp [v];omega,by simpa [x] using hk,hr⟩

/-- Each further predecessor hub requires another feeder proof level. -/
theorem corridor_requires_unbounded_depth (L K fuel : Nat) (hK : 3≤K) :
    ∀ i : Nat, i+fuel ≤ L → ¬Shallow fuel (left L K i) (right L K i) := by
  induction fuel with
  | zero =>
    intro i _ hb
    have hx := left_positive_mod L K i hK
    have hy := right_odd L K i hK
    cases hb with
    | modLeaf _ _ _ heven hpos hlarge hmod => omega
    | powerLeaf _ _ _ heven hpos hceven hgap => omega
  | succ fuel ih =>
    intro i hbound hb
    have hx := left_positive_mod L K i hK
    have hy := right_odd L K i hK
    cases hb with
    | modLeaf _ _ _ heven hpos hlarge hmod => omega
    | powerLeaf _ _ _ heven hpos hceven hgap => omega
    | feeder f b d hchildren =>
      obtain ⟨k,v,hanc,hv,hleft,hright⟩ := corridor_ancestor L K i hK (by omega)
      have hchild := hchildren k v hanc hv
      rw [hleft,hright] at hchild
      exact ih (i+1) (by omega) hchild

/-- No depth-L certificate in this relaxed feeder/leaf calculus can close
    the authentic critical P1 root for n=2^(L+4)-2. -/
theorem critical_no_shallow_certificate (L : Nat) :
    ¬Shallow L (14*2^(critIndex L)-2*(critIndex L)-16) 3 := by
  have h := corridor_requires_unbounded_depth (L+2) (critWeight L)
    L (crit_weight_lower L) 0 (by omega)
  have hr := critical_root_eq L
  have hright : right (L+2) (critWeight L) 0 = 3 := rfl
  simpa only [hr,hright] using h

/-- Strong form: every depth no greater than L is formally impossible. -/
theorem critical_no_shallow_up_to (L fuel : Nat) (h : fuel≤L) :
    ¬Shallow fuel (14*2^(critIndex L)-2*(critIndex L)-16) 3 := by
  intro hs
  have hw := shallow_le L fuel _ _ h hs
  exact critical_no_shallow_certificate L hw

#print axioms BB6.P1Deep.critical_no_shallow_up_to
#print axioms BB6.P1Deep.corridor_ancestor
#print axioms BB6.P1Deep.corridor_requires_unbounded_depth
#print axioms BB6.P1Deep.critical_no_shallow_certificate
end BB6.P1Deep
