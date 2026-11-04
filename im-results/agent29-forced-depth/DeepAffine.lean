import SourceBound
import Lean.Elab.Tactic.Omega

namespace BB6.Agent29Depth
open BB6.Agent3

/-- Smallest even-right input counter with exactly n possible
    affine halving operations, starting with the terminal value two. -/
def tallRight : Nat → Nat
  | 0 => 2
  | n+1 => 2 * tallRight n + 2

private theorem tallRight_ge_two (n : Nat) : 2≤tallRight n := by
  induction n with
  | zero => decide
  | succ n ih =>
    change 2 ≤ 2*tallRight n+2
    omega

private theorem tallRight_mod_four (n : Nat) : tallRight n%4=2 := by
  induction n with
  | zero => decide
  | succ n ih =>
    change (2*tallRight n+2)%4=2
    omega

/-- Exact source forced-inverse paths, with no assumptions of
    reachability from the genuine blank section seed. -/
inductive forcedChain : Nat → Nat × Nat → Nat × Nat → Prop where
  | zero (s : Nat × Nat) : forcedChain 0 s s
  | succ {n : Nat} {s t u : Nat × Nat}
      (h : forcedEdge s.1 s.2 t.1 t.2)
      (hs : forcedChain n t u) : forcedChain (n+1) s u

private theorem tallAffineStep (n x : Nat) (hx : x%4=3) :
    forcedEdge x (tallRight (n+1))
       (x+tallRight (n+1)-2) (tallRight n) := by
  have hy := tallRight_mod_four (n+1)
  have hbound : 4≤tallRight (n+1) := by
    change 4 ≤ 2*tallRight n+2
    have hh := tallRight_ge_two n
    omega
  have hright : ((tallRight (n+1)-2)/2)=tallRight n := by
    change (2*tallRight n+2-2)/2=tallRight n
    omega
  have hsum : (x+tallRight (n+1))%4=1 := by omega
  exact Or.inr (Or.inr ⟨⟨hbound,by omega,hsum⟩,rfl,hright.symm⟩)

/-- For every n there is a genuine n-step exact forced inverse chain
    of only affine A steps, all of whose initial states lie in mass
    class three. Thus no constant bound can hold for that class. -/
theorem unbounded_affine_forced_depth (n x : Nat)
    (hx : x%4=3) :
    ∃ t : Nat × Nat, forcedChain n (x,tallRight n) t := by
  induction n generalizing x with
  | zero =>
    exact ⟨(x,tallRight 0),forcedChain.zero _⟩
  | succ n ih =>
    have hx' : (x+tallRight (n+1)-2)%4=3 := by
      have hh := tallRight_mod_four (n+1)
      omega
    obtain ⟨t,ht⟩ := ih (x+tallRight (n+1)-2) hx'
    exact ⟨t, forcedChain.succ (tallAffineStep n x hx) ht⟩

theorem unbounded_mass_three_example (n : Nat) :
    (3+2*tallRight n)%4=3 ∧
      ∃ t : Nat × Nat, forcedChain n (3,tallRight n) t := by
  constructor
  · have h := tallRight_mod_four n
    omega
  · exact unbounded_affine_forced_depth n 3 (by decide)

#print axioms unbounded_affine_forced_depth
#print axioms unbounded_mass_three_example
end BB6.Agent29Depth
