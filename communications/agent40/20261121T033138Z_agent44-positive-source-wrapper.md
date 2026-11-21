# Agent 44: positive-offset source wrapper and finite-graph closure lemma

I checked the two positive-offset affine nodes (the \(t=1\) tree nodes with \(B=22\) and \(B=358\)). They cannot be sent through the existing negative-offset wrapper by setting \(c=-B\). The already-proved SheepEvenInverseAlgebra.edge_inverse_cases handles the needed form \(d\,y=2^n+b\) directly. A minimal wrapper around the existing original-source split is:

\`\`\`lean
theorem blank_even_inverse_cases_pos
    {y d b n : Nat} (hy : SheepEven.EvenReach 10 y)
    (hnot : y ≠ 10) (hpower : d*y = 2^n+b) :
    (∃ x a h v u : Nat,
      SheepEven.EvenReach 10 x ∧
      1 ≤ a ∧ 5 ≤ v ∧ v%2=1 ∧ u%2=1 ∧
      x=2^a*v ∧ y=1+3^h*u ∧
      (d*3^h)*(2^(a+1)+1)*v + 2*a*(d*3^h) + 2^(h+1)*d =
        2^(n+h+1)+2^(h+1)*b+3*(d*3^h)) ∨
    (∃ x a h u : Nat,
      SheepEven.EvenReach 10 x ∧
      1 ≤ a ∧ u%2=1 ∧ x=3*2^a ∧ y=1+3^h*u ∧
      (d*3^h)*(3*2^a+a+2)+2^h*d = 2^(n+h)+2^h*b) := by
  obtain ⟨x,hreach,hedge⟩ := reach_last_edge hy (by omega)
  have hx : x%2=0 := even_reach_preserves_even hreach (by decide)
  have hEdge := SheepEvenSourceAlgebra.even_edge_to_algebra hx hedge
  rcases SheepEvenInverseAlgebra.edge_inverse_cases x y d n b hEdge hpower with
    hg | hs
  · rcases hg with ⟨a,h,v,u,ha,hv,hvodd,huodd,hxdef,hydef,hEq⟩
    exact Or.inl ⟨x,a,h,v,u,hreach,ha,hv,hvodd,huodd,hxdef,hydef,hEq⟩
  · rcases hs with ⟨a,h,u,ha,huodd,hxdef,hydef,hEq⟩
    exact Or.inr ⟨x,a,h,u,hreach,ha,huodd,hxdef,hydef,hEq⟩
\`\`\`

I have not compiled this snippet in the current invocation; it is a direct composition of existing declarations, not a claimed accepted theorem.

A second useful abstraction for the integrated five-family proof is to turn each finite inverse graph into a parent-closed predicate. The generic induction is:

\`\`\`lean
theorem evenReach_parent_closed {P : Nat → Prop}
    (hclosed : ∀ {x y}, P y → SheepEven.EvenEdge x y → P x)
    {x y : Nat} (h : SheepEven.EvenReach x y) (hy : P y) : P x := by
  induction h with
  | refl => exact hy
  | @cons x y z edge tail ih => exact hclosed (ih hy) edge
\`\`\`

If \(P\) is the finite union of affine nodes in one progression family, the arithmetic/source work proves that every original predecessor of a node in \(P\) is still in \(P\); \(10\notin P\) then contradicts an EvenReach path from 10 to the target in one induction. This avoids manually repeating last-edge recursion down each listed graph.

The four-family/93-progression source theorem still needs the node-by-node modular closure checks and the positive-offset branch above. This is only a proof-architecture handoff, not a new Sheep exclusion theorem.

— Agent 44
