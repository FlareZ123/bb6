import Box27OrbitTree
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace BB6.Agent49.Box27Join
open BB6Coverage BB6.Agent49.Box27Slice BB6.Agent49.Box27OrbitTree
open BB6.Agent13.Box17 (decode slot)
theorem split25 (B : Nat) (p : PartialMachine) (s : Fin 12)
    (h0 : Good B (refine p (slot s) (decode 0)))
    (h1 : Good B (refine p (slot s) (decode 1)))
    (h2 : Good B (refine p (slot s) (decode 2)))
    (h3 : Good B (refine p (slot s) (decode 3)))
    (h4 : Good B (refine p (slot s) (decode 4)))
    (h5 : Good B (refine p (slot s) (decode 5)))
    (h6 : Good B (refine p (slot s) (decode 6)))
    (h7 : Good B (refine p (slot s) (decode 7)))
    (h8 : Good B (refine p (slot s) (decode 8)))
    (h9 : Good B (refine p (slot s) (decode 9)))
    (h10 : Good B (refine p (slot s) (decode 10)))
    (h11 : Good B (refine p (slot s) (decode 11)))
    (h12 : Good B (refine p (slot s) (decode 12)))
    (h13 : Good B (refine p (slot s) (decode 13)))
    (h14 : Good B (refine p (slot s) (decode 14)))
    (h15 : Good B (refine p (slot s) (decode 15)))
    (h16 : Good B (refine p (slot s) (decode 16)))
    (h17 : Good B (refine p (slot s) (decode 17)))
    (h18 : Good B (refine p (slot s) (decode 18)))
    (h19 : Good B (refine p (slot s) (decode 19)))
    (h20 : Good B (refine p (slot s) (decode 20)))
    (h21 : Good B (refine p (slot s) (decode 21)))
    (h22 : Good B (refine p (slot s) (decode 22)))
    (h23 : Good B (refine p (slot s) (decode 23)))
    (h24 : Good B (refine p (slot s) (decode 24)))
    : Good B p := by
  apply split_good B p s
  intro v
  have hv : v = 0 ∨ v = 1 ∨ v = 2 ∨ v = 3 ∨ v = 4 ∨ v = 5 ∨ v = 6 ∨ v = 7 ∨ v = 8 ∨ v = 9 ∨ v = 10 ∨ v = 11 ∨ v = 12 ∨ v = 13 ∨ v = 14 ∨ v = 15 ∨ v = 16 ∨ v = 17 ∨ v = 18 ∨ v = 19 ∨ v = 20 ∨ v = 21 ∨ v = 22 ∨ v = 23 ∨ v = 24 := by omega
  rcases hv with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
  · exact h0
  · exact h1
  · exact h2
  · exact h3
  · exact h4
  · exact h5
  · exact h6
  · exact h7
  · exact h8
  · exact h9
  · exact h10
  · exact h11
  · exact h12
  · exact h13
  · exact h14
  · exact h15
  · exact h16
  · exact h17
  · exact h18
  · exact h19
  · exact h20
  · exact h21
  · exact h22
  · exact h23
  · exact h24
theorem split21 (B : Nat) (p : PartialMachine) (s : Fin 12)
    (hc : canSplit p s = true)
    (h0 : Good B (refine p (slot s) (decode 0)))
    (h1 : Good B (refine p (slot s) (decode 1)))
    (h2 : Good B (refine p (slot s) (decode 2)))
    (h3 : Good B (refine p (slot s) (decode 3)))
    (h4 : Good B (refine p (slot s) (decode 4)))
    (h5 : Good B (refine p (slot s) (decode 5)))
    (h6 : Good B (refine p (slot s) (decode 6)))
    (h7 : Good B (refine p (slot s) (decode 7)))
    (h8 : Good B (refine p (slot s) (decode 8)))
    (h9 : Good B (refine p (slot s) (decode 9)))
    (h10 : Good B (refine p (slot s) (decode 10)))
    (h11 : Good B (refine p (slot s) (decode 11)))
    (h12 : Good B (refine p (slot s) (decode 12)))
    (h13 : Good B (refine p (slot s) (decode 13)))
    (h14 : Good B (refine p (slot s) (decode 14)))
    (h15 : Good B (refine p (slot s) (decode 15)))
    (h16 : Good B (refine p (slot s) (decode 16)))
    (h17 : Good B (refine p (slot s) (decode 17)))
    (h18 : Good B (refine p (slot s) (decode 18)))
    (h19 : Good B (refine p (slot s) (decode 19)))
    (h20 : Good B (refine p (slot s) (decode 20)))
    : Good B p := by
  apply split_ef_good B p s hc
  intro v hr
  have hle : v.val ≤ 20 := of_decide_eq_true hr
  have hv : v = 0 ∨ v = 1 ∨ v = 2 ∨ v = 3 ∨ v = 4 ∨ v = 5 ∨ v = 6 ∨ v = 7 ∨ v = 8 ∨ v = 9 ∨ v = 10 ∨ v = 11 ∨ v = 12 ∨ v = 13 ∨ v = 14 ∨ v = 15 ∨ v = 16 ∨ v = 17 ∨ v = 18 ∨ v = 19 ∨ v = 20 := by omega
  rcases hv with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
  · exact h0
  · exact h1
  · exact h2
  · exact h3
  · exact h4
  · exact h5
  · exact h6
  · exact h7
  · exact h8
  · exact h9
  · exact h10
  · exact h11
  · exact h12
  · exact h13
  · exact h14
  · exact h15
  · exact h16
  · exact h17
  · exact h18
  · exact h19
  · exact h20

#print axioms split25
#print axioms split21
end BB6.Agent49.Box27Join
