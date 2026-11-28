import Raw11Extra28AllChildren
set_option maxRecDepth 100000
set_option maxHeartbeats 0

/-!
  Source-faithful final 20-way parent join at weighted bound 158.
  No assumed totality, no missing normalized move, and no abstract
  machine-specific oracle. The twelve proof arguments are the exact
  original-table children left by Raw11Extra28AllChildren.
  This theorem is CONDITIONAL until all twelve arguments are supplied
  by locally / CI-accepted exported proofs.
-/
namespace BB6.Agent44Extra28CompleteJoin
open BB6Coverage BB6.Agent13BlankDelay BB6.Agent47PhaseFrontier
open BB6.Agent44Extra28AllChildren

private def child (w r : Bool) (q : Fin 6) : PartialMachine :=
  refine parent (3,true) (some ⟨w,r,q⟩)

structure Certificates where
  c7 : ∀ m, compatible (child true true 1) m → WeightedBound 72 m
  c8 : ∀ m, compatible (child false false 2) m → WeightedBound 42 m
  c9 : ∀ m, compatible (child false true 2) m → WeightedBound 84 m
  c10 : ∀ m, compatible (child true false 2) m → WeightedBound 101 m
  c12 : ∀ m, compatible (child false false 3) m → WeightedBound 64 m
  c13 : ∀ m, compatible (child false true 3) m → WeightedBound 79 m
  c14 : ∀ m, compatible (child true false 3) m → WeightedBound 96 m
  c15 : ∀ m, compatible (child true true 3) m → WeightedBound 119 m
  c16 : ∀ m, compatible (child false false 4) m → WeightedBound 81 m
  c17 : ∀ m, compatible (child false true 4) m → WeightedBound 150 m
  c18 : ∀ m, compatible (child true false 4) m → WeightedBound 141 m
  c19 : ∀ m, compatible (child true true 4) m → WeightedBound 158 m

private theorem raiseSafe {A B : Nat} (h : A ≤ B) {p : PartialMachine}
    (safe : ∀ m, compatible p m → WeightedBound A m) :
    ∀ m, compatible p m → WeightedBound B m :=
  fun m hm => liftBound h (safe m hm)

def completeRoute (h : Certificates) : Route 158 :=
  BB6.Agent47PhaseFrontier.split 9 (3,true) 4 #[
    (.closed (.side 10 3 false (-2))),
    (.closed (.side 15 3 false (-1))),
    (.closed (.side 10 3 false (-2))),
    (.closed (.side 14 4 true (-2))),
    (.closed (.side 4 6 false 0)),
    (.closed (.side 1 12 false 2)),
    (.closed (.side 4 6 false 0)),
    (.certified (child true true 1) (raiseSafe (B:=158) (by decide) h.c7)),
    (.certified (child false false 2) (raiseSafe (B:=158) (by decide) h.c8)),
    (.certified (child false true 2) (raiseSafe (B:=158) (by decide) h.c9)),
    (.certified (child true false 2) (raiseSafe (B:=158) (by decide) h.c10)),
    (.closed (.side 2 8 false 2)),
    (.certified (child false false 3) (raiseSafe (B:=158) (by decide) h.c12)),
    (.certified (child false true 3) (raiseSafe (B:=158) (by decide) h.c13)),
    (.certified (child true false 3) (raiseSafe (B:=158) (by decide) h.c14)),
    (.certified (child true true 3) (raiseSafe (B:=158) (by decide) h.c15)),
    (.certified (child false false 4) (raiseSafe (B:=158) (by decide) h.c16)),
    (.certified (child false true 4) (raiseSafe (B:=158) (by decide) h.c17)),
    (.certified (child true false 4) (raiseSafe (B:=158) (by decide) h.c18)),
    (.certified (child true true 4) (raiseSafe (B:=158) (by decide) h.c19))
  ]

theorem route_checked (h : Certificates) :
    check 158 parent (completeRoute h) = true := by decide +kernel

theorem no_residual (h : Certificates) :
    residuals 158 parent (completeRoute h) = [] := by decide +kernel

/-- All twelve authentic child Covers suffice, at their distinct checked
    bounds, for the entire Extra28 parent at bound 158. -/
theorem completeCover (h : Certificates) :
    Cover (WeightedBound 158) parent :=
  .leaf _ (consume 158 parent (completeRoute h) (by decide)
    (route_checked h) (by
      intro q hq
      have hn := no_residual h
      rw [hn] at hq
      simp at hq))

theorem completeCoverAt (B : Nat) (hB : 158 ≤ B) (h : Certificates) :
    Cover (WeightedBound B) parent :=
  .leaf _ (fun m hm => liftBound hB (completeCover h |>.1 m hm))

#print axioms route_checked
#print axioms no_residual
#print axioms completeCover
end BB6.Agent44Extra28CompleteJoin
