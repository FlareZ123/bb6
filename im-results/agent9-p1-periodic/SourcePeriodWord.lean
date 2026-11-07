import PeriodPrimitiveFinite
import UniformPrecisionPath

namespace BB6.Agent9PeriodSource

/-- An arbitrary exact finite inverse-depth word from an authentic shadow
node is a valid continuation in the unmodified source ShadowReach relation.
This has no bound on inverse depth, word length, or original source cost. -/
theorem run_source_transport
    (L : Nat) {w : List Nat} {m z m2 z2 : Nat}
    (hr : PeriodWord.Run L w m z m2 z2) :
    ∀ root, BB6.Precision.ShadowReach L root m z →
      BB6.Precision.ShadowReach L root m2 z2 := by
  induction hr with
  | nil m z =>
      intro root hp
      exact hp
  | @cons ts m z z1 m2 z2 t v hd hn hrest ih =>
      intro root hp
      apply ih
      exact BB6.Precision.ShadowReach.step hp t v z1 hd hn

/-- An explicit finite-length upper bound for a primitive positive-depth word
on the authentic P1 feeder scalar equation. Both source feeder choices are
covered by a single theorem, since the proof is uniform in L and root. -/
theorem source_primitive_repetition_bound
    (L root : Nat) (w : List Nat) (N : Nat)
    (hp : ∃ t ∈ w, 0<t) (hprim : PeriodPrimitive.Primitive w)
    (m z : Nat → Nat)
    (hroot : BB6.Precision.ShadowReach L root (m 0) (z 0))
    (hr : ∀ n<N+1, PeriodWord.Run L w (m n) (z n)
       (m (n+1)) (z (n+1))) :
    (∀ i≤N+1, BB6.Precision.ShadowReach L root (m i) (z i)) ∧
    (2:Nat)^(PeriodWord.cost w*N) ≤
       (PeriodFinite.error (2^(PeriodWord.cost w))
        (PeriodWord.weight w:Int) (PeriodWord.cost w:Int)
        (fun n => (z n:Int)) 0).natAbs := by
  constructor
  · intro i hi
    induction i with
    | zero => exact hroot
    | succ i ih =>
        have hprev : i≤N+1 := by omega
        have hstep : i<N+1 := by omega
        exact run_source_transport L (hr i hstep) root (ih hprev)
  · exact PeriodPrimitiveFinite.primitive_finite_bound L w N hp hprim m z hr

#print axioms run_source_transport
#print axioms source_primitive_repetition_bound
end BB6.Agent9PeriodSource
