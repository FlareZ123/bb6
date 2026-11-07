import PeriodPrimitiveFinite
import PeriodAllPeriods
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


/-- A repeated finite block preserves original-source reachability at every
    boundary after any reachable starting index. -/
theorem source_periodic_tail_boundaries_reachable
    (L root N : Nat) (w : List Nat) (m z : Nat → Nat)
    (hroot : BB6.Precision.ShadowReach L root (m N) (z N))
    (hr : ∀ n, PeriodWord.Run L w (m (N+n)) (z (N+n))
      (m (N+(n+1))) (z (N+(n+1)))) :
    ∀ n, BB6.Precision.ShadowReach L root (m (N+n)) (z (N+n)) := by
  intro n
  induction n with
  | zero => simpa using hroot
  | succ n ih =>
      exact run_source_transport L (hr n) root ih

/-- The arbitrary-word theorem excludes every eventually periodic
    positive-depth inverse tail in the original P1 scalar shadow. -/
theorem source_no_eventually_periodic_positive_depth_ray
    (L : Nat) (w : List Nat) (N : Nat)
    (hp : ∃ t ∈ w, 0<t) (m z : Nat → Nat)
    (hr : ∀ n, PeriodWord.Run L w (m (N+n)) (z (N+n))
      (m (N+(n+1))) (z (N+(n+1)))) : False := by
  exact PeriodWord.no_eventually_periodic_positive_depth_ray L w N hp m z hr

#print axioms source_periodic_tail_boundaries_reachable
#print axioms source_no_eventually_periodic_positive_depth_ray


#print axioms run_source_transport
#print axioms source_primitive_repetition_bound
end BB6.Agent9PeriodSource
