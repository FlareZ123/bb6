import TotalEdge
import StrictAllCert

namespace Agent36.StrictGuard
open CryptidBoundary BB6.Agent32Route BB6.Agent32Guard BB6.Agent32Counted BB6.Padding BB6.BoundaryPadding
set_option maxHeartbeats 8000000
set_option maxRecDepth 4096

theorem halt_cert_first (h : HaltCert) (k : Nat) (hv : h.Valid) :
    FirstEvent (sect (allInputN k h.e.r) h.e.v) (liveTime h k) ∧
    Gate (run (liveTime h k) (sect (allInputN k h.e.r) h.e.v)) := by
  rcases hv with ⟨hr,hw,hi,hf,hs,hb⟩
  exact all_guarded_halt_first h.e k h.target hr hw hi hf ⟨hs,hb⟩

theorem totalEdge_first (n : Nat) (v : List Bool) (hn : 2≤n) :
    match totalEdge n v with
    | .live _ m w p _ => FirstEvent (sect n v) p.c ∧
        ObsEq (run p.c (sect n v)) (sect m w)
    | .halt _ p => FirstEvent (sect n v) p.c ∧ Gate (run p.c (sect n v)) := by
  unfold totalEdge
  simp only [hn,dite_true]
  generalize hk : (n-branchBase (n%3))/3 = k
  have hi := input_decomp n hn
  rw [hk] at hi
  cases he : totalCert (n%3) v (by omega) with
  | inl e =>
    rw [←e.property.1] at hi
    have hv := all_cert_first e.val k e.property.2.2
    rw [←hi,e.property.2.1] at hv
    simpa only [returnPoly,edgePoly,←time_poly] using hv
  | inr h =>
    rw [←h.property.1] at hi
    have hv := halt_cert_first h.val k h.property.2.2
    rw [←hi,h.property.2.1] at hv
    simpa only [haltPoly,edgePoly,←halt_time_poly] using hv

/-- All residue classes, all suffixes, all unary parameters: the first
    physical event itself has the affine endpoint and quadratic clock. -/
theorem global_first_affine (r : Nat) (v : List Bool) (hr : r<3) :
    (∃ (c b t : Nat) (w : List Bool), 3≤c ∧ 0<t ∧
      ∀ k, FirstEvent (sect (allInputN k r) v) (12*k*k+b*k+t) ∧
        SrcRun (allInputN k r) v (8*k+c) w (12*k*k+b*k+t)) ∨
    (∃ b t : Nat, 0<t ∧ ∀ k, FirstEvent (sect (allInputN k r) v) (12*k*k+b*k+t) ∧
        SrcHalt (allInputN k r) v (12*k*k+b*k+t)) := by
  rcases all_cert_total r v hr with ⟨e,he,hev,hval⟩|⟨h,he,hev,hval⟩
  · left
    refine ⟨2*(e.inc+e.p)+3+e.lead,49+24*triples e.ws,e.time 0,e.out,by omega,?_,?_⟩
    · exact (all_cert_first e 0 hval).1.1
    · intro k
      rw [←he,←hev,←time_poly]
      have h := all_cert_first e k hval
      simpa [SrcRun,AllCert.outputN,Nat.add_assoc] using h
  · right
    refine ⟨41+24*triples h.e.ws,liveTime h 0,?_,?_⟩
    · exact (halt_cert_first h 0 hval).1.1
    · intro k
      rw [←he,←hev,←halt_time_poly]
      exact halt_cert_first h k hval

#print axioms halt_cert_first
#print axioms totalEdge_first
#print axioms global_first_affine
end Agent36.StrictGuard
