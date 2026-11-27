import Lean.Elab.Tactic.Omega
import ExceptionalEReentryClassification
import ExceptionalBGeneral
import ExceptionalEPacketClosure

set_option maxRecDepth 8192
set_option maxHeartbeats 15000000

namespace BB6.Agent37ExceptionalEResidueClassification

open CryptidBoundary BB6.BoundaryPadding

/-- The section used by the packet engine is exactly the DRegular section
    for every valid unary length a>=2, without any padding hypothesis. -/
private theorem regular_eq_source (a q b : Nat) (ha : 2 ≤ a) :
    BB6.Agent2BoundaryBZero.regularSection a q b =
      DRegularSource.sourceSection ⟨a,q,b⟩ := by
  have hs : List.replicate a true =
      List.replicate 2 true ++ List.replicate (a-2) true := by
    rw [List.replicate_append_replicate]
    congr 1
    omega
  unfold BB6.Agent2BoundaryBZero.regularSection
    DRegularSource.sourceSection CryptidBoundary.init
  rw [hs]
  simp [List.replicate,List.append_assoc]

/-- Under the explicit, *sharp* pair of modular restrictions, every
    exceptional E section returns to some source-connected regular section.
    The sole omitted residue cylinder is simultaneously
        k≡1 (mod 3), q≡1 (mod 3), q>=4.
    This is a formal classification of what existing all-parameter
    original-machine E, B, and A source-composition laws already cover.
    Canonicality of the chosen witness is not asserted in the general
    packet-normalizer E/A branch. -/
theorem all_E_except_double_one_residue (k q : Nat)
    (hq : 1 ≤ q)
    (hcover : q = 1 ∨ k % 3 ≠ 1 ∨ q % 3 ≠ 1) :
    ∃ T a q' b,
      ObsEq
        (run T (DRegularSource.sourceSection ⟨3*k+4,q,1⟩))
        (BB6.Agent2BoundaryBZero.regularSection a q' b) := by
  by_cases hq1 : q=1
  · obtain ⟨T,a,q',b,hobs,hcanon⟩ :=
      BB6.Agent37ExceptionalEReentryClassification.all_E_reentry_canonical_except_q1_mod3
        k q (Or.inl hq1)
    have hs := regular_eq_source a q' b hcanon.1
    exact ⟨T,a,q',b,by rw [hs]; exact hobs⟩
  · have hq2 : 2 ≤ q := by omega
    by_cases hqmod : q % 3 ≠ 1
    · obtain ⟨T,a,q',b,hobs,hcanon⟩ :=
        BB6.Agent37ExceptionalESafeCanonical.all_E_safe_reentry_canonical
          k q hq2 hqmod
      have hs := regular_eq_source a q' b hcanon.1
      exact ⟨BB6.Agent32EAll.duration k (q-1)+T,
        a,q',b,by rw [hs]; exact hobs⟩
    · have hkmod : k % 3 ≠ 1 := by
        rcases hcover with h | h | h
        · exact False.elim (hq1 h)
        · exact h
        · exact False.elim (hqmod h)
      have hcases : k % 3 = 0 ∨ k % 3 = 2 := by omega
      rcases hcases with hk0 | hk2
      · let t : Nat := k/3
        let p : Nat := q-2
        have hkt : k=3*t := by dsimp [t]; omega
        have hqp : q=p+2 := by dsimp [p]; omega
        have hstate : (⟨9*t+4,p+2,1⟩ : DRegular.L) =
            (⟨3*k+4,q,1⟩ : DRegular.L) := by
          congr 1 <;> omega
        have hsource := BB6.Agent25BGeneral.exceptional_EB_general t p
        rw [hstate] at hsource
        have hs := regular_eq_source (64*t+21+2*p) 1 5 (by omega)
        refine ⟨BB6.Agent32EAll.duration (3*t) (p+1) +
          BB6.Agent25BGeneral.bCost t,
          64*t+21+2*p,1,5,?_⟩
        rw [hs]
        exact hsource
      · let t : Nat := k/3
        have hkt : k=3*t+2 := by dsimp [t];omega
        obtain ⟨T,a,q',b,hsource⟩ :=
          BB6.Agent2ExceptionalEPacketClosure.exceptional_EA_all_reentry
            t q hq2
        have hstate : (⟨9*t+10,q,1⟩ : DRegular.L) =
            (⟨3*k+4,q,1⟩ : DRegular.L) := by
          congr 1 <;> omega
        rw [hstate] at hsource
        exact ⟨T,a,q',b,hsource⟩

#print axioms all_E_except_double_one_residue

end BB6.Agent37ExceptionalEResidueClassification
