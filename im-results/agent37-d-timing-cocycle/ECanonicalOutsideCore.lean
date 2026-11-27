import Lean.Elab.Tactic.Omega
import EAResidueCanonical
import ExceptionalEResidueClassification
import ExceptionalBGeneral
import ExceptionalESafeCanonical
import ExceptionalEReentryClassification

set_option maxRecDepth 8192
set_option maxHeartbeats 16000000

namespace BB6.Agent37ECanonicalOutsideCore

open CryptidBoundary BB6.BoundaryPadding

/-- Every exceptional E source section except the simultaneous
    k≡q≡1 mod3, q>=4 cylinder admits a *canonical* DRegular endpoint,
    not merely an arbitrary regularSection. This permits new exact
    DRegular model iterations after the exceptional source corridor. -/
theorem all_E_except_double_one_canonical (k q : Nat)
    (hq : 1 ≤ q)
    (hcover : q = 1 ∨ k % 3 ≠ 1 ∨ q % 3 ≠ 1) :
    ∃ T a q' b,
      ObsEq
        (run T (DRegularSource.sourceSection ⟨3*k+4,q,1⟩))
        (DRegularSource.sourceSection ⟨a,q',b⟩) ∧
      DRegular.Canon ⟨a,q',b⟩ := by
  by_cases hq1 : q=1
  · obtain ⟨T,a,q',b,hobs,hcanon⟩ :=
      BB6.Agent37ExceptionalEReentryClassification.all_E_reentry_canonical_except_q1_mod3
        k q (Or.inl hq1)
    exact ⟨T,a,q',b,hobs,hcanon⟩
  · have hq2 : 2 ≤ q := by omega
    by_cases hqmod : q % 3 ≠ 1
    · obtain ⟨T,a,q',b,hobs,hcanon⟩ :=
        BB6.Agent37ExceptionalESafeCanonical.all_E_safe_reentry_canonical
          k q hq2 hqmod
      exact ⟨BB6.Agent32EAll.duration k (q-1)+T,
        a,q',b,hobs,hcanon⟩
    · have hkmod : k % 3 ≠ 1 := by
        rcases hcover with h | h | h
        · exact False.elim (hq1 h)
        · exact h
        · exact False.elim (hqmod h)
      have hcases : k % 3 = 0 ∨ k % 3 = 2 := by omega
      rcases hcases with hk0 | hk2
      · let t : Nat := k/3
        let p : Nat := q-2
        have hkt : k=3*t := by dsimp [t];omega
        have hqp : q=p+2 := by dsimp [p];omega
        have hstate : (⟨9*t+4,p+2,1⟩ : DRegular.L) =
            (⟨3*k+4,q,1⟩ : DRegular.L) := by
          congr 1 <;> omega
        have hsource := BB6.Agent25BGeneral.exceptional_EB_general t p
        rw [hstate] at hsource
        have ha : 2 ≤ 64*t+21+2*p := by omega
        have hc : DRegular.Canon
            ⟨64*t+21+2*p,1,5⟩ := by
          exact ⟨ha,Or.inl (show (1:Nat)≠0 by decide)⟩
        exact ⟨BB6.Agent32EAll.duration (3*t) (p+1) +
          BB6.Agent25BGeneral.bCost t,
          64*t+21+2*p,1,5,hsource,hc⟩
      · let t : Nat := k/3
        have hkt : k=3*t+2 := by dsimp [t];omega
        obtain ⟨T,a,hobs,hcanon⟩ :=
          BB6.Agent37EAResidueCanonical.ea_q1_residue_canonical
            t q hq2 (by omega)
        have hstate : (⟨9*t+10,q,1⟩ : DRegular.L) =
            (⟨3*k+4,q,1⟩ : DRegular.L) := by
          congr 1 <;> omega
        rw [hstate] at hobs
        exact ⟨T,a,3,2,hobs,hcanon⟩

#print axioms all_E_except_double_one_canonical

end BB6.Agent37ECanonicalOutsideCore
