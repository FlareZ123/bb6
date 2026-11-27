import Lean.Elab.Tactic.Omega
import BlankRegular8394
import ExceptionalESafeCanonical

set_option maxRecDepth 55000
set_option maxHeartbeats 100000000

namespace BB6.Agent37Blank8394SafeE

open CryptidBoundary BB6.BoundaryPadding

/-- The existing 8394-step *authenticated* blank-root regular trajectory
    ends at an E-row with q=6, b=1 and a=1 mod 3. This is a predicate
    certificate, not an unstructured dump of its enormous a parameter. -/
theorem exit9_safe_E_check :
    (DRegular.run 8394 BB6.BlankRegular8394.seed9).any
      (fun t => (t.q == 6) && (t.b == 1) &&
        (t.a % 3 == 1) && decide (4 ≤ t.a)) = true := by
  decide

/-- Genuine *blank-tape* source continuation, not just an assumed
    prepared packet: 36 raw blank-entry steps, 8394 exact regular
    source returns and their accumulated primitive runtimes, then an
    exceptional E6 source return to a later canonical DRegular section.

    This statement does not claim halt; its endpoint has state F/0. -/
theorem blank8394_then_E6_canonical :
    ∃ T a q b,
      ObsEq
        (CryptidBoundary.run
          (36 + DRegular.accumulated 8394
            BB6.BlankRegular8394.seed9 + T)
          CryptidBoundary.blank)
        (DRegularSource.sourceSection ⟨a,q,b⟩) ∧
      DRegular.Canon ⟨a,q,b⟩ := by
  obtain ⟨t,hmodel,hblank⟩ := BB6.BlankRegular8394.blank8394
  have hc := exit9_safe_E_check
  rw [hmodel] at hc
  simp at hc
  have hq : t.q = 6 := by omega
  have hb : t.b = 1 := by omega
  have hm : t.a % 3 = 1 := by omega
  have ha : 4 ≤ t.a := by omega
  let k : Nat := (t.a-4)/3
  have hka : t.a = 3*k+4 := by
    dsimp [k]
    omega
  have hshape : t = (⟨3*k+4,6,1⟩ : DRegular.L) := by
    cases t
    congr 1 <;> omega
  obtain ⟨u,a,q,b,hE,houtCanon⟩ :=
    BB6.Agent37ExceptionalESafeCanonical.all_E_safe_reentry_canonical
      k 6 (by omega) (by decide)
  have hE' : ObsEq
      (CryptidBoundary.run (BB6.Agent32EAll.duration k 5 + u)
        (DRegularSource.sourceSection t))
      (DRegularSource.sourceSection ⟨a,q,b⟩) := by
    simpa [hshape] using hE
  have hchain := BB6.BoundaryPadding.source_chain
    (36 + DRegular.accumulated 8394 BB6.BlankRegular8394.seed9)
    (BB6.Agent32EAll.duration k 5 + u)
    CryptidBoundary.blank
    (DRegularSource.sourceSection t)
    (DRegularSource.sourceSection ⟨a,q,b⟩)
    hblank hE'
  exact ⟨BB6.Agent32EAll.duration k 5 + u,
    a,q,b,hchain,houtCanon⟩

#print axioms exit9_safe_E_check
#print axioms blank8394_then_E6_canonical

end BB6.Agent37Blank8394SafeE
