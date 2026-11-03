import Lean.Elab.Tactic.Omega
import BlankRegular8394
import EAllDouble

set_option maxHeartbeats 150000000
set_option maxRecDepth 55000
namespace BB6.BlankExceptional
open CryptidBoundary BB6.BoundaryPadding BB6.Padding

private theorem terminal_source (k : Nat) :
    DRegularSource.sourceSection ⟨3*k+4,6,1⟩ =
      BB6.Agent32EAll.start k 5 [] := by
  have hn : (3*k+4)-2=3*k+2 := by omega
  have hl : oppairs 6 ++ List.replicate 1 true =
      false::(pairs 5 ++ [true,true]) := by decide
  simp only [DRegularSource.sourceSection,BB6.Agent32EAll.start,hn,
    List.append_nil, List.replicate_one]
  simp only [List.replicate_one] at hl
  rw [List.append_assoc, hl]

/-- The genuine blank orbit reaches the exceptional E q=6,b=1 return
    exactly at the last modeled regular section. -/
theorem exceptional_section :
    ∃ k : Nat, ObsEq
      (run (36+DRegular.accumulated 8394 BB6.BlankRegular8394.seed9) blank)
      (BB6.Agent32EAll.start k 5 []) := by
  rcases BB6.BlankRegular8394.blank8394 with ⟨t,hr,hobs⟩
  have ht : (DRegular.run 8394 BB6.BlankRegular8394.seed9).map
      (fun s => (s.a%3,s.q,s.b,decide (s.a≥4))) = some (1,6,1,true) := by decide
  rw [hr] at ht
  simp only [Option.map_some, Option.some.injEq, Prod.mk.injEq] at ht
  rcases ht with ⟨hm,hq,hb,hge⟩
  have hlarge : t.a ≥ 4 := by simpa using hge
  let k := t.a/3-1
  have hform : t.a=3*k+4 := by dsimp [k]; omega
  refine ⟨k,?_⟩
  have hst : t = (⟨3*k+4,6,1⟩ : DRegular.L) := by
    cases t with
    | mk a q b =>
      simp only [DRegular.L.mk.injEq]
      exact ⟨hform,hq,hb⟩
  rw [hst,terminal_source] at hobs
  exact hobs

/-- A complete original-source exceptional E macro on the true blank orbit,
    extending its certified finite nonhalting horizon beyond the regular exit. -/
theorem exceptional_return :
    ∃ k : Nat, ObsEq
      (run ((36 + DRegular.accumulated 8394 BB6.BlankRegular8394.seed9) +
        BB6.Agent32EAll.duration k 5) blank)
      (BB6.Agent32EAll.output k 5 []) := by
  rcases exceptional_section with ⟨k,hs⟩
  refine ⟨k,?_⟩
  exact source_chain
    (36 + DRegular.accumulated 8394 BB6.BlankRegular8394.seed9)
    (BB6.Agent32EAll.duration k 5)
    blank (BB6.Agent32EAll.start k 5 [])
    (BB6.Agent32EAll.output k 5 []) hs
    (BB6.Agent32EAll.all_e_double_implicit_blank k 5)

#print axioms exceptional_section
#print axioms exceptional_return
end BB6.BlankExceptional
