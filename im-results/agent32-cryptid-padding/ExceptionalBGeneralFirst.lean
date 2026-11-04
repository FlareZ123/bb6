import Lean.Elab.Tactic.Omega
import ExceptionalBGeneral
import BTrueFirst
import PhysicalReturnObs

set_option maxHeartbeats 10000000
set_option maxRecDepth 4096
set_option linter.unusedSimpArgs false

namespace BB6.Agent32ExceptionalBFirst
open CryptidBoundary BB6.Padding BB6.BoundaryPadding
open BB6.Agent32PhysicalObs
open BB6.Agent32EDoubleFirst
open BB6.Agent32BTrueFirst

/-- The universal q≥2 exceptional E-to-B reentry of Agent25 has
    two CONSECUTIVE real physical F-on-blank-left returns, for every
    source parameter and with any implicit zero padding on the source
    terminal suffix. No earlier physical return intervenes at any
    primitive step in either one-return interval. -/
theorem exceptional_EB_general_first (t p : Nat) :
    let eCost := BB6.Agent32EAll.duration (3*t) (p+1)
    let bCost := BB6.Agent25BGeneral.bCost t
    let start := DRegularSource.sourceSection ⟨9*t+4,p+2,1⟩
    ObsEq
      (run (eCost+bCost) start)
      (DRegularSource.sourceSection ⟨64*t+21+2*p,1,5⟩) ∧
    (∀ u, 0<u → u<eCost →
      ¬PhysicalF0 (run u start)) ∧
    (∀ v, 0<v → v<bCost →
      ¬PhysicalF0 (run (eCost+v) start)) := by
  dsimp
  let xs : List Bool :=
    List.replicate (3*(3*t)+2) true ++
      false :: (pairs (p+1) ++ [true,true])
  have hsource :
      DRegularSource.sourceSection ⟨9*t+4,p+2,1⟩ =
      init xs := by
    exact BB6.Agent25BGeneral.e_input t p
  have htarget :
      BB6.Agent32EAll.start (3*t) (p+1) [] =
      init (xs ++ List.replicate 2 false) := by
    simp [BB6.Agent32EAll.start,xs,List.append_assoc]
  have hinput : ObsEq
      (DRegularSource.sourceSection ⟨9*t+4,p+2,1⟩)
      (BB6.Agent32EAll.start (3*t) (p+1) []) := by
    rw [hsource,htarget]
    simpa only [CryptidBoundary.run] using
      (source_init_pad 0 2 xs)
  have hEmacro : ObsEq
      (run (BB6.Agent32EAll.duration (3*t) (p+1))
        (BB6.Agent32EAll.start (3*t) (p+1) []))
      (BB6.Agent32EAll.output (3*t) (p+1) []) := by
    rw [(BB6.Agent32EDoubleFirst.all_e_double_first_return
      (3*t) (p+1) []).1]
    exact cfgEq_refl _
  have hAfterE : ObsEq
      (run (BB6.Agent32EAll.duration (3*t) (p+1))
        (DRegularSource.sourceSection ⟨9*t+4,p+2,1⟩))
      (BB6.Agent32EAll.output (3*t) (p+1) []) :=
    cfgEq_trans
      (source_congr (BB6.Agent32EAll.duration (3*t) (p+1)) hinput)
      hEmacro
  let K := BB6.Agent25BGeneral.K t
  let ys : List Bool :=
    List.replicate (2*p+4) true ++
      (false :: List.replicate 6 true)
  have hBinput : BB6.Agent32EAll.output (3*t) (p+1) [] =
      init (List.replicate (3*K) true ++ false :: ys) := by
    exact BB6.Agent25BGeneral.output_input t p
  refine ⟨BB6.Agent25BGeneral.exceptional_EB_general t p,?_,?_⟩
  · intro u hpos hbound hp
    have hob : ObsEq
        (run u (DRegularSource.sourceSection ⟨9*t+4,p+2,1⟩))
        (run u (BB6.Agent32EAll.start (3*t) (p+1) [])) :=
      source_congr u hinput
    exact (BB6.Agent32EDoubleFirst.all_e_double_first_return
      (3*t) (p+1) []).2 u hpos hbound
        ((physicalF0_congr hob).mp hp)
  · intro v hpos hbound hp
    rw [run_add] at hp
    have hob : ObsEq
        (run v (run (BB6.Agent32EAll.duration (3*t) (p+1))
          (DRegularSource.sourceSection ⟨9*t+4,p+2,1⟩)))
        (run v (BB6.Agent32EAll.output (3*t) (p+1) [])) :=
      source_congr v hAfterE
    have hafter := (physicalF0_congr hob).mp hp
    rw [hBinput] at hafter
    exact (full_B_true_physical_first K ys) v hpos
      (by
        have hcost : BB6.Agent25BGeneral.bCost t =
          12*K*K+49*K+40 := by rfl
        omega) hafter

#print axioms exceptional_EB_general_first
end BB6.Agent32ExceptionalBFirst
