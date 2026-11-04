import Lean.Elab.Tactic.Omega
import BlankRootRejoin
import BTrueFirst
import PhysicalReturnObs

set_option maxHeartbeats 150000000
set_option maxRecDepth 55000

namespace BB6.Agent32BlankTwoConsecutive

open CryptidBoundary BB6.Padding BB6.BoundaryPadding
open BB6.Agent32PhysicalObs
open BB6.Agent32EDoubleFirst
open BB6.Agent32BTrueFirst

private def T0 : Nat :=
  36 + DRegular.accumulated 8394 BB6.BlankRegular8394.seed9

/-- Original blank-start trajectory: the 8394-checkpoint is a canonical
    E(10)^5-1100 branch with a parameter in the residue k=0 (mod 3).
    The following E and B macro endpoints are not merely checkpoints:
    there is no earlier physically blank-left F/0 section between them.

    The two strict intervals use the infinite-blank equivalence, so
    arbitrary trailing explicit zero cells cannot fake a return. -/
theorem blank_two_consecutive_physical_first_returns :
    ∃ t : Nat,
      ObsEq
        (run (T0 +
          (BB6.Agent32EAll.duration (3*t) 5 +
            BB6.Agent25Rejoin.bCost t)) blank)
        (DRegularSource.sourceSection ⟨64*t+29,1,5⟩) ∧
      (∀ u, 0<u → u<BB6.Agent32EAll.duration (3*t) 5 →
        ¬PhysicalF0 (run (T0+u) blank)) ∧
      (∀ v, 0<v → v<BB6.Agent25Rejoin.bCost t →
        ¬PhysicalF0
          (run ((T0+BB6.Agent32EAll.duration (3*t) 5)+v) blank)) := by
  rcases BB6.BlankRegular8394.blank8394 with ⟨s,hr,hobs⟩
  have hv : (DRegular.run 8394 BB6.BlankRegular8394.seed9).map
      (fun x => (x.a%9,x.q,x.b)) = some (4,6,1) := by decide
  rw [hr] at hv
  simp only [Option.map_some, Option.some.injEq, Prod.mk.injEq] at hv
  rcases hv with ⟨hm,hq,hb⟩
  let t := s.a/9
  have ha : s.a = 9*t+4 := by dsimp [t]; omega
  have hs : s = (⟨9*t+4,6,1⟩ : DRegular.L) := by
    cases s with
    | mk a q b =>
      simp only [DRegular.L.mk.injEq]
      exact ⟨ha,hq,hb⟩
  rw [hs] at hobs
  let xs : List Bool :=
    List.replicate (3*(3*t)+2) true ++
      (false :: (pairs 5 ++ [true,true]))
  have hsource : DRegularSource.sourceSection ⟨9*t+4,6,1⟩ =
      init xs := by
    have hidx : 9*t+4=3*(3*t)+4 := by omega
    rw [hidx]
    have hn : (3*(3*t)+4)-2=3*(3*t)+2 := by omega
    have hl : oppairs 6 ++ List.replicate 1 true =
        false::(pairs 5 ++ [true,true]) := by decide
    simp only [DRegularSource.sourceSection,xs,hn,
      List.append_nil,List.replicate_one]
    simp only [List.replicate_one] at hl
    rw [List.append_assoc,hl]
  have htarget : BB6.Agent32EAll.start (3*t) 5 [] =
      init (xs ++ List.replicate 2 false) := by
    simp [BB6.Agent32EAll.start,xs,pairs,List.append_assoc]
  have hinput : ObsEq
      (DRegularSource.sourceSection ⟨9*t+4,6,1⟩)
      (BB6.Agent32EAll.start (3*t) 5 []) := by
    rw [hsource,htarget]
    simpa only [CryptidBoundary.run] using
      (source_init_pad 0 2 xs)
  have hstart : ObsEq (run T0 blank)
      (BB6.Agent32EAll.start (3*t) 5 []) := by
    exact cfgEq_trans hobs hinput
  have hEmacro : ObsEq
      (run (BB6.Agent32EAll.duration (3*t) 5)
        (BB6.Agent32EAll.start (3*t) 5 []))
      (BB6.Agent32EAll.output (3*t) 5 []) := by
    rw [(BB6.Agent32EDoubleFirst.all_e_double_first_return (3*t) 5 []).1]
    exact cfgEq_refl _
  have hAfterE : ObsEq
      (run (T0+BB6.Agent32EAll.duration (3*t) 5) blank)
      (BB6.Agent32EAll.output (3*t) 5 []) := by
    exact source_chain T0 (BB6.Agent32EAll.duration (3*t) 5)
      blank (BB6.Agent32EAll.start (3*t) 5 [])
      (BB6.Agent32EAll.output (3*t) 5 []) hstart hEmacro
  let K : Nat := BB6.Agent25Rejoin.K t
  let suffix : List Bool :=
    List.replicate 12 true ++ (false :: List.replicate 6 true)
  have hBinput : BB6.Agent32EAll.output (3*t) 5 [] =
      init (List.replicate (3*K) true ++ (false::suffix)) := by
    have hn : 8*(3*t)+5 = 2+3*K := by
      dsimp [K,BB6.Agent25Rejoin.K]
      omega
    have hrep : List.replicate (8*(3*t)+5) true =
        true::true::List.replicate (3*K) true := by
      calc
        _ = List.replicate (2+3*K) true := by rw [hn]
        _ = List.replicate 2 true ++ List.replicate (3*K) true :=
          (List.replicate_append_replicate).symm
        _ = _ := rfl
    simp [BB6.Agent32EAll.output,init,hrep,suffix]
  refine ⟨t,?_,?_,?_⟩
  · exact source_chain
      T0 (BB6.Agent32EAll.duration (3*t) 5 +
        BB6.Agent25Rejoin.bCost t)
      blank
      (DRegularSource.sourceSection ⟨9*t+4,6,1⟩)
      (DRegularSource.sourceSection ⟨64*t+29,1,5⟩)
      hobs (BB6.Agent25Rejoin.exceptional_EB_two_source t)
  · intro u hpos hbound hp
    rw [run_add] at hp
    have hob : ObsEq
        (run u (run T0 blank))
        (run u (BB6.Agent32EAll.start (3*t) 5 [])) :=
      source_congr u hstart
    exact (BB6.Agent32EDoubleFirst.all_e_double_first_return
      (3*t) 5 []).2 u hpos hbound
        ((physicalF0_congr hob).mp hp)
  · intro v hpos hbound hp
    rw [run_add] at hp
    have hob : ObsEq
        (run v (run (T0+BB6.Agent32EAll.duration (3*t) 5) blank))
        (run v (BB6.Agent32EAll.output (3*t) 5 [])) :=
      source_congr v hAfterE
    have hnext := (physicalF0_congr hob).mp hp
    rw [hBinput] at hnext
    exact (full_B_true_physical_first K suffix)
      v hpos (by
        have hcost : BB6.Agent25Rejoin.bCost t =
          12*K*K+49*K+40 := by rfl
        omega) hnext

#print axioms blank_two_consecutive_physical_first_returns

end BB6.Agent32BlankTwoConsecutive
