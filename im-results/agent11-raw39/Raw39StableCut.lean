import ZipThreeHoleAudit

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace BB6.Agent11Raw39Stable
open BB6Coverage BB6.Agent13BlankDelay BB6.Agent8TNFPath
open BB6.Agent50TNFPilot BB6.Agent31ThreeHole BB6.Agent10ZipAudit
open BB6Coverage.Agent10ZipAudit

abbrev p39 : PartialMachine :=
  refine (pathEnd root 2 (path.take 3)).1 (3,true) (some ⟨false,true,0⟩)
abbrev child (mv : Move) := refine p39 (0,true) (some mv)

theorem p39_root : p39 initialSlot = some (some ⟨true,true,1⟩) := by decide

def residualMoves : List Move := [
  ⟨false,false,0⟩, ⟨false,false,4⟩, ⟨false,false,5⟩,
  ⟨false,true,2⟩, ⟨false,true,5⟩,
  ⟨true,false,0⟩, ⟨true,false,1⟩, ⟨true,false,4⟩,
  ⟨true,false,5⟩, ⟨true,true,4⟩, ⟨true,true,5⟩]

def residuals : List (List Move × PartialMachine) :=
  residualMoves.map fun mv => ([mv], child mv)

theorem residual_count : residuals.length = 11 := by decide

theorem residual_mem (mv : Move) : ([mv], child mv) ∈ residuals ↔ mv ∈ residualMoves := by
  constructor
  · intro h
    obtain ⟨v,hv,he⟩ := List.mem_map.mp h
    have he' := congrArg Prod.fst he
    have : v = mv := by simpa using he'
    simpa [this] using hv
  · intro h
    exact List.mem_map.mpr ⟨mv,h,rfl⟩

theorem lift_bound {A B : Nat} {m : Machine} (hAB : A ≤ B)
    (h : WeightedBound A m) : WeightedBound B m :=
  fun k d hk hd => Nat.le_trans (h k d hk hd) hAB

private theorem cycle_bound (mv : Move) (e k : Nat) (r : Bool) (b : Int)
    (hk : 0 < k) (hc : zipCycle (child mv) e k r b = true)
    (m : Machine) (hm : compatible (child mv) m) : WeightedBound 1882 m :=
  weighted_never 1882 m (zipCycle_sound (child mv) e k r b hk hc m hm)

private theorem retain (mv : Move) (hv : mv ∈ residualMoves)
    (m : Machine) (hm : compatible (child mv) m) :
    WeightedBound 1882 m ∨ ∃ e ∈ residuals, compatible e.2 m :=
  Or.inr ⟨([mv],child mv), (residual_mem mv).mpr hv, hm⟩

/-- Compose semantic child bounds without replaying their large Audit trees. -/
theorem cut_sound
    (h0RB : ∀ m, compatible (child ⟨false,true,1⟩) m → WeightedBound 1271 m)
    (h1RB : ∀ m, compatible (child ⟨true,true,1⟩) m → WeightedBound 175 m)
    (h1RC : ∀ m, compatible (child ⟨true,true,2⟩) m → WeightedBound 1882 m)
    (h0RE : ∀ m, compatible (child ⟨false,true,4⟩) m → WeightedBound 944 m) :
    ∀ m, compatible p39 m →
      WeightedBound 1882 m ∨ ∃ e ∈ residuals, compatible e.2 m := by
  intro m hm
  have hc := compatible_refine p39 m (0,true) hm
  cases ht : m (0,true) with
  | none =>
    have hq : zipQueryOK 1882 p39 6 (0,true) = true := by decide
    obtain ⟨hread,hhole,hw⟩ := zipQueryOK_sound hq
    cases hr : knownRun p39 6 with
    | none => simp [hr] at hread
    | some c =>
      have hs : readSlot c = (0,true) := by simpa [hr] using hread
      exact Or.inl (first_hole_weighted_halt 1882 p39 6 c p39_root hr
        (by simpa [hs] using hhole)
        (by simpa [hs] using weightOK_sound p39 (0,true) 6 1882 hw) m
        (by simpa [hs,ht] using hc))
  | some mv =>
    have hm' : compatible (child mv) m := by simpa [ht] using hc
    rcases mv with ⟨w,r,q⟩
    have hq : q = 0 ∨ q = 1 ∨ q = 2 ∨ q = 3 ∨ q = 4 ∨ q = 5 := by omega
    rcases hq with rfl|rfl|rfl|rfl|rfl|rfl
    all_goals cases w <;> cases r
    · exact retain _ (by decide) m hm'
    · exact Or.inl (cycle_bound _ 0 8 true 0 (by decide) (by decide) m hm')
    · exact retain _ (by decide) m hm'
    · exact Or.inl (cycle_bound _ 0 8 true 0 (by decide) (by decide) m hm')
    · exact Or.inl (cycle_bound _ 0 10 true 0 (by decide) (by decide) m hm')
    · exact Or.inl (lift_bound (by decide) (h0RB m hm'))
    · exact retain _ (by decide) m hm'
    · exact Or.inl (lift_bound (by decide) (h1RB m hm'))
    · exact Or.inl (cycle_bound _ 13 1 false 1 (by decide) (by decide) m hm')
    · exact retain _ (by decide) m hm'
    · exact Or.inl (cycle_bound _ 0 12 true 0 (by decide) (by decide) m hm')
    · exact Or.inl (h1RC m hm')
    · exact Or.inl (cycle_bound _ 10 1 false 0 (by decide) (by decide) m hm')
    · exact Or.inl (cycle_bound _ 0 8 true 0 (by decide) (by decide) m hm')
    · exact Or.inl (cycle_bound _ 10 1 false 0 (by decide) (by decide) m hm')
    · exact Or.inl (cycle_bound _ 0 8 true 0 (by decide) (by decide) m hm')
    · exact retain _ (by decide) m hm'
    · exact Or.inl (lift_bound (by decide) (h0RE m hm'))
    · exact retain _ (by decide) m hm'
    · exact retain _ (by decide) m hm'
    · exact retain _ (by decide) m hm'
    · exact retain _ (by decide) m hm'
    · exact retain _ (by decide) m hm'
    · exact retain _ (by decide) m hm'

#print axioms residual_count
#print axioms residual_mem
#print axioms cut_sound
end BB6.Agent11Raw39Stable
