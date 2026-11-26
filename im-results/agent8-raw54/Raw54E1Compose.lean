import Raw54Base
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace BB6.Agent8Raw54
open BB6Coverage BB6.Agent13BlankDelay BB6.Agent8TNFPath
open BB6.Agent50TNFPilot BB6.Agent31ThreeHole BB6.Agent10ZipAudit BB6.Agent47PartialAudit
open BB6Coverage.Agent10ZipAudit

/-- A first-hole split can consume independently proved weighted covers,
    without copying their certificate trees. -/
theorem cover_of_firstHole (B : Nat) (p : PartialMachine) (n : Nat) (s : Slot)
    (hf : p initialSlot = some (some ⟨true,true,1⟩))
    (hq : zipQueryOK B p n s = true)
    (kids : ∀ mv, ∀ m, compatible (refine p s (some mv)) m → WeightedBound B m) :
    ∀ m, compatible p m → WeightedBound B m := by
  obtain ⟨hread,hhole,hw⟩ := zipQueryOK_sound hq
  intro m hm
  cases ht : m s with
  | none =>
    cases hr : knownRun p n with
    | none => simp [hr] at hread
    | some c =>
      have hs : readSlot c = s := by simpa [hr] using hread
      have hc : compatible (refine p s none) m := by
        simpa [ht] using compatible_refine p m s hm
      exact first_hole_weighted_halt B p n c hf hr
        (by simpa [hs] using hhole)
        (by simpa [hs] using weightOK_sound p s n B hw) m
        (by simpa [hs] using hc)
  | some mv =>
    apply kids mv m
    simpa [ht] using compatible_refine p m s hm

def e1Child (mv : Move) : PartialMachine := refine e1 (4,false) (some mv)

theorem cycle_weighted (B : Nat) (p : PartialMachine) (entry period : Nat)
    (r : Bool) (b : Int) (hp : 0 < period) (hc : zipCycle p entry period r b = true) :
    ∀ m, compatible p m → WeightedBound B m :=
  fun m hm => weighted_never B m (zipCycle_sound p entry period r b hp hc m hm)

theorem e1_cover39447
    (h0LF : ∀ m, compatible (e1Child ⟨false,false,5⟩) m → WeightedBound 39447 m)
    (h0RA : ∀ m, compatible (e1Child ⟨false,true,0⟩) m → WeightedBound 39447 m)
    (h0RB : ∀ m, compatible (e1Child ⟨false,true,1⟩) m → WeightedBound 39447 m)
    (h0RF : ∀ m, compatible (e1Child ⟨false,true,5⟩) m → WeightedBound 39447 m)
    (h1LA : ∀ m, compatible (e1Child ⟨true,false,0⟩) m → WeightedBound 39447 m)
    (h1LB : ∀ m, compatible (e1Child ⟨true,false,1⟩) m → WeightedBound 39447 m)
    (h1LF : ∀ m, compatible (e1Child ⟨true,false,5⟩) m → WeightedBound 39447 m)
    (h1RA : ∀ m, compatible (e1Child ⟨true,true,0⟩) m → WeightedBound 39447 m)
    (h1RB : ∀ m, compatible (e1Child ⟨true,true,1⟩) m → WeightedBound 39447 m)
    (h1RF : ∀ m, compatible (e1Child ⟨true,true,5⟩) m → WeightedBound 39447 m)
    : ∀ m, compatible e1 m → WeightedBound 39447 m := by
  apply cover_of_firstHole 39447 e1 7 (4,false) (by decide) (by decide)
  intro mv
  rcases mv with ⟨w,r,q⟩
  have hq : q = 0 ∨ q = 1 ∨ q = 2 ∨ q = 3 ∨ q = 4 ∨ q = 5 := by omega
  rcases hq with rfl|rfl|rfl|rfl|rfl|rfl
  all_goals cases w <;> cases r
  · exact cycle_weighted _ _ 0 8 false (3) (by decide) (by decide)
  · exact h0RA
  · exact h1LA
  · exact h1RA
  · exact cycle_weighted _ _ 7 6 false (0) (by decide) (by decide)
  · exact h0RB
  · exact h1LB
  · exact h1RB
  · exact cycle_weighted _ _ 9 1 false (-1) (by decide) (by decide)
  · exact cycle_weighted _ _ 9 1 false (1) (by decide) (by decide)
  · exact cycle_weighted _ _ 7 3 false (-1) (by decide) (by decide)
  · exact cycle_weighted _ _ 31 18 false (0) (by decide) (by decide)
  · exact cycle_weighted _ _ 8 1 false (-2) (by decide) (by decide)
  · exact cycle_weighted _ _ 8 1 false (0) (by decide) (by decide)
  · exact cycle_weighted _ _ 8 1 false (-2) (by decide) (by decide)
  · exact cycle_weighted _ _ 7 3 false (0) (by decide) (by decide)
  · exact cycle_weighted _ _ 7 1 false (-1) (by decide) (by decide)
  · exact cycle_weighted _ _ 14 1 true (2) (by decide) (by decide)
  · exact cycle_weighted _ _ 7 1 false (-1) (by decide) (by decide)
  · exact cycle_weighted _ _ 25 1 true (-3) (by decide) (by decide)
  · exact h0LF
  · exact h0RF
  · exact h1LF
  · exact h1RF
#print axioms cover_of_firstHole
#print axioms e1_cover39447
end BB6.Agent8Raw54
