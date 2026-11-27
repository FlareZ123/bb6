import FastPhaseTree
import PackedPrefixAudit
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace BB6.Agent5CachedPhaseTree
open BB6Coverage BB6.Agent13BlankDelay BB6.Agent5PhaseTree BB6.Agent1NGram
open BB6Coverage.Agent13PackedZipper BB6.Agent3PackedCycle BB6.Agent48PackedPrefix

def query (B : Nat) (p : PartialMachine) (n : Nat) (s : Slot) (z : H) : Bool :=
  decide (readP z.p = s) && decide (p s = none) && decide (n+6 ≤ B)

theorem query_eq (B : Nat) (p : PartialMachine) (n : Nat) (s : Slot) (z : H)
    (hz : runH p n startH = some z) :
    query B p n s z = BB6.Agent5FastPhaseTree.firstOK B p n s := by
  have hp : runP p n startP = some z.p := by
    have h' := runH_project p n startH
    rw [hz] at h'
    simpa only [Option.map_some,startH] using h'.symm
  simp only [query,BB6.Agent5FastPhaseTree.firstOK,readRunP,hp,Option.map_some,Option.some.injEq]

/-- Use the already-proved packed zipper, retained-half-line checker and
    prefix preservation together; unlike an ordinary audit, enforce the
    state-normalized cut at every split. -/
def check (B : Nat) (p : PartialMachine) (t : Nat) (z : H) : (a : Tree) → Bool
  | .bad => false
  | .side e n r b => decide (0 < n) && cycleAtH p t z e n r b
  | .automata a => BB6.Agent4Automata.check p a
  | .last n s =>
    match advanceH p t z n with
    | none => false
    | some c => query B p n s c && BB6.Agent50TNFPilot.restOK p s
  | .split n s cut kids =>
    match advanceH p t z n with
    | none => false
    | some c =>
      query B p n s c && decide (0 < cut) && supportOK p cut &&
      (List.finRange 6).all (fun q => if q.val ≤ cut then bits.all (fun w => bits.all (fun r =>
        check B (refine p s (some ⟨w,r,q⟩)) n c (kids ⟨w,r,q⟩))) else true)
termination_by structural a => a

theorem soundAt (B : Nat) (p : PartialMachine) (a : Tree) (t : Nat) (z : H)
    (valid : runH p t startH = some z)
    (hf : p initialSlot = some (some ⟨true,true,1⟩)) (hc : check B p t z a = true) :
    ∀ m, compatible p m → WeightedBound B m := by
  induction a generalizing p t z with
  | bad => simp [check] at hc
  | side e n r b =>
    simp only [check,cycleAtH_eq p t z e n r b valid,Bool.and_eq_true,decide_eq_true_eq] at hc
    exact fun m hm => weighted_never B m (cycleH_sound p e n r b hc.1 hc.2 m hm)
  | automata a =>
    exact fun m hm => weighted_never B m (BB6.Agent4Automata.never p a hc m hm)
  | last n s =>
    simp only [check,advanceH_eq p t z valid] at hc
    cases hr : runH p n startH with
    | none => simp [hr] at hc
    | some c =>
      simp only [hr,query_eq B p n s c hr,Bool.and_eq_true] at hc
      exact BB6.Agent5FastPhaseTree.sound B p (.last n s) hf (by
        simp only [BB6.Agent5FastPhaseTree.check,Bool.and_eq_true]
        exact hc)
  | split n s cut kids ih =>
    simp only [check,advanceH_eq p t z valid] at hc
    cases hr : runH p n startH with
    | none => simp [hr] at hc
    | some c =>
      simp only [hr,query_eq B p n s c hr,Bool.and_eq_true,decide_eq_true_eq] at hc
      have hu : p s = none := by
        have hq := hc.1.1.1
        simp only [BB6.Agent5FastPhaseTree.firstOK,Bool.and_eq_true,decide_eq_true_eq] at hq
        exact hq.1.2
      apply BB6.Agent5FastPhaseTree.splitFast B p n s cut hf hc.1.1.1 hc.1.1.2 hc.1.2
      intro mv hv
      rcases mv with ⟨w,r,q⟩
      apply ih ⟨w,r,q⟩ _ n c
        (refineRunH p s ⟨w,r,q⟩ hu n startH c hr)
        (refine_preserves_firstOne p s (some ⟨w,r,q⟩) hu hf)
      have H := List.all_eq_true.mp hc.2 q (mem_states q)
      simp only [hv,ite_true] at H
      exact List.all_eq_true.mp (List.all_eq_true.mp H w (mem_bits w)) r (mem_bits r)

def rootCheck (B : Nat) (p : PartialMachine) (a : Tree) : Bool := check B p 0 startH a

theorem sound (B : Nat) (p : PartialMachine) (a : Tree)
    (hf : p initialSlot = some (some ⟨true,true,1⟩)) (hc : rootCheck B p a = true) :
    ∀ m, compatible p m → WeightedBound B m := soundAt B p a 0 startH rfl hf hc

#print axioms soundAt
#print axioms sound
end BB6.Agent5CachedPhaseTree
