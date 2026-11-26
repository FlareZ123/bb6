import Agent46CanonicalCut

set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace BB6.Agent46ResidualGraft
open BB6Coverage BB6.Agent13BlankDelay BB6.Agent46CanonicalCut
open BB6.Agent31ThreeHole

/-- A newly solved literal cylinder, certified with its own budget and root. -/
structure Seal (B : Nat) where
  table : PartialMachine
  root : table initialSlot = some (some ⟨true,true,1⟩)
  safe : ∀ m, compatible table m → WeightedBound B m

def sealedBy {B} (seals : List (Seal B)) (p : PartialMachine) : Bool :=
  seals.any (fun s => tableOK p s.table)

theorem matches_sound {B} {seals : List (Seal B)} {p : PartialMachine}
    (h : sealedBy seals p = true) (m : Machine) (hm : TNFQuotientCompatible p m) :
    WeightedBound B m := by
  rcases List.any_eq_true.mp h with ⟨s, _, hs⟩
  have he := tableOK_sound p s.table hs
  rw [he] at hm
  exact safe_quotient s.root s.safe m hm

def prune {B} (seals : List (Seal B)) (xs : List (List Move × PartialMachine)) :=
  xs.filter (fun e => !sealedBy seals e.2)

/-- Consume any new exact cylinder certificates without recomputing an old cut. -/
theorem prune_sound {B} (seals : List (Seal B)) (xs : List (List Move × PartialMachine))
    (m : Machine) (h : WeightedBound B m ∨ ∃ e ∈ xs, TNFQuotientCompatible e.2 m) :
    WeightedBound B m ∨ ∃ e ∈ prune seals xs, TNFQuotientCompatible e.2 m := by
  rcases h with hb | ⟨e,he,hq⟩
  · exact Or.inl hb
  · cases hm : sealedBy seals e.2 with
    | true => exact Or.inl (matches_sound hm m hq)
    | false => exact Or.inr ⟨e,List.mem_filter.mpr ⟨he,by simp [hm]⟩,hq⟩

/-- Ordinary-label mass represented by a fresh-label quotient path. -/
def pathMass (holes cut : Nat) : List Move → Nat
  | [] => 25^holes
  | mv :: rest => (if mv.next.val = cut then 6-cut else 1) *
      pathMass (holes-1) (nextCut cut mv) rest

def listMass (holes cut : Nat) (xs : List (List Move × PartialMachine)) : Nat :=
  (xs.map (fun e => pathMass holes cut e.1)).sum

private theorem sum_map_mul (xs : List α) (f : α → Nat) (c : Nat) :
    (xs.map (fun x => c * f x)).sum = c * (xs.map f).sum := by
  induction xs with
  | nil => simp
  | cons a xs ih => simp [ih,Nat.mul_add]

private theorem sum_flatmap (xs : List α) (f : α → List Nat) :
    (xs.flatMap f).sum = (xs.map (fun a => (f a).sum)).sum := by
  induction xs with
  | nil => simp
  | cons a xs ih => simp [List.sum_append,ih]

/-- The list accounting agrees with the original checked cut diagnostic. -/
theorem residual_mass_eq (p : PartialMachine) (holes cut : Nat) (t : Cut) :
    listMass holes cut (residuals p cut t) = openMass holes cut t := by
  induction t generalizing p holes cut with
  | unresolved => simp [listMass,residuals,openMass,pathMass]
  | closed t => rfl
  | bounded q C safe => rfl
  | state mask => rfl
  | split n s kids ih =>
    simp only [listMass,residuals,openMass,List.map_flatMap,sum_flatmap,List.map_map,Function.comp_def,pathMass]
    rw [← List.foldl_map,← List.sum_eq_foldl]
    congr 1
    apply List.map_congr_left
    intro mv hmv
    rw [sum_map_mul]
    rw [← ih mv (refine p s (some mv)) (holes-1) (nextCut cut mv)]
    rfl

/-- The exact removed and surviving masses partition the old list mass. -/
theorem mass_partition {B} (seals : List (Seal B)) (holes cut : Nat)
    (xs : List (List Move × PartialMachine)) :
    listMass holes cut (prune seals xs) +
      listMass holes cut (xs.filter (fun e => sealedBy seals e.2)) = listMass holes cut xs := by
  induction xs with
  | nil => simp [prune,listMass]
  | cons e xs ih =>
    cases hm : sealedBy seals e.2 <;> simp [prune,listMass,hm] at * <;> omega

#print axioms prune_sound
#print axioms residual_mass_eq
#print axioms mass_partition
end BB6.Agent46ResidualGraft
