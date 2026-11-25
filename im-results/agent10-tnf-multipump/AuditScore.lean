import ExactAuditWeight
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace BB6.Agent10ExactAuditWeight
open BB6Coverage BB6.Agent13BlankDelay BB6.Agent8TNFPath
open BB6.Agent50TNFPilot BB6.Agent31ThreeHole BB6.Agent10ZipAudit

def maxList (xs : List Nat) : Nat := xs.foldr max 0

theorem maxList_le (xs : List Nat) (B : Nat) :
    maxList xs ≤ B ↔ ∀ x ∈ xs, x ≤ B := by
  induction xs with
  | nil => simp [maxList]
  | cons x xs ih =>
    change max x (maxList xs) ≤ B ↔ _
    rw [Nat.max_le,ih]
    constructor
    · rintro ⟨h1,h2⟩ y hy
      rcases List.mem_cons.mp hy with rfl | h
      · exact h1
      · exact h2 y h
    · intro h
      exact ⟨h x (by simp),fun y hy => h y (List.mem_cons_of_mem _ hy)⟩

def queryScore (p : PartialMachine) (n : Nat) (s : Slot) : Nat :=
  maxList ((possibleDelays (refine p s none) 0).map (fun d => d+n+1))

theorem queryScore_le (p : PartialMachine) (n : Nat) (s : Slot) (B : Nat) :
    queryScore p n s ≤ B ↔ weightOK p s n B = true := by
  unfold queryScore weightOK
  rw [maxList_le,List.all_eq_true]
  constructor
  · intro h d hd
    exact decide_eq_true (h _ (List.mem_map.mpr ⟨d,hd,rfl⟩))
  · intro h x hx
    obtain ⟨d,hd,rfl⟩ := List.mem_map.mp hx
    exact of_decide_eq_true (h d hd)

def moves : List Move :=
  (List.finRange 6).flatMap fun q => [false,true].flatMap fun w => [false,true].map fun r => ⟨w,r,q⟩

theorem mem_moves (mv : Move) : mv ∈ moves := by
  rcases mv with ⟨w,r,q⟩
  apply List.mem_flatMap.mpr
  refine ⟨q,List.mem_finRange q,?_⟩
  apply List.mem_flatMap.mpr
  refine ⟨w,by cases w <;> simp,?_⟩
  exact List.mem_map.mpr ⟨r,by cases r <;> simp,rfl⟩

def auditScore (p : PartialMachine) : (t : Audit) → Nat
  | .last n s => queryScore p n s
  | .cycle .. => 0
  | .far .. => 0
  | .proven .. => 0
  | .split n s kids => max (queryScore p n s)
      (maxList (moves.map fun mv => auditScore (refine p s (some mv)) (kids mv)))
termination_by structural t => t

theorem auditScore_le (p : PartialMachine) (t : Audit) (B : Nat) :
    auditScore p t ≤ B ↔ weightCheck B p t = true := by
  induction t generalizing p with
  | last n s => exact queryScore_le p n s B
  | cycle e k r b => simp [auditScore,weightCheck]
  | far rev d cert => simp [auditScore,weightCheck]
  | proven q safe => simp [auditScore,weightCheck]
  | split n s kids ih =>
    simp only [auditScore,weightCheck,Nat.max_le,queryScore_le,Bool.and_eq_true,maxList_le]
    constructor
    · rintro ⟨hq,hk⟩
      refine ⟨hq,allMoves_of _ ?_⟩
      intro mv
      exact (ih mv _).mp (hk _ (List.mem_map.mpr ⟨mv,mem_moves mv,rfl⟩))
    · rintro ⟨hq,hk⟩
      refine ⟨hq,?_⟩
      intro x hx
      obtain ⟨mv,hm,rfl⟩ := List.mem_map.mp hx
      exact (ih mv _).mpr (allMoves_sound _ hk mv)

/-- The arithmetic fold returns the least possible weighted bound. -/
theorem exact_score_iff {B C : Nat} (p : PartialMachine) (t : Audit)
    (hroot : p initialSlot = some (some ⟨true,true,1⟩))
    (hno : weightedTNFNoAssignedHalt p) (h : zipCheck B p t = true) :
    (∀ m, compatible p m → WeightedBound C m) ↔ auditScore p t ≤ C :=
  (exact_weight_iff p t hroot hno h).trans (auditScore_le p t C).symm

/-- A positive fold value is actually attained, rather than just an upper bound. -/
theorem score_attained {B : Nat} (p : PartialMachine) (t : Audit)
    (hroot : p initialSlot = some (some ⟨true,true,1⟩))
    (hno : weightedTNFNoAssignedHalt p) (h : zipCheck B p t = true)
    (hpos : 0 < auditScore p t) :
    ∃ m, compatible p m ∧ ∃ k d, HaltsAfter m k ∧ d ∈ delays (zeroNext m) 0 ∧
      d+k+1 = auditScore p t := by
  classical
  have hupper := (exact_score_iff (C := auditScore p t) p t hroot hno h).mpr (Nat.le_refl _)
  have hnot : ¬ ∀ m, compatible p m → WeightedBound (auditScore p t - 1) m := by
    intro hh
    have hle := (exact_score_iff p t hroot hno h).mp hh
    omega
  apply Classical.byContradiction
  intro hnone
  apply hnot
  intro m hm k d hk hd
  have hu := hupper m hm k d hk hd
  have hn : d+k+1 ≠ auditScore p t := fun he => hnone ⟨m,hm,k,d,hk,hd,he⟩
  omega

#print axioms exact_score_iff
#print axioms score_attained
end BB6.Agent10ExactAuditWeight
