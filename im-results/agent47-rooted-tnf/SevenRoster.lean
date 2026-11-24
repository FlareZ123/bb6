import RootFrontier
import CryptidGraft
import R1Graft
import R4Graft

set_option maxRecDepth 40000
set_option maxHeartbeats 0

namespace BB6.Agent47SevenRoster
open BB6Coverage BB6.Agent13BlankDelay BB6.Agent8TNFPath
open BB6.Agent50TNFPilot BB6.Agent50RootFrontier
open BB6.Agent50CryptidSiblings BB6.Agent50CryptidGraft
open BB6.Agent47R1Parent BB6.Agent47R1Graft
open BB6.Agent47R4Parent BB6.Agent47R4Graft

/-- An exact packed roster with no evaluation of proof constructors. -/
def Covered (B : Nat) (r : List PackedResidual) : Prop :=
  ∀ m, compatible root m → WeightedBound B m ∨
    ∃ e ∈ r, compatible (unpackTable e.2) m

def replaceAt (target : PackedTable)
    (replacement : PackedResidual → List PackedResidual)
    (r : List PackedResidual) : List PackedResidual :=
  r.flatMap fun e => if e.2 = target then replacement e else [e]

theorem replaceAt_sound {B : Nat} (target : PackedTable)
    (replacement : PackedResidual → List PackedResidual) (r : List PackedResidual)
    (h : Covered B r)
    (hrep : ∀ e, e.2 = target → ∀ m, compatible (unpackTable e.2) m →
      WeightedBound B m ∨ ∃ x ∈ replacement e, compatible (unpackTable x.2) m) :
    Covered B (replaceAt target replacement r) := by
  intro m hm
  rcases h m hm with hg | ⟨e,he,hmatch⟩
  · exact Or.inl hg
  · by_cases ht : e.2 = target
    · rcases hrep e ht m hmatch with hg | ⟨x,hx,hxmatch⟩
      · exact Or.inl hg
      · apply Or.inr
        refine ⟨x, List.mem_flatMap.mpr ⟨e,he,?_⟩,hxmatch⟩
        simpa [ht] using hx
    · apply Or.inr
      refine ⟨e, List.mem_flatMap.mpr ⟨e,he,?_⟩,hmatch⟩
      simp [ht]

def splitAt (p : PartialMachine) (s : Slot) (r : List PackedResidual) : List PackedResidual :=
  replaceAt (packTable p) (fun e => allMoves.map fun mv =>
    (e.1 ++ [mv],packTable (refine p s (some mv)))) r

theorem splitAt_sound {B : Nat} (p : PartialMachine) (n : Nat) (s : Slot)
    (r : List PackedResidual) (h : Covered B r)
    (hroot : p initialSlot = some (some ⟨true,true,1⟩))
    (hhole : p s = none) (hread : (knownRun p n).map readSlot = some s)
    (hw : weightOK p s n B = true) : Covered B (splitAt p s r) := by
  unfold splitAt
  apply replaceAt_sound _ _ _ h
  intro e he m hm
  have hcomp : compatible p m := by simpa only [he,unpack_packTable] using hm
  have href (v : Option Move) (hv : m s = v) : compatible (refine p s v) m := by
    intro t u hu
    by_cases hts : t = s
    · subst t
      have h' : u = v := by simpa [refine] using hu.symm
      simpa [h'] using hv
    · exact hcomp t u (by simpa [refine,hts] using hu)
  cases ha : m s with
  | none =>
    cases hr : knownRun p n with
    | none => simp [hr] at hread
    | some c =>
      have hs : readSlot c = s := by simpa [hr] using hread
      exact Or.inl (first_hole_weighted_halt B p n c hroot hr
        (by simpa [hs] using hhole)
        (by simpa [hs] using weightOK_sound p s n B hw)
        m (by simpa [hs] using href none ha))
  | some mv =>
    apply Or.inr
    refine ⟨(e.1 ++ [mv],packTable (refine p s (some mv))),?_,?_⟩
    · exact List.mem_map.mpr ⟨mv,allMoves_complete mv,rfl⟩
    · simpa only [unpack_packTable] using href (some mv) ha

def eraseAt (p : PartialMachine) (r : List PackedResidual) : List PackedResidual :=
  replaceAt (packTable p) (fun _ => []) r

theorem eraseAt_sound {B : Nat} (p : PartialMachine) (r : List PackedResidual)
    (h : Covered B r) (hp : ∀ m, compatible p m → WeightedBound B m) :
    Covered B (eraseAt p r) := by
  unfold eraseAt
  apply replaceAt_sound _ _ _ h
  intro e he m hm
  exact Or.inl (hp m (by simpa only [he,unpack_packTable] using hm))

/-- Expand a checked path's first-hole cylinders only if they are still in
    the current roster. Shared prefixes are expanded once; a closed endpoint
    is erased only using its weighted certificate. -/
def followPath (p : PartialMachine) (cut : Nat) :
    List PathEntry → List PackedResidual → List PackedResidual
  | [], r => eraseAt p r
  | (_,s,mv)::xs, r => followPath (refine p s (some mv)) (advanceCut cut mv) xs (splitAt p s r)

def pathOKB (B : Nat) (p : PartialMachine) (cut : Nat) : List PathEntry → Bool
  | [] => true
  | (n,s,mv)::xs =>
      decide (p s = none) &&
      decide ((knownRun p n).map readSlot = some s) &&
      decide (s.1.val < cut) && decide (mv.next.val ≤ cut) &&
      weightOK p s n B &&
      pathOKB B (refine p s (some mv)) (advanceCut cut mv) xs

theorem pathOKB_cons {B : Nat} {p : PartialMachine} {cut n : Nat}
    {s : Slot} {mv : Move} {xs : List PathEntry}
    (h : pathOKB B p cut ((n,s,mv)::xs) = true) :
    p s = none ∧ (knownRun p n).map readSlot = some s ∧
    s.1.val < cut ∧ mv.next.val ≤ cut ∧ weightOK p s n B = true ∧
    pathOKB B (refine p s (some mv)) (advanceCut cut mv) xs = true := by
  simpa only [pathOKB,Bool.and_eq_true,decide_eq_true_eq,and_assoc] using h

theorem followPath_sound {B : Nat} (p : PartialMachine) (cut : Nat) (xs : List PathEntry)
    (r : List PackedResidual) (h : Covered B r)
    (hroot : p initialSlot = some (some ⟨true,true,1⟩))
    (hpath : pathOKB B p cut xs = true)
    (hend : ∀ m, compatible (pathEnd p cut xs).1 m → WeightedBound B m) :
    Covered B (followPath p cut xs r) := by
  induction xs generalizing p cut r with
  | nil => exact eraseAt_sound p r h hend
  | cons x xs ih =>
    rcases x with ⟨n,s,mv⟩
    obtain ⟨hhole,hread,_,_,hw,htail⟩ := pathOKB_cons hpath
    exact ih _ _ _ (splitAt_sound p n s r h hroot hhole hread hw)
      (refine_preserves_firstOne p s (some mv) hhole hroot) htail hend

theorem weighted_mono {B C : Nat} (hBC : B ≤ C) {m : Machine}
    (h : WeightedBound B m) : WeightedBound C m := by
  intro k d hk hd
  exact Nat.le_trans (h k d hk hd) hBC

def seedRoster : List PackedResidual := [([],packTable root)]
theorem seedRoster_sound (B : Nat) : Covered B seedRoster := by
  intro m hm
  exact Or.inr ⟨([],packTable root),by simp [seedRoster],by simpa only [unpack_packTable] using hm⟩

def paths : List (List PathEntry) := [path,r1.path,r2.path,r3.path,r4.path,r5.path,r6.path]

def sevenRoster : List PackedResidual :=
  paths.foldl (fun r xs => followPath root 2 xs r) seedRoster

theorem paths_checked : paths.all (pathOKB 7014 root 2) = true := by decide

theorem endpoint_sound (xs : List PathEntry) (h : xs ∈ paths) :
    ∀ m, compatible (pathEnd root 2 xs).1 m → WeightedBound 7014 m := by
  simp only [paths,List.mem_cons,List.not_mem_nil,or_false] at h
  rcases h with h | h | h | h | h | h | h <;> subst xs
  · exact fun m hm => weighted_mono (by decide : 84 ≤ 7014) (all_completions_weighted m hm)
  · exact fun m hm => r1_certificate.sound m hm
  · exact fun m hm => weighted_mono (by decide : r2.bound ≤ 7014) (r2_certificate.sound m hm)
  · exact fun m hm => weighted_mono (by decide : r3.bound ≤ 7014) (r3_certificate.sound m hm)
  · exact fun m hm => weighted_mono (by decide : r4.bound ≤ 7014) (r4_certificate.sound m hm)
  · exact fun m hm => weighted_mono (by decide : r5.bound ≤ 7014) (r5_certificate.sound m hm)
  · exact fun m hm => weighted_mono (by decide : r6.bound ≤ 7014) (r6_certificate.sound m hm)

theorem fold_sound (xs : List (List PathEntry)) (r : List PackedResidual)
    (hr : Covered 7014 r) (hs : ∀ p ∈ xs, p ∈ paths) :
    Covered 7014 (xs.foldl (fun r p => followPath root 2 p r) r) := by
  induction xs generalizing r with
  | nil => exact hr
  | cons p ps ih =>
    have hp : p ∈ paths := hs p (by simp)
    have ht : pathOKB 7014 root 2 p = true := List.all_eq_true.mp paths_checked p hp
    apply ih
    · exact followPath_sound root 2 p r hr rfl ht (endpoint_sound p hp)
    · intro q hq; exact hs q (by simp [hq])

theorem sevenRoster_sound : Covered 7014 sevenRoster :=
  fold_sound paths seedRoster (seedRoster_sound 7014) (fun _ h => h)

-- VM count is diagnostic; semantic soundness above is a proof over the exact list.
#eval sevenRoster.length

#print axioms replaceAt_sound
#print axioms splitAt_sound
#print axioms followPath_sound
#print axioms sevenRoster_sound

end BB6.Agent47SevenRoster
