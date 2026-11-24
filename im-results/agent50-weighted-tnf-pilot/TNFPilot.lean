import FirstHolePath
import FiniteLassoOracle
import RayFiniteOracle

set_option maxRecDepth 16000
set_option maxHeartbeats 0

namespace BB6.Agent50TNFPilot
open BB6Coverage BB6.Agent13BlankDelay BB6.Agent8TNFPath

/-- Each record specifies the genuine first-hole time, slot and ordinary
    action. The path and local certificate are independently checked. -/
abbrev PathEntry := Nat × Slot × Move

def path : List PathEntry :=
  [(1, (1,false), ⟨true,true,2⟩),
   (2, (2,false), ⟨false,true,3⟩),
   (3, (3,false), ⟨true,false,3⟩),
   (5, (3,true), ⟨true,true,4⟩),
   (6, (4,true), ⟨false,false,1⟩),
   (7, (1,true), ⟨true,false,5⟩),
   (8, (5,true), ⟨false,false,0⟩),
   (11, (2,true), ⟨false,true,1⟩),
   (21, (5,false), ⟨false,false,4⟩)]

def pathEnd (p : PartialMachine) (cut : Nat) :
    List PathEntry → PartialMachine × Nat
  | [] => (p, cut)
  | (_,s,mv)::xs => pathEnd (refine p s (some mv)) (advanceCut cut mv) xs

def pathOK (p : PartialMachine) (cut : Nat) : List PathEntry → Bool
  | [] => true
  | (n,s,mv)::xs =>
    decide (p s = none) &&
      (decide ((knownRun p n).map readSlot = some s) &&
       (decide (s.1.val < cut) &&
        (decide (mv.next.val ≤ cut) &&
         pathOK (refine p s (some mv)) (advanceCut cut mv) xs)))

theorem pathOK_sound (p : PartialMachine) (cut : Nat) (xs : List PathEntry)
    (hp : FirstHolePath p cut) (h : pathOK p cut xs = true) :
    FirstHolePath (pathEnd p cut xs).1 (pathEnd p cut xs).2 := by
  induction xs generalizing p cut with
  | nil => exact hp
  | cons x xs ih =>
    rcases x with ⟨n,s,mv⟩
    simp only [pathOK, Bool.and_eq_true, decide_eq_true_eq] at h
    obtain ⟨hhole,hread,hslot,hmove,htail⟩ := h
    cases hr : knownRun p n with
    | none => simp [hr] at hread
    | some c =>
      have hs : readSlot c = s := by simpa [hr] using hread
      subst s
      exact ih _ _ (.step hp hr hhole hslot hmove) htail

abbrev root := BB6.CoverageAdapter.firstOneCylinder
abbrev parent : PartialMachine := (pathEnd root 2 path).1

theorem parent_reachable : FirstHolePath parent 6 := by
  have hc : pathOK root 2 path = true := by decide
  have hp := pathOK_sound root 2 path FirstHolePath.root hc
  exact hp

theorem parent_root : parent initialSlot = some (some ⟨true,true,1⟩) := by
  decide

theorem support6 (p : PartialMachine) : TNFSupport p 6 := by
  intro s t _
  exact ⟨s.1.isLt, fun mv _ => mv.next.isLt⟩

theorem pathEnd_nohalt (p : PartialMachine) (cut : Nat) (xs : List PathEntry)
    (hp : weightedTNFNoAssignedHalt p) :
    weightedTNFNoAssignedHalt (pathEnd p cut xs).1 := by
  induction xs generalizing p cut with
  | nil => exact hp
  | cons x xs ih =>
    rcases x with ⟨n,s,mv⟩
    exact ih _ _ (weightedTNFNoAssignedHalt_refine p s mv hp)

theorem parent_nohalt : weightedTNFNoAssignedHalt parent :=
  pathEnd_nohalt root 2 path firstOneCylinder_no_assigned_halt

abbrev a1 : Slot := (0,true)
abbrev e0 : Slot := (4,false)
abbrev child (mv : Move) : PartialMachine := refine parent a1 (some mv)

theorem parent_hole : parent a1 = none := by decide

theorem child_root (mv : Move) :
    child mv initialSlot = some (some ⟨true,true,1⟩) :=
  refine_preserves_firstOne parent a1 (some mv) parent_hole parent_root

theorem child_nohalt (mv : Move) : weightedTNFNoAssignedHalt (child mv) :=
  weightedTNFNoAssignedHalt_refine parent a1 mv parent_nohalt

/-- The last-hole test independently checks every other row. -/
def restOK (p : PartialMachine) (hole : Slot) : Bool :=
  (List.finRange 6).all fun q => [false,true].all fun b =>
    if (q,b) = hole then true else ((p (q,b)).getD none).isSome

theorem restOK_sound (p : PartialMachine) (hole : Slot)
    (h : restOK p hole = true) :
    ∀ s, s ≠ hole → ∃ mv, p s = some (some mv) := by
  rintro ⟨q,b⟩ hn
  have hq := List.all_eq_true.mp h q (List.mem_finRange q)
  have hb : b ∈ [false,true] := by cases b <;> simp
  have hs := List.all_eq_true.mp hq b hb
  simp only [hn, if_false] at hs
  cases hp : p (q,b) with
  | none => simp [hp] at hs
  | some t =>
    cases t with
    | none => simp [hp] at hs
    | some mv => exact ⟨mv,rfl⟩

/-- Check actual incoming delays, not a raw score or a loose margin. -/
def weightOK (p : PartialMachine) (hole : Slot) (n B : Nat) : Bool :=
  (possibleDelays (refine p hole none) 0).all fun d => decide (d+n+1 ≤ B)

theorem weightOK_sound (p : PartialMachine) (hole : Slot) (n B : Nat)
    (h : weightOK p hole n B = true) :
    ∀ d ∈ possibleDelays (refine p hole none) 0, d+n+1 ≤ B := by
  intro d hd
  exact of_decide_eq_true (List.all_eq_true.mp h d hd)

inductive Witness where
  | last (n : Nat)
  | ray (n : Nat)
  | lasso (n : Nat)

def witness (mv : Move) : Witness :=
  match mv.write, mv.right, mv.next.val with
  | false,false,0 => .last 36
  | false,false,1 => .last 40
  | false,false,2 => .ray 33
  | false,false,3 => .ray 32
  | false,false,4 => .last 32
  | false,false,5 => .last 33
  | false,true,0 => .lasso 40
  | false,true,1 => .lasso 52
  | false,true,2 => .last 34
  | false,true,3 => .ray 32
  | false,true,4 => .last 32
  | false,true,5 => .last 33
  | true,false,0 => .last 83
  | true,false,1 => .last 68
  | true,false,2 => .last 34
  | true,false,3 => .ray 32
  | true,false,4 => .last 32
  | true,false,5 => .last 33
  | true,true,0 => .lasso 33
  | true,true,1 => .lasso 36
  | true,true,2 => .last 34
  | true,true,3 => .last 37
  | true,true,4 => .last 32
  | true,true,5 => .last 42
  | _,_,_ => .last 0

/-- All ray witnesses enter D on a pristine left half-line; D/0=1LD. -/
def dMask (q : Fin 6) : Bool := q == 3

def witnessOK (mv : Move) : Bool :=
  let p := child mv
  match witness mv with
  | .last n =>
    decide ((knownRun p n).map readSlot = some e0) &&
      (decide (p e0 = none) && (restOK p e0 && weightOK p e0 n 84))
  | .ray n => finiteRayCheck p n false dMask
  | .lasso n => finiteLassoCheck p n

def allWitnessOK : Bool :=
  (List.finRange 6).all fun q => [false,true].all fun w =>
    [false,true].all fun r => witnessOK ⟨w,r,q⟩

theorem all_witnesses_checked : allWitnessOK = true := by decide

theorem witness_checked (mv : Move) : witnessOK mv = true := by
  rcases mv with ⟨w,r,q⟩
  have hq := List.all_eq_true.mp all_witnesses_checked q (List.mem_finRange q)
  have hw : w ∈ [false,true] := by cases w <;> simp
  have hr : r ∈ [false,true] := by cases r <;> simp
  exact List.all_eq_true.mp (List.all_eq_true.mp hq w hw) r hr

theorem zeroCover_never {p : PartialMachine} (cert : Cover (DecidedBelow 0) p) :
    ∀ m, compatible p m → NeverHalts m := by
  intro m hm
  rcases cert.sound m hm with hn | ⟨n,h,_⟩
  · exact hn
  · omega

/-- Construct a real lastHole node from accepted finite observations. -/
def lastCert (p : PartialMachine) (n : Nat) (hole : Slot)
    (hf : p initialSlot = some (some ⟨true,true,1⟩))
    (hread : (knownRun p n).map readSlot = some hole)
    (hh : p hole = none) (hrest : restOK p hole = true)
    (hw : weightOK p hole n 84 = true) :
    WeightedTNFCertificate 84 p 6 := by
  cases hr : knownRun p n with
  | none => simp [hr] at hread
  | some c =>
    have hs : readSlot c = hole := by simpa [hr] using hread
    exact .lastHole hf (support6 p) (by decide) hr
      (by simpa [hs] using hh)
      (by simpa [hs] using restOK_sound p hole hrest)
      (by simpa [hs] using weightOK_sound p hole n 84 hw)

/-- All 24 ordinary branches have a semantic leaf or an actual lastHole
    node; no decider cutoff is converted into a verdict. -/
def childCert (mv : Move) : WeightedTNFCertificate 84 (child mv) 6 := by
  have hc := witness_checked mv
  cases he : witness mv with
  | last n =>
    have h : ((knownRun (child mv) n).map readSlot = some e0) ∧
        child mv e0 = none ∧ restOK (child mv) e0 = true ∧
        weightOK (child mv) e0 n 84 = true := by
      simpa only [witnessOK, he, Bool.and_eq_true, decide_eq_true_eq] using hc
    exact lastCert (child mv) n e0 (child_root mv) h.1 h.2.1 h.2.2.1 h.2.2.2
  | ray n =>
    have h : finiteRayCheck (child mv) n false dMask = true := by
      simpa only [witnessOK,he] using hc
    exact .nonhalt (child_root mv) (support6 _) (child_nohalt mv)
      (zeroCover_never (finiteRayCheck_sound _ n false dMask 0 h))
  | lasso n =>
    have h : finiteLassoCheck (child mv) n = true := by
      simpa only [witnessOK,he] using hc
    exact .nonhalt (child_root mv) (support6 _) (child_nohalt mv)
      (zeroCover_never (finiteLassoCheck_sound _ n 0 h))

theorem parent_query : (knownRun parent 31).map readSlot = some a1 := by decide
theorem parent_weight : weightOK parent a1 31 84 = true := by decide

/-- A complete nontrivial normalized subtree. The halt sibling at A1 is
    bounded using the actual delay list, and every ordinary sibling is
    retained. There is no fresh-label branch because cut=6. -/
def certificate : WeightedTNFCertificate 84 parent 6 := by
  have hread := parent_query
  cases hr : knownRun parent 31 with
  | none => simp [hr] at hread
  | some c =>
    have hs : readSlot c = a1 := by simpa [hr] using hread
    refine .expand parent_root (support6 _) (by decide) parent_nohalt hr
      (by simpa [hs] using parent_hole)
      (by simpa [hs] using weightOK_sound parent a1 31 84 parent_weight) ?_ ?_
    · intro mv _
      simpa only [hs, child] using childCert mv
    · intro q hq _ _
      have hlt := q.isLt
      omega

theorem all_completions_weighted : ∀ m, compatible parent m → WeightedBound 84 m :=
  certificate.sound

/-- The 1LA child followed by E0=halt attains 83 ordinary moves. -/
theorem attained : ∃ m, compatible parent m ∧ HaltsAfter m 83 := by
  let p := child ⟨true,false,0⟩
  let m := weightedTNFDefaultCompletion (refine p e0 none)
  have hr : (knownRun p 83).map readSlot = some e0 := by decide
  have hh : p e0 = none := by decide
  have hm : compatible (refine p e0 none) m :=
    weightedTNFDefaultCompletion_compatible _
  have hmp : compatible p m := refine_preserves_compat p m e0 none hh hm
  have hparent : compatible parent m :=
    refine_preserves_compat parent m a1 (some ⟨true,false,0⟩) parent_hole hmp
  refine ⟨m,hparent,?_⟩
  cases hrun : knownRun p 83 with
  | none => simp [hrun] at hr
  | some c =>
    have hs : readSlot c = e0 := by simpa [hrun] using hr
    apply first_hole_halts p 83 c hrun
    · simpa [hs] using hh
    · simpa [hs] using hm

theorem exact_weighted_threshold (B : Nat) :
    (∀ m, compatible parent m → WeightedBound B m) ↔ 84 ≤ B := by
  constructor
  · intro h
    obtain ⟨m,hm,hh⟩ := attained
    have hz := firstOne_terminal parent parent_root m hm
    have hd : 0 ∈ delays (zeroNext m) 0 :=
      (mem_delays_iff hz).mpr ⟨0, TerminalPath.stop 0 hz⟩
    have hb := h m hm 83 0 hh hd
    omega
  · intro hb m hm k d hk hd
    exact Nat.le_trans (all_completions_weighted m hm k d hk hd) hb

#print axioms parent_reachable
#print axioms all_witnesses_checked
#print axioms certificate
#print axioms all_completions_weighted
#print axioms attained
#print axioms exact_weighted_threshold
end BB6.Agent50TNFPilot
