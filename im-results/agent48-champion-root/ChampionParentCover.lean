import ChampionSiblingCounter
import ChampionSiblingLC
import ChampionSiblingRE
import SideCycle
import FirstHolePath

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace BB6.Agent48Parent
open BB6Coverage BB6Coverage.Agent48Champion BB6Coverage.Agent31Pump
open BB6Coverage.Agent50SideCycle BB6.Agent13BlankDelay BB6.Agent47WeightedHalt

def a1 : Slot := (0,true)
def b1 : Slot := (1,true)
def parentM : Machine := fun s => if s=a1 then none else championTable s
def parent : PartialMachine := forgetHaltRows parentM
def childM (mv : Move) : Machine := fun s => if s=a1 then some mv else championTable s
def child (mv : Move) : PartialMachine := forgetHaltRows (childM mv)

theorem child_eq (mv : Move) : child mv = refine parent a1 (some mv) := by
  funext s
  by_cases h : s=a1 <;> simp [child,childM,parent,parentM,refine,forgetHaltRows,h]

theorem parent_hole : parent a1 = none := by decide
theorem child_hole (mv : Move) : child mv b1 = none := rfl

theorem champion_rest : ∀ s, s ≠ b1 → ∃ mv, championTable s = some mv := by
  have h : ∀ q : Fin 6, ∀ b : Bool, (q,b) ≠ b1 → (championTable (q,b)).isSome = true := by decide
  intro s hs
  have hh := h s.1 s.2 hs
  cases he : championTable s with
  | none => simp [he] at hh
  | some mv => exact ⟨mv,rfl⟩

theorem child_rest (mv : Move) (s : Slot) (hs : s ≠ b1) :
    ∃ w, child mv s = some (some w) := by
  by_cases ha : s=a1
  · subst s
    exact ⟨mv,by simp [child,childM,forgetHaltRows]⟩
  · obtain ⟨w,hw⟩ := champion_rest s hs
    exact ⟨w,by simp [child,childM,forgetHaltRows,ha,hw]⟩

theorem champion_child : child ⟨true,true,0⟩ = forgetHaltRows championTable := by
  funext s
  by_cases h : s=a1
  · subst s; rfl
  · simp [child,childM,forgetHaltRows,h]

def slot0 (z : Z0) : Slot := (z.q,z.l.headD false)
def check (p : PartialMachine) (n : Nat) (s : Slot) : Bool :=
  decide ((run0 p n ⟨0,[],[]⟩).map slot0 = some s)

/-- Fast finite zipper computation certifies the exact first-hole query
    in the original weighted-TNF known-run semantics. -/
theorem check_sound (p : PartialMachine) (n : Nat) (s : Slot)
    (h : check p n s = true) : ∃ c, knownRun p n = some c ∧ readSlot c = s := by
  have hh := of_decide_eq_true h
  change (run0 p n ⟨0,[],[]⟩).map slot0 = some s at hh
  have hz := run_project p n start
  change (Agent50Zipper.zrun p n start).map project = run0 p n ⟨0,[],[]⟩ at hz
  cases he : Agent50Zipper.zrun p n start with
  | none =>
    rw [he] at hz
    rw [← hz] at hh
    simp at hh
  | some z =>
    have hr := Agent50Zipper.zrun_sound p (weightedTNFDefaultCompletion p)
      (weightedTNFDefaultCompletion_compatible p) n start z he
    rw [start_embed] at hr
    rw [weightedTNFKnownRun_eq_defaultRun]
    refine ⟨Agent50Zipper.embed z,hr,?_⟩
    rw [← hz,he] at hh
    rw [Agent50Zipper.read_embed]
    exact Option.some.inj hh

theorem short_bound {B n : Nat} {p : PartialMachine} (hB : 3512 ≤ B)
    (hn : n ≤ 3506) : ∀ d ∈ possibleDelays p 0, d+n+1 ≤ B := by
  intro d hd
  have hd' := List.mem_range.mp (List.mem_filter.mp hd).1
  omega

theorem short_child (B : Nat) (hB : 3512 ≤ B) (mv : Move) (n : Nat)
    (hn : n ≤ 3506) (h : check (child mv) n b1 = true) :
    Cover (WeightedBound B) (child mv) := by
  obtain ⟨c,hr,hs⟩ := check_sound (child mv) n b1 h
  apply Cover.leaf
  exact last_hole_sound B (child mv) n c (by rfl) hr
    (by rw [hs]; exact child_hole mv)
    (by intro s hne; apply child_rest mv s; simpa [hs] using hne)
    (short_bound hB hn)

theorem halt_child (B : Nat) (hB : 3512 ≤ B) :
    Cover (WeightedBound B) (refine parent a1 none) := by
  obtain ⟨c,hr,hs⟩ := check_sound parent 213 a1 (by decide)
  have h := first_hole_weighted_halt B parent 213 c (by rfl) hr
    (by rw [hs]; exact parent_hole) (short_bound hB (by decide))
  rw [hs] at h
  exact .leaf _ h

theorem liftNever (B : Nat) {p : PartialMachine} (h : Cover NeverHalts p) :
    Cover (WeightedBound B) p :=
  .leaf _ (fun m hm => weighted_never B m (h.sound m hm))

theorem side_child (B : Nat) (mv : Move) (entry period : Nat) (boundary : Int)
    (hn : 0 < period) (h : fastSideCycleCheck (child mv) entry period true boundary = true) :
    Cover (WeightedBound B) (child mv) :=
  .leaf _ (fun m hm => weighted_never B m
    (fastSideCycleCheck_sound (child mv) entry period true boundary hn h m hm))

theorem forget_map (m : Machine) : forgetHaltRows m = fun s => (m s).map some := by
  funext s
  cases h : m s <;> simp [forgetHaltRows,h]

theorem child_formula (mv : Move) : child mv = fun s =>
    if s=a1 then some (some mv) else (championTable s).map some := by
  funext s
  by_cases hs : s=a1 <;> simp [child,childM,forget_map,hs]

theorem ld_child (B : Nat) : Cover (WeightedBound B) (child ⟨true,false,3⟩) := by
  rw [child_formula]
  change Cover (WeightedBound B) (BB6.Agent48SiblingCounter.table .ld)
  exact liftNever B (BB6.Agent48SiblingCounter.sibling_cover .ld)
theorem rd_child (B : Nat) : Cover (WeightedBound B) (child ⟨true,true,3⟩) := by
  rw [child_formula]
  change Cover (WeightedBound B) (BB6.Agent48SiblingCounter.table .rd)
  exact liftNever B (BB6.Agent48SiblingCounter.sibling_cover .rd)
theorem le_child (B : Nat) : Cover (WeightedBound B) (child ⟨false,false,4⟩) := by
  rw [child_formula]
  change Cover (WeightedBound B) (BB6.Agent48SiblingCounter.table .le)
  exact liftNever B (BB6.Agent48SiblingCounter.sibling_cover .le)
theorem lc_child (B : Nat) : Cover (WeightedBound B) (child ⟨true,false,2⟩) := by
  rw [child_formula]
  change Cover (WeightedBound B) BB6.Agent48SiblingLC.lc
  exact liftNever B BB6.Agent48SiblingLC.lc_cover
theorem re_child (B : Nat) : Cover (WeightedBound B) (child ⟨true,true,4⟩) := by
  rw [child_formula]
  change Cover (WeightedBound B) BB6.Agent48SiblingRE.re
  exact liftNever B BB6.Agent48SiblingRE.re_cover

/-- All 24 ordinary A1 choices; the only high-score child is the champion.
    Finite halt witnesses count ordinary transitions, excluding final query. -/
theorem ordinary_children (B : Nat) (hB : 3512 ≤ B)
    (hchamp : Cover (WeightedBound B) (forgetHaltRows championTable))
    (mv : Move) : Cover (WeightedBound B) (child mv) := by
  rcases mv with ⟨w,r,q⟩
  have hq : q = 0 ∨ q = 1 ∨ q = 2 ∨ q = 3 ∨ q = 4 ∨ q = 5 := by
    have := q.isLt
    omega
  rcases hq with h|h|h|h|h|h <;> subst q <;> cases w <;> cases r
  · exact side_child B _ 390 71 11 (by decide) (by decide)
  · exact short_child B hB _ 464 (by decide) (by decide)
  · exact short_child B hB _ 216 (by decide) (by decide)
  · rwa [champion_child]
  · exact short_child B hB _ 214 (by decide) (by decide)
  · exact short_child B hB _ 214 (by decide) (by decide)
  · exact short_child B hB _ 214 (by decide) (by decide)
  · exact short_child B hB _ 214 (by decide) (by decide)
  · exact side_child B _ 191 321 2 (by decide) (by decide)
  · exact short_child B hB _ 706 (by decide) (by decide)
  · exact lc_child B
  · exact short_child B hB _ 544 (by decide) (by decide)
  · exact short_child B hB _ 242 (by decide) (by decide)
  · exact short_child B hB _ 915 (by decide) (by decide)
  · exact ld_child B
  · exact rd_child B
  · exact le_child B
  · exact short_child B hB _ 1649 (by decide) (by decide)
  · exact short_child B hB _ 3506 (by decide) (by decide)
  · exact re_child B
  · exact short_child B hB _ 218 (by decide) (by decide)
  · exact short_child B hB _ 3312 (by decide) (by decide)
  · exact side_child B _ 272 43 11 (by decide) (by decide)
  · exact short_child B hB _ 252 (by decide) (by decide)

/-- Close all 625 canonical two-hole completions from a single bound for the
    champion leaf. This is a universally quantified cylinder statement. -/
theorem parent_cover (B : Nat) (hB : 3512 ≤ B)
    (hchamp : Cover (WeightedBound B) (forgetHaltRows championTable)) :
    Cover (WeightedBound B) parent := by
  apply Cover.branch parent a1 parent_hole
  intro t _
  cases t with
  | none => exact halt_child B hB
  | some mv => rw [← child_eq]; exact ordinary_children B hB hchamp mv

def parentSchedule : List (Nat × Slot) :=
  [(1,(1,false)), (2,(2,false)), (3,(3,true)), (4,(4,true)),
   (7,(4,false)), (8,(3,false)), (11,(2,true)), (12,(5,true)), (53,(5,false))]

theorem parent_reachable : BB6.Agent8TNFPath.FirstHolePath parent 6 :=
  BB6.Agent8TNFPath.checked_from_root parentM parentSchedule (by decide)

noncomputable def parentCertificate (B : Nat) (hB : 3512 ≤ B)
    (hchamp : Cover (WeightedBound B) (forgetHaltRows championTable)) :
    WeightedTNFCertificate B parent 6 :=
  .ofWeightedCover (forgetHaltRows_root _ (by decide))
    (forgetHaltRows_tnfSupport _) (forgetHaltRows_noAssignedHalt _)
    (parent_cover B hB hchamp)

#print axioms parent_cover
#print axioms parent_reachable
#print axioms parentCertificate
end BB6.Agent48Parent
