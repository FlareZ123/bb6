import Box27OrbitTree
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace BB6.Agent49.Box27PrefixTrace
open BB6Coverage BB6Coverage.Agent50Zipper BB6Coverage.Agent31Pump
open BB6Coverage.Agent10ZipAudit BB6Coverage.Agent50SideCycle BB6.Agent13BlankDelay
open BB6.Agent49.Box27Slice (Good split_good automata_sound)
open BB6.Agent49.Box27OrbitTree (Tree split_ef_good canSplit reps representative)
open BB6.Agent13.Box17 (decode slot Witness tableEq tableEq_sound ordinaryExcept ordinaryExcept_sound)

structure Trace where
  past : Array Z
  now : Z

def Trace.n (t : Trace) : Nat := t.past.size
def Trace.at (t : Trace) (i : Nat) : Option Z :=
  if i = t.n then some t.now else t.past[i]?
def Valid (m : Machine) (t : Trace) : Prop :=
  run m t.n blank = some (embed t.now) ∧
  ∀ i < t.n, run m i blank = (t.past[i]?).map embed

def initial : Trace := ⟨#[],start⟩
theorem initial_valid (m : Machine) : Valid m initial := by
  constructor
  · change some blank = some (embed start)
    rw [start_embed]
  · intro i hi
    change i < 0 at hi
    omega

theorem at_sound (m : Machine) (t : Trace) (ht : Valid m t) (i : Nat) (hi : i ≤ t.n) :
    run m i blank = (t.at i).map embed := by
  unfold Trace.at
  split
  · rename_i h; subst i; exact ht.1
  · exact ht.2 i (by omega)

def advance (p : PartialMachine) (t : Trace) : Option Trace :=
  (step p t.now).map fun z => ⟨t.past.push t.now,z⟩

theorem advance_sound (p : PartialMachine) (m : Machine) (hm : compatible p m)
    (t u : Trace) (ht : Valid m t) (h : advance p t = some u) : Valid m u ∧ u.n = t.n + 1 := by
  unfold advance at h
  cases hs : step p t.now with
  | none => simp [hs] at h
  | some z =>
    have he : ⟨t.past.push t.now,z⟩ = u := by simpa [hs] using h
    subst u
    have hz : zrun p 1 t.now = some z := by simp [zrun,hs]
    have hr := zrun_sound p m hm 1 t.now z hz
    have hn : (Trace.mk (t.past.push t.now) z).n = t.n+1 := by simp [Trace.n]
    refine ⟨⟨?_,?_⟩,hn⟩
    · rw [hn,run_append,ht.1]; exact hr
    · intro i hi
      rw [hn] at hi
      change run m i blank = ((t.past.push t.now)[i]?).map embed
      rw [Array.getElem?_push]
      by_cases he : i=t.n
      · subst i
        rw [if_pos (show t.n = t.past.size from rfl)]
        exact ht.1
      · have hh : i < t.n := by omega
        have hne : i ≠ t.past.size := he
        simp only [hne,ite_false]
        exact ht.2 i hh

def advanceN (p : PartialMachine) : Nat → Trace → Option Trace
  | 0,t => some t
  | k+1,t => (advance p t).bind (advanceN p k)

theorem advanceN_sound (p : PartialMachine) (m : Machine) (hm : compatible p m)
    (k : Nat) (t u : Trace) (ht : Valid m t) (h : advanceN p k t = some u) :
    Valid m u ∧ u.n = t.n+k := by
  induction k generalizing t with
  | zero => have he : t=u := Option.some.inj h; subst u; exact ⟨ht,by omega⟩
  | succ k ih =>
    cases hs : advance p t with
    | none => simp [advanceN,hs] at h
    | some v =>
      obtain ⟨hv,hn⟩ := advance_sound p m hm t v ht hs
      have hh : advanceN p k v = some u := by simpa [advanceN,hs] using h
      obtain ⟨hu,he⟩ := ih v hv hh
      exact ⟨hu,by omega⟩

def untilStop (p : PartialMachine) : Nat → Trace → Trace
  | 0,t => t
  | k+1,t => match advance p t with | none => t | some u => untilStop p k u

theorem untilStop_sound (p : PartialMachine) (m : Machine) (hm : compatible p m)
    (k : Nat) (t : Trace) (ht : Valid m t) : Valid m (untilStop p k t) := by
  induction k generalizing t with
  | zero => exact ht
  | succ k ih =>
    cases hs : advance p t with
    | none => simpa [untilStop,hs] using ht
    | some u => simpa [untilStop,hs] using ih u (advance_sound p m hm t u ht hs).1

def toTime (p : PartialMachine) (t : Trace) (n : Nat) : Option Trace :=
  if t.n ≤ n then advanceN p (n-t.n) t else none

theorem toTime_sound (p : PartialMachine) (m : Machine) (hm : compatible p m)
    (t u : Trace) (ht : Valid m t) (n : Nat) (h : toTime p t n = some u) : Valid m u ∧ u.n = n := by
  unfold toTime at h
  split at h
  · rename_i hn
    obtain ⟨hv,he⟩ := advanceN_sound p m hm (n-t.n) t u ht h
    exact ⟨hv,by omega⟩
  · contradiction

def read (t : Trace) : Slot := (t.now.q,t.now.l.headD false)

theorem halt_at (B : Nat) (m : Machine) (t : Trace) (ht : Valid m t)
    (hh : m (read t) = none) (hb : t.n+6 ≤ B) : WeightedBound B m := by
  have hhalt : HaltsAfter m t.n := by
    constructor
    · rw [ht.1]; rfl
    · change (run m t.n blank).bind (rawStep m) = none
      rw [ht.1]
      change (rawStep m (embed t.now)) = none
      unfold rawStep
      rw [read_embed]
      change (m (read t)).map _ = none
      rw [hh]
      rfl
  intro k d hk hd
  have he := halting_time_unique m k t.n hk hhalt
  have hlt : d<6 := List.mem_range.mp (List.mem_filter.mp hd).1
  omega

def haltCheck (B : Nat) (p : PartialMachine) (t : Trace) (n : Nat) : Bool :=
  match toTime p t n with
  | none => false
  | some u => decide (p (read u) = some none) && decide (n+6 ≤ B)

theorem haltCheck_sound (B : Nat) (p : PartialMachine) (t : Trace) (n : Nat)
    (h : haltCheck B p t n = true) (m : Machine) (hm : compatible p m) (ht : Valid m t) : WeightedBound B m := by
  unfold haltCheck at h
  split at h
  · contradiction
  · rename_i u hu
    obtain ⟨hv,hn⟩ := toTime_sound p m hm t u ht n hu
    have h' := Bool.and_eq_true_iff.mp h
    exact halt_at B m u hv (hm (read u) none (of_decide_eq_true h'.1)) (by rw [hn]; exact of_decide_eq_true h'.2)

def lastCheck (B : Nat) (p : PartialMachine) (t : Trace) (i : Fin 12) (n : Nat) : Bool :=
  ordinaryExcept p (slot i) && haltCheck B (refine p (slot i) none) t n

theorem lastCheck_sound (B : Nat) (p : PartialMachine) (t : Trace) (i : Fin 12) (n : Nat)
    (h : lastCheck B p t i n = true) (m : Machine) (hm : compatible p m) (ht : Valid m t) : WeightedBound B m := by
  have hh := Bool.and_eq_true_iff.mp h
  cases he : m (slot i) with
  | none =>
    apply haltCheck_sound B _ t n hh.2 m _ ht
    simpa [he] using compatible_refine p m (slot i) hm
  | some mv => exact weighted_of_never B m (ordinaryExcept_sound p (slot i) hh.1 m hm ⟨mv,he⟩)

def sideAt (t : Trace) (right : Bool) (boundary : Int) (i : Nat) : Bool :=
  match t.at i with | none => false | some z => decide (side right boundary z.h)

def cycleCheck (p : PartialMachine) (t : Trace) (entry period : Nat) (right : Bool) (boundary : Int) : Bool :=
  decide (0<period) && match toTime p t (entry+period) with
    | none => false
    | some u => match u.at entry with
      | none => false
      | some c => zipTailEq right boundary c u.now &&
        (List.range period).all (fun j => sideAt u right boundary (entry+j))

theorem cycleCheck_sound (p : PartialMachine) (t : Trace) (entry period : Nat) (right : Bool) (boundary : Int)
    (h : cycleCheck p t entry period right boundary = true) (m : Machine) (hm : compatible p m) (ht : Valid m t) : NeverHalts m := by
  have hh := Bool.and_eq_true_iff.mp h
  have hpos : 0<period := of_decide_eq_true hh.1
  have hc := hh.2
  split at hc
  · contradiction
  · rename_i u hu
    obtain ⟨hv,hn⟩ := toTime_sound p m hm t u ht (entry+period) hu
    split at hc
    · contradiction
    · rename_i c he
      have hcheck := Bool.and_eq_true_iff.mp hc
      obtain ⟨hδ,hrel⟩ := zipTailEq_sound right boundary c u.now hcheck.1
      have hs := at_sound m u hv entry (by omega)
      rw [he] at hs
      change run m entry blank = some (embed c) at hs
      have hloop : run m period (embed c) = some (embed u.now) := by
        have he := hv.1
        rw [hn,run_append,hs] at he
        exact he
      apply sideCycle_never m right boundary (u.now.h-c.h) (embed c) (embed u.now) entry period hpos hδ hs ?_ hloop hrel
      intro j hj e he'
      have hside := List.all_eq_true.mp hcheck.2 j (List.mem_range.mpr hj)
      have hrun := at_sound m u hv (entry+j) (by omega)
      rw [run_append,hs,Option.bind_some,he'] at hrun
      unfold sideAt at hside
      split at hside
      · contradiction
      · rename_i z hz
        rw [hz] at hrun
        have heq : e = embed z := Option.some.inj hrun
        subst e
        exact of_decide_eq_true hside

def leaf (B : Nat) (known : Array PartialMachine) (p : PartialMachine) (t : Trace) : Witness → Bool
  | .halt n => haltCheck B p t n
  | .last i n => lastCheck B p t i n
  | .cycle e k r b => cycleCheck p t e k r b
  | .cert i => match known[i]? with | some q => tableEq p q | none => false

theorem leaf_sound (B : Nat) (known : Array PartialMachine)
    (hknown : ∀ (i : Nat) (q : PartialMachine), known[i]? = some q → Good B q)
    (p : PartialMachine) (t : Trace) (w : Witness) (h : leaf B known p t w = true)
    (m : Machine) (hm : compatible p m) (ht : Valid m t) : WeightedBound B m := by
  cases w with
  | halt n => exact haltCheck_sound B p t n h m hm ht
  | last i n => exact lastCheck_sound B p t i n h m hm ht
  | cycle e k r b => exact weighted_of_never B m (cycleCheck_sound p t e k r b h m hm ht)
  | cert i =>
    cases he : known[i]? with
    | none => simp [leaf,he] at h
    | some q =>
      have heq : p=q := tableEq_sound p q (by simpa [leaf,he] using h)
      exact hknown i q he m (heq ▸ hm)

/-- Prefix sharing: simulate the known segment once before refining a slot.
The prefix is retained even for the symmetry branch; the latter uses a
fresh trace for the conjugate soundness rule, so audit it separately. -/
def audit (B : Nat) (known : Array PartialMachine) (cap : Nat) : Nat → PartialMachine → Trace → Tree → Bool
  | _,p,t,.terminal w => leaf B known p t w
  | _,p,_,.automata c => BB6.Agent4Automata.check p c
  | 0,_,_,.branch _ _ | 0,_,_,.orbit _ _ => false
  | k+1,p,t,.branch s kids =>
    let u := untilStop p cap t
    (kids.map Prod.fst == List.finRange 25) &&
    kids.all (fun (v,c) => audit B known cap k (refine p (slot s) (decode v)) u c)
  | k+1,p,_,.orbit s kids =>
    canSplit p s && (kids.map Prod.fst == reps) &&
    kids.all (fun (v,c) => audit B known cap k (refine p (slot s) (decode v)) initial c)

theorem audit_sound (B : Nat) (known : Array PartialMachine)
    (hknown : ∀ (i : Nat) (q : PartialMachine), known[i]? = some q → Good B q) (cap fuel : Nat)
    (p : PartialMachine) (t : Trace) (tree : Tree) (h : audit B known cap fuel p t tree = true)
    (m : Machine) (hm : compatible p m) (ht : Valid m t) : WeightedBound B m := by
  induction fuel generalizing p t tree m with
  | zero =>
    cases tree with
    | terminal w => exact leaf_sound B known hknown p t w h m hm ht
    | automata c => exact automata_sound B p c h m hm
    | branch s kids | orbit s kids => contradiction
  | succ fuel ih =>
    cases tree with
    | terminal w => exact leaf_sound B known hknown p t w h m hm ht
    | automata c => exact automata_sound B p c h m hm
    | branch s kids =>
      simp only [audit,Bool.and_eq_true,beq_iff_eq] at h
      obtain ⟨v,hv⟩ := BB6.Agent49.Box27Slice.decode_surjective (m (slot s))
      have hmem : v ∈ kids.map Prod.fst := by rw [h.1]; simp
      obtain ⟨⟨w,c⟩,hmem,he⟩ := List.mem_map.mp hmem
      dsimp at he
      subst w
      apply ih (refine p (slot s) (decode v)) (untilStop p cap t) c (List.all_eq_true.mp h.2 (v,c) hmem) m
      · rw [hv]; exact compatible_refine p m (slot s) hm
      · exact untilStop_sound p m hm cap t ht
    | orbit s kids =>
      simp only [audit,Bool.and_eq_true,beq_iff_eq] at h
      apply split_ef_good B p s h.1.1 ?_ m hm
      intro v hv m' hm'
      have hmem : v ∈ kids.map Prod.fst := by rw [h.1.2]; simp [reps,hv]
      obtain ⟨⟨w,c⟩,hmem,he⟩ := List.mem_map.mp hmem
      dsimp at he
      subst w
      exact ih _ initial c (List.all_eq_true.mp h.2 (v,c) hmem) m' hm' (initial_valid m')

theorem check_sound (B : Nat) (known : Array PartialMachine)
    (hknown : ∀ (i : Nat) (q : PartialMachine), known[i]? = some q → Good B q) (cap fuel : Nat)
    (p : PartialMachine) (tree : Tree) (h : audit B known cap fuel p initial tree = true) : Good B p := by
  intro m hm
  exact audit_sound B known hknown cap fuel p initial tree h m hm (initial_valid m)

#print axioms check_sound
end BB6.Agent49.Box27PrefixTrace
