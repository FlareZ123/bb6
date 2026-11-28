import SideCycle
import Agent46AutoPump
import NGramCertificate
import Raw45ReQuadratic

set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace BB6.Agent24Raw45.ReAudit
open BB6Coverage BB6Coverage.Agent50Zipper BB6Coverage.Agent50SideCycle
open BB6Coverage.Agent31Pump

/-- Physical enumeration: destination, write bit, then direction. -/
def allSlots (f : Slot → Bool) : Bool :=
  (List.finRange 6).all fun q => [false,true].all fun a => f (q,a)

theorem allSlots_sound (f : Slot → Bool) (h : allSlots f = true) (s : Slot) : f s = true := by
  rcases s with ⟨q,a⟩
  have hq := List.all_eq_true.mp h q (List.mem_finRange q)
  have ha : a ∈ [false,true] := by cases a <;> simp
  exact List.all_eq_true.mp hq a ha

def allMoves (f : Move → Bool) : Bool :=
  (List.finRange 6).all fun q => [false,true].all fun w => [false,true].all fun r => f ⟨w,r,q⟩

theorem allMoves_sound (f : Move → Bool) (h : allMoves f = true) (mv : Move) : f mv = true := by
  rcases mv with ⟨w,r,q⟩
  have hq := List.all_eq_true.mp h q (List.mem_finRange q)
  have hw : w ∈ [false,true] := by cases w <;> simp
  have hr : r ∈ [false,true] := by cases r <;> simp
  exact List.all_eq_true.mp (List.all_eq_true.mp hq w hw) r hr

def tableOK (p q : PartialMachine) : Bool := allSlots fun s => decide (p s = q s)

theorem tableOK_sound (p q : PartialMachine) (h : tableOK p q = true) : p = q := by
  funext s
  exact of_decide_eq_true (allSlots_sound _ h s)

def queryOK (B : Nat) (p : PartialMachine) (n : Nat) (s : Slot) : Bool :=
  decide (n+1 ≤ B) && decide (p s = none) &&
    decide ((zrun p n start).map (fun z => (z.q,z.l.headD false)) = some s)

theorem query_halt (B : Nat) (p : PartialMachine) (n : Nat) (s : Slot)
    (h : queryOK B p n s = true) (m : Machine) (hm : compatible p m) (hs : m s = none) :
    DecidedBelow B m := by
  simp only [queryOK,Bool.and_eq_true,decide_eq_true_eq] at h
  cases hz : zrun p n start with
  | none => simp [hz] at h
  | some z =>
    have he : (z.q,z.l.headD false) = s := by simpa only [hz,Option.map_some,Option.some.injEq] using h.2
    have hr := zrun_sound p m hm n start z hz
    rw [start_embed] at hr
    have hread : readSlot (embed z) = s := (read_embed z).trans he
    right
    refine ⟨n,h.1.1,by simp [hr],?_⟩
    simp [run,hr,rawStep,hread,hs]

def restOK (p : PartialMachine) (hole : Slot) : Bool :=
  allSlots fun s => if s = hole then true else ((p s).bind id).isSome

theorem total_never (m : Machine) (h : ∀ s, (m s).isSome = true) : NeverHalts m := by
  intro n
  induction n with
  | zero => rfl
  | succ n ih =>
    cases hr : run m n blank with
    | none => simp [hr] at ih
    | some c => simpa only [run,hr,Option.bind_some,rawStep,Option.isSome_map] using h (readSlot c)

theorem rest_never (p : PartialMachine) (s : Slot) (h : restOK p s = true)
    (m : Machine) (hm : compatible p m) (mv : Move) (hs : m s = some mv) : NeverHalts m := by
  apply total_never m
  intro t
  by_cases he : t = s
  · simp [he,hs]
  · have hp := allSlots_sound _ h t
    simp only [he,ite_false] at hp
    cases ht : p t with
    | none => simp [ht] at hp
    | some op =>
      cases op with
      | none => simp [ht] at hp
      | some mv' => simp [hm t (some mv') ht]

/-- All proof methods are checked against the actual recursively refined table.
    Covered/proven leaves transport semantic proofs only after all twelve slots match. -/
inductive Audit (B : Nat) where
  | bad
  | last (n : Nat) (s : Slot)
  | cycle (entry period : Nat) (right : Bool) (boundary : Int)
  | pump (c : BB6Coverage.Agent31Pump.Auto.Cert)
  | ngram (c : BB6.Agent1NGram.Cert)
  | proven (q : PartialMachine) (h : ∀ m, compatible q m → NeverHalts m)
  | covered (q : PartialMachine) (h : Cover (DecidedBelow B) q)
  | split (n : Nat) (s : Slot) (kids : Move → Audit B)

def check (B : Nat) (p : PartialMachine) : Audit B → Bool
  | .bad => false
  | .last n s => queryOK B p n s && restOK p s
  | .cycle e k r b => decide (0 < k) && fastSideCycleCheck p e k r b
  | .pump c => BB6Coverage.Agent31Pump.Auto.check p c
  | .ngram c => BB6.Agent1NGram.check p c
  | .proven q _ => tableOK p q
  | .covered q _ => tableOK p q
  | .split n s kids => queryOK B p n s && allMoves fun mv => check B (refine p s (some mv)) (kids mv)
termination_by structural t => t

theorem sound (B : Nat) (p : PartialMachine) (t : Audit B) (h : check B p t = true) :
    Cover (DecidedBelow B) p := by
  induction t generalizing p with
  | bad => simp [check] at h
  | last n s =>
    have hh : queryOK B p n s = true ∧ restOK p s = true := by simpa only [check,Bool.and_eq_true] using h
    apply Cover.leaf
    intro m hm
    cases hs : m s with
    | none => exact query_halt B p n s hh.1 m hm hs
    | some mv => exact Or.inl (rest_never p s hh.2 m hm mv hs)
  | cycle e k r b =>
    have hh : 0 < k ∧ fastSideCycleCheck p e k r b = true := by simpa only [check,Bool.and_eq_true,decide_eq_true_eq] using h
    exact .leaf _ fun m hm => Or.inl (fastSideCycleCheck_sound p e k r b hh.1 hh.2 m hm)
  | pump c => exact .leaf _ fun m hm => Or.inl (BB6Coverage.Agent31Pump.Auto.check_never p c (by simpa only [check] using h) m hm)
  | ngram c => exact .leaf _ fun m hm => Or.inl (BB6.Agent1NGram.never p c (by simpa only [check] using h) m hm)
  | proven q safe =>
    have he : p = q := tableOK_sound p q (by simpa only [check] using h)
    subst q
    exact .leaf _ fun m hm => Or.inl (safe m hm)
  | covered q safe =>
    have he : p = q := tableOK_sound p q (by simpa only [check] using h)
    subst q
    exact safe
  | split n s kids ih =>
    have hh : queryOK B p n s = true ∧ allMoves (fun mv => check B (refine p s (some mv)) (kids mv)) = true := by
      simpa only [check,Bool.and_eq_true] using h
    apply Cover.leaf
    intro m hm
    cases hs : m s with
    | none => exact query_halt B p n s hh.1 m hm hs
    | some mv =>
      have hc : compatible (refine p s (some mv)) m := by simpa [hs] using compatible_refine p m s hm
      exact (ih mv (refine p s (some mv)) (allMoves_sound _ hh.2 mv)).sound m hc

def byMove {B : Nat} (xs : List (Audit B)) (mv : Move) : Audit B :=
  xs[4*mv.next.val+2*mv.write.toNat+mv.right.toNat]?.getD .bad

#print axioms sound
end BB6.Agent24Raw45.ReAudit
