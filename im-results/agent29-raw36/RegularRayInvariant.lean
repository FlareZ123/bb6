import ClosedGrowth
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
namespace BB6.Agent29RegularRay
open BB6Coverage BB6Coverage.Agent31Pump BB6.Agent29ClosedGrowth

/-- A finite word summary reads the finite tape ray from its far end to
    its head end. The empty list is state 0; no zero self-loop is required. -/
structure RayDFA where
  trans : Array (Nat × Nat)
  deriving Repr

def RayDFA.push (d : RayDFA) (s : Nat) (b : Bool) : Nat :=
  let ab := d.trans[s]?.getD (0,0)
  if b then ab.2 else ab.1

def RayDFA.summary (d : RayDFA) : List Bool → Nat
  | [] => 0
  | b::xs => d.push (d.summary xs) b

def RayDFA.valid (d : RayDFA) : Bool :=
  decide (0 < d.trans.size) && (List.range d.trans.size).all (fun i =>
    decide (d.push i false < d.trans.size) && decide (d.push i true < d.trans.size))

theorem RayDFA.summary_lt (d : RayDFA) (h : d.valid = true) (xs : List Bool) :
    d.summary xs < d.trans.size := by
  simp only [RayDFA.valid,Bool.and_eq_true] at h
  obtain ⟨h0,hs⟩ := h
  induction xs with
  | nil => simpa [RayDFA.summary] using h0
  | cons b xs ih =>
    have hb := List.all_eq_true.mp hs (d.summary xs) (List.mem_range.mpr ih)
    simp only [Bool.and_eq_true] at hb
    cases b
    · exact of_decide_eq_true hb.1
    · exact of_decide_eq_true hb.2

/-- The empty word contributes a distinguished 0-read self-pop. All other
    predecessors are genuine transitions of the finite word summary. -/
def RayDFA.pred (d : RayDFA) (s : Nat) (b : Bool) : List Nat :=
  (if s == 0 && !b then [0] else []) ++
  (List.range d.trans.size).filter (fun i => d.push i b == s)

theorem RayDFA.pop_mem (d : RayDFA) (h : d.valid = true) (xs : List Bool) :
    d.summary xs.tail ∈ d.pred (d.summary xs) (xs.headD false) := by
  cases xs with
  | nil => simp [RayDFA.pred,RayDFA.summary]
  | cons b xs =>
    apply List.mem_append.mpr
    right
    simp only [RayDFA.pred,List.tail_cons,List.headD_cons,RayDFA.summary,List.mem_filter,List.mem_range,beq_self_eq_true, and_true]
    exact d.summary_lt h xs

structure Certificate where
  left : RayDFA
  right : RayDFA
  rows : Array (Array (List Nat))
  deriving Repr

def Certificate.row (c : Certificate) (q : Fin 6) (l : Nat) : List Nat :=
  ((c.rows[q.val]?.getD #[])[l]?.getD [])

def Certificate.mem (c : Certificate) (q : Fin 6) (l r : Nat) : Bool :=
  (c.row q l).contains r

def Certificate.invariant (c : Certificate) (z : Z0) : Prop :=
  c.mem z.q (c.left.summary z.l) (c.right.summary z.r) = true

def Certificate.closedAt (c : Certificate) (p : PartialMachine) (q : Fin 6) (l r : Nat) : Bool :=
  [false,true].all fun a => (c.left.pred l a).all fun ll =>
    match p (q,a) with
    | some (some mv) =>
      if mv.right then
        [false,true].all fun b => (c.right.pred r b).all fun rr =>
          c.mem mv.next (c.left.push (c.left.push ll mv.write) b) rr
      else c.mem mv.next ll (c.right.push r mv.write)
    | _ => false

def Certificate.check (c : Certificate) (p : PartialMachine) : Bool :=
  c.left.valid && c.right.valid && c.mem 0 0 0 &&
    (List.finRange 6).all (fun q => (List.range c.left.trans.size).all (fun l =>
      (c.row q l).all (fun r => c.closedAt p q l r)))

theorem Certificate.sound (c : Certificate) (p : PartialMachine) (h : c.check p = true) :
    ∀ m, compatible p m → NeverHalts m := by
  simp only [Certificate.check,Bool.and_eq_true] at h
  obtain ⟨⟨⟨hl,hr⟩,h0⟩,hc⟩ := h
  apply never_of_invariant p c.invariant 0 ⟨0,[],[]⟩ rfl h0
  intro z hz
  obtain ⟨q,l,r⟩ := z
  let ls := c.left.summary l
  let rs := c.right.summary r
  let a := l.headD false
  let ll := c.left.summary l.tail
  have hmem : rs ∈ c.row q ls := List.contains_iff_mem.mp hz
  have hqa := List.all_eq_true.mp hc q (List.mem_finRange q)
  have hla := List.all_eq_true.mp hqa ls (List.mem_range.mpr (c.left.summary_lt hl l))
  have hclose := List.all_eq_true.mp hla rs hmem
  unfold Certificate.closedAt at hclose
  have ha : a ∈ [false,true] := by cases h : a <;> simp [h]
  have hpop := List.all_eq_true.mp (List.all_eq_true.mp hclose a ha) ll (c.left.pop_mem hl l)
  cases hp : p (q,a) with
  | none => simp [hp] at hpop
  | some tr =>
    cases tr with
    | none => simp [hp] at hpop
    | some mv =>
      refine ⟨1,move0 mv ⟨q,l,r⟩,by omega,?_,?_⟩
      · change (((p (q,a)).bind id).map (fun mv => move0 mv ⟨q,l,r⟩) ).bind (run0 p 0) = some (move0 mv ⟨q,l,r⟩)
        rw [hp];rfl
      · cases hd : mv.right with
        | false =>
          simpa [hp,hd,Certificate.invariant,move0,RayDFA.summary,ls,rs,ll] using hpop
        | true =>
          simp only [hp,hd,ite_true] at hpop
          let b := r.headD false
          have hb : b ∈ [false,true] := by cases h : b <;> simp [h]
          have hright := List.all_eq_true.mp (List.all_eq_true.mp hpop b hb) (c.right.summary r.tail) (c.right.pop_mem hr r)
          simpa [Certificate.invariant,move0,hd,RayDFA.summary,ls,rs,ll,b] using hright
#print axioms Certificate.sound
end BB6.Agent29RegularRay
