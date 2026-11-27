import SparseZipper
import Lean.Elab.Tactic.Omega

namespace BB6Coverage.Agent42Crossing
open BB6Coverage Agent50Zipper

structure Ev where
  entering : Bool
  right : Bool
  q : Fin 6
  write : Bool := false
  deriving DecidableEq, Repr

inductive Mode where
  | active (q : Fin 6)
  | idle (fromRight : Bool)
  deriving DecidableEq, Repr

structure Cell where
  bit : Bool
  out : Bool
  mark : Bool
  events : List Ev
  deriving DecidableEq, Repr

-- A terminal visit has no departure. All our recurrence endpoints use state A.
def valid (p : PartialMachine) (out mark : Bool) : Bool → Mode → List Ev → Prop
  | b, .active q, [] => b = out ∧ mark = true ∧ q = 0
  | b, .idle _, [] => b = out ∧ mark = false
  | b, .active q, e::es =>
    e.entering = false ∧ p (q,b) = some (some ⟨e.write,e.right,e.q⟩) ∧
      valid p out mark e.write (.idle e.right) es
  | b, .idle fromRight, e::es =>
    e.entering = true ∧ e.right = !fromRight ∧
      valid p out mark b (.active e.q) es

def localOK (p : PartialMachine) (c : Cell) (m : Mode) : Prop :=
  valid p c.out c.mark c.bit m c.events

def iface (d : Bool) : List Ev → List (Bool × Fin 6)
  | [] => []
  | e::es => if (if e.entering then !e.right else e.right) = d
    then (e.right,e.q)::iface d es else iface d es

def edge (c : Cell) (d : Bool) := iface d c.events

-- Outward direction d; the neighboring cell's inward face is !d.
def chain (p : PartialMachine) (d : Bool) (a : List (Bool × Fin 6)) :
    List Cell → List (Bool × Fin 6) → Prop
  | [], b => a = b
  | c::cs, b => a = edge c (!d) ∧ localOK p c (.idle (!d)) ∧
      chain p d (edge c d) cs b

structure ScriptZ where
  q : Fin 6
  h : Int
  l : List Cell
  c : Cell
  r : List Cell
  deriving Repr

def ok (p : PartialMachine) (z : ScriptZ) : Prop :=
  localOK p z.c (.active z.q) ∧ chain p false (edge z.c false) z.l [] ∧
    chain p true (edge z.c true) z.r []

def view (z : ScriptZ) : Z := ⟨z.q,z.h,z.c.bit::z.l.map Cell.bit,z.r.map Cell.bit⟩
def marked (c : Cell) : Bool × Bool := (c.out,c.mark)
def finalWord (z : ScriptZ) : List (Bool × Bool) := z.l.reverse.map marked ++ marked z.c :: z.r.map marked
def origin (z : ScriptZ) : Int := z.h - z.l.length

def total (xs : List Cell) : Nat := (xs.map fun c => c.events.length).sum
def remaining (z : ScriptZ) : Nat := z.c.events.length + total z.l + total z.r

def finished (base : Int) (acc : List Bool) : List (Bool × Bool) → Option Z
  | [] => none
  | (b,m)::xs => if m then some ⟨0,base+acc.length,b::acc,xs.map Prod.fst⟩
    else finished base (b::acc) xs

def goal (z : ScriptZ) := finished (origin z) [] (finalWord z)

-- Repetition preserves interface compatibility.
theorem chain_append (p : PartialMachine) (d : Bool) (a b c : List (Bool × Fin 6))
    (xs ys : List Cell) (hx : chain p d a xs b) (hy : chain p d b ys c) :
    chain p d a (xs++ys) c := by
  induction xs generalizing a with
  | nil => simp [chain] at hx; subst b; simpa using hy
  | cons x xs ih =>
    simp only [chain, List.cons_append] at hx ⊢
    exact ⟨hx.1,hx.2.1,ih _ hx.2.2⟩

def copies {α : Type} (xs : List α) : Nat → List α
  | 0 => []
  | n+1 => xs ++ copies xs n

theorem chain_copies (p : PartialMachine) (d : Bool) (a : List (Bool × Fin 6))
    (xs : List Cell) (hx : chain p d a xs a) (n : Nat) : chain p d a (copies xs n) a := by
  induction n with
  | zero => rfl
  | succ n ih => exact chain_append p d a a a xs (copies xs n) hx ih

-- If the inward interface is exhausted, a locally idle cell has no visit left.
theorem empty_chain (p : PartialMachine) (d : Bool) (xs : List Cell)
    (h : chain p d [] xs []) : ∀ c ∈ xs, c.events = [] ∧ c.bit = c.out ∧ c.mark = false := by
  induction xs with
  | nil => simp
  | cons c cs ih =>
    simp only [chain] at h
    have ce : c.events = [] := by
      cases he : c.events with
      | nil => rfl
      | cons e es =>
        have hv := h.2.1
        simp only [localOK,he,valid] at hv
        have hi := h.1
        simp [edge,he,iface,hv.1,hv.2.1] at hi
    have hc := h.2.1
    simp [localOK,ce,valid] at hc
    have ht : chain p d [] cs [] := by simpa [edge,ce,iface] using h.2.2
    intro x hx
    simp only [List.mem_cons] at hx
    rcases hx with rfl | hx
    · exact ⟨ce,hc.1,hc.2⟩
    · exact ih ht x hx

-- A useful helper for reconstructing a marked finite tape from the left side.
theorem finished_prefix (base : Int) (acc : List Bool) (xs : List Cell) (ys : List (Bool × Bool))
    (h : ∀ c ∈ xs, c.mark = false) :
    finished base acc (xs.map marked ++ ys) =
      finished base ((xs.map Cell.out).reverse ++ acc) ys := by
  induction xs generalizing acc with
  | nil => rfl
  | cons x xs ih =>
    have hx := h x (by simp)
    have ht : ∀ c ∈ xs, c.mark = false := fun c hc => h c (by simp [hc])
    simp [marked,finished,hx,ih (x.out::acc) ht,List.append_assoc]

theorem map_eq_of_mem {α β : Type} (f g : α → β) (xs : List α)
    (h : ∀ x ∈ xs, f x = g x) : xs.map f = xs.map g := by
  induction xs with
  | nil => rfl
  | cons x xs ih => simp [h x (by simp),ih (fun y hy => h y (by simp [hy]))]

theorem stop_goal (p : PartialMachine) (z : ScriptZ) (hz : ok p z)
    (he : z.c.events = []) : goal z = some (view z) := by
  have hc := hz.1
  simp [localOK,he,valid] at hc
  have hl := empty_chain p false z.l (by simpa [edge,he,iface] using hz.2.1)
  have hr := empty_chain p true z.r (by simpa [edge,he,iface] using hz.2.2)
  unfold goal finalWord
  rw [finished_prefix _ _ _ _ (fun c h => (hl c (by simpa using h)).2.2)]
  simp only [List.map_reverse,List.reverse_reverse,List.append_nil,marked,finished,hc.2.1,ite_true]
  have hl' := map_eq_of_mem Cell.bit Cell.out z.l (fun c h => (hl c h).2.1)
  have hr' := map_eq_of_mem Cell.bit Cell.out z.r (fun c h => (hr c h).2.1)
  have hm : (z.r.map marked).map Prod.fst = z.r.map Cell.out := by
    simp [List.map_map,marked,Function.comp_def]
  rw [hm,← hl',← hr']
  simp [view,origin,hc.1,hc.2.2]

/-- Each locally valid nonterminal script admits one genuine machine move,
    consuming its departure and the matching arrival. -/
theorem progress (p : PartialMachine) (z : ScriptZ) (hz : ok p z)
    (he : z.c.events ≠ []) : ∃ z' : ScriptZ, ok p z' ∧
      step p (view z) = some (view z') ∧ goal z' = goal z ∧
      remaining z' + 2 = remaining z := by
  rcases z with ⟨q,h,l,c,r⟩
  simp only [ok] at hz
  rcases hz with ⟨hc,hl,hr⟩
  change c.events ≠ [] at he
  cases hes : c.events with
  | nil => exact (he hes).elim
  | cons e es =>
    have hv := hc
    simp only [localOK,hes,valid] at hv
    rcases hv with ⟨hen,hp,ht⟩
    let c' : Cell := {c with bit := e.write, events := es}
    cases hd : e.right with
    | false =>
      have ec : edge c false = (false,e.q)::edge c' false := by
        simp [edge,hes,iface,hen,hd,c']
      have eo : edge c true = edge c' true := by
        simp [edge,hes,iface,hen,hd,c']
      rw [ec] at hl
      cases l with
      | nil => simp [chain] at hl
      | cons x xs =>
        simp only [chain, Bool.not_false] at hl
        rcases hl with ⟨hm,hx,hxs⟩
        cases hxe : x.events with
        | nil => simp [edge,hxe,iface] at hm
        | cons f fs =>
          have hxf := hx
          simp only [localOK,hxe,valid,Bool.not_true] at hxf
          rcases hxf with ⟨hfen,hfd,hft⟩
          let x' : Cell := {x with events := fs}
          have ex : edge x true = (false,f.q)::edge x' true := by
            simp [edge,hxe,iface,hfen,hfd,x']
          have exo : edge x false = edge x' false := by
            simp [edge,hxe,iface,hfen,hfd,x']
          rw [ex] at hm
          have hq : e.q = f.q := (List.cons.inj hm).1 |> congrArg Prod.snd
          have htail : edge c' false = edge x' true := (List.cons.inj hm).2
          refine ⟨⟨e.q,h-1,xs,x',c'::r⟩,?_,?_,?_,?_⟩
          · refine ⟨?_,?_,?_⟩
            · simpa [localOK,x',hq] using hft
            · simpa [exo] using hxs
            · simp only [chain,Bool.not_true]
              exact ⟨htail.symm,by simpa [localOK,c',hd] using ht,by simpa [eo] using hr⟩
          · simp [view,step,move,hp,hd,c',x']
          · have hf : finalWord ⟨e.q,h-1,xs,x',c'::r⟩ = finalWord ⟨q,h,x::xs,c,r⟩ := by
              simp [finalWord,marked,c',x',List.append_assoc]
            have ho : origin ⟨e.q,h-1,xs,x',c'::r⟩ = origin ⟨q,h,x::xs,c,r⟩ := by
              simp [origin]; omega
            simp only [goal,hf,ho]
          · simp [remaining,total,hes,hxe,c',x']; omega
    | true =>
      have ec : edge c true = (true,e.q)::edge c' true := by
        simp [edge,hes,iface,hen,hd,c']
      have eo : edge c false = edge c' false := by
        simp [edge,hes,iface,hen,hd,c']
      rw [ec] at hr
      cases r with
      | nil => simp [chain] at hr
      | cons x xs =>
        simp only [chain, Bool.not_true] at hr
        rcases hr with ⟨hm,hx,hxs⟩
        cases hxe : x.events with
        | nil => simp [edge,hxe,iface] at hm
        | cons f fs =>
          have hxf := hx
          simp only [localOK,hxe,valid,Bool.not_false] at hxf
          rcases hxf with ⟨hfen,hfd,hft⟩
          let x' : Cell := {x with events := fs}
          have ex : edge x false = (true,f.q)::edge x' false := by
            simp [edge,hxe,iface,hfen,hfd,x']
          have exo : edge x true = edge x' true := by
            simp [edge,hxe,iface,hfen,hfd,x']
          rw [ex] at hm
          have hq : e.q = f.q := (List.cons.inj hm).1 |> congrArg Prod.snd
          have htail : edge c' true = edge x' false := (List.cons.inj hm).2
          refine ⟨⟨e.q,h+1,c'::l,x',xs⟩,?_,?_,?_,?_⟩
          · refine ⟨?_,?_,?_⟩
            · simpa [localOK,x',hq] using hft
            · simp only [chain,Bool.not_false]
              exact ⟨htail.symm,by simpa [localOK,c',hd] using ht,by simpa [eo] using hl⟩
            · simpa [exo] using hxs
          · simp [view,step,move,hp,hd,c',x']
          · have hf : finalWord ⟨e.q,h+1,c'::l,x',xs⟩ = finalWord ⟨q,h,l,c,x::xs⟩ := by
              simp [finalWord,marked,c',x',List.append_assoc]
            have ho : origin ⟨e.q,h+1,c'::l,x',xs⟩ = origin ⟨q,h,l,c,x::xs⟩ := by
              simp [origin]; omega
            simp only [goal,hf,ho]
          · simp [remaining,total,hes,hxe,c',x']; omega


theorem total_zero (xs : List Cell) (h : ∀ c ∈ xs, c.events = []) : total xs = 0 := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    have hx := h x (by simp)
    have ht := ih (fun c hc => h c (by simp [hc]))
    simp [total,hx] at ht ⊢
    exact ht

theorem stop_remaining (p : PartialMachine) (z : ScriptZ) (hz : ok p z)
    (he : z.c.events = []) : remaining z = 0 := by
  have hl := empty_chain p false z.l (by simpa [edge,he,iface] using hz.2.1)
  have hr := empty_chain p true z.r (by simpa [edge,he,iface] using hz.2.2)
  simp [remaining,he,total_zero z.l (fun c hc => (hl c hc).1),
    total_zero z.r (fun c hc => (hr c hc).1)]

/-- Soundness of an arbitrary finite script tape, in the genuine zipper step
    semantics. There is no assumed correspondence with a primitive trace:
    local transition checks and neighboring interface agreement suffice. -/
theorem sound (p : PartialMachine) (z : ScriptZ) (hz : ok p z) :
    ∃ n f, 2*n = remaining z ∧ goal z = some f ∧ zrun p n (view z) = some f := by
  by_cases he : z.c.events = []
  · exact ⟨0,view z,by simp [stop_remaining p z hz he],stop_goal p z hz he,rfl⟩
  · obtain ⟨z',hz',hs,hg,hd⟩ := progress p z hz he
    obtain ⟨n,f,hn,hf,hr⟩ := sound p z' hz'
    refine ⟨n+1,f,by omega,hg ▸ hf,?_⟩
    simp [zrun,hs,hr]
termination_by remaining z
decreasing_by omega

#print axioms sound
#print axioms chain_copies
end BB6Coverage.Agent42Crossing
