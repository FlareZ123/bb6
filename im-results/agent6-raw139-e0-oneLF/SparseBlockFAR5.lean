import BlockMacro5

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace BB6.Agent6SparseBlockFAR5
open BB6BlockFAR5

/-- An executable total vector, interpreted as a binary decision tree on the
low-order index bits. Leaves denote a constant on every index below them.
The generator can compress arbitrary repeated subtrees; the invariant theorem
checks the interpreted vector, not the generator. -/
inductive VectorTrie (α : Type) where
  | leaf (value : α)
  | fork (even odd : VectorTrie α)

def VectorTrie.get {α : Type} : VectorTrie α → Nat → α
  | .leaf x, _ => x
  | .fork l r, i => if i % 2 = 0 then l.get (i / 2) else r.get (i / 2)

/-- Finite, possibly partial left DFA and a forward NFA for the right block
    word. The checker trusts neither the state abstraction nor its synthesis.
    Missing DFA edges are allowed only because every reachable left word
    is proved to have a defined path. -/
structure Data (d n : Nat) where
  start : Fin (d+1)
  pushCodes : VectorTrie Nat
  controlCodes : VectorTrie Nat
  auxiliaryCodes : VectorTrie Nat
  predecessorCodes : VectorTrie (List Nat)
  edgeCodes : VectorTrie (List (Nat × Nat))
  zeroCodes : Nat
  zeroNextCodes : VectorTrie Nat

abbrev LState (d : Nat) := Fin (d+1)
abbrev Node (n : Nat) := Fin (n+1)

def finCode (n x : Nat) : Fin (n+1) := ⟨x%(n+1),Nat.mod_lt _ (by omega)⟩

def Data.push {d n} (C : Data d n) (l : LState d) (a : Sym) : Option (LState d) :=
  match C.pushCodes.get (32*l.val+a.code) with
  | 0 => none
  | j+1 => some (finCode d j)

def Data.control {d n} (C : Data d n) (l : LState d) (q : Q) (dir : Bool) : Node n :=
  finCode n (C.controlCodes.get (12*l.val+2*q.val+dir.toNat))

def Data.auxiliary {d n} (C : Data d n) (l : LState d) (q : Q) (b : Sym) : Node n :=
  finCode n (C.auxiliaryCodes.get (192*l.val+32*q.val+b.code))

def Data.predecessors {d n} (C : Data d n) (l : LState d) : List (LState d × Sym) :=
  (C.predecessorCodes.get l.val).map fun x => (finCode d (x/32),Sym.ofCode (x%32))

/-- Only present labelled edges are stored. Missing labels have no target. -/
def Data.edges {d n} (C : Data d n) (v : Node n) : List (Sym × Node n) :=
  (C.edgeCodes.get v.val).map (fun (a,t) => (Sym.ofCode a,finCode n t))

def Data.targets {d n} (C : Data d n) (v : Node n) (a : Sym) : List (Node n) :=
  (C.edges v).filterMap (fun (b,t) => if b = a then some t else none)

theorem Data.mem_targets {d n} (C : Data d n) (v : Node n) (a : Sym) (t : Node n) :
    t ∈ C.targets v a ↔ (a,t) ∈ C.edges v := by
  unfold Data.targets
  rw [List.mem_filterMap]
  constructor
  · rintro ⟨⟨b,u⟩,hm,he⟩
    by_cases h : b = a
    · subst b
      simp at he
      subst u
      exact hm
    · simp [h] at he
  · intro h
    exact ⟨(a,t),h,by simp⟩

def Data.labels {d n} (C : Data d n) (v : Node n) : List Sym :=
  (C.edges v).map Prod.fst

theorem Data.mem_labels {d n} (C : Data d n) (v : Node n) (a : Sym) (t : Node n)
    (h : t ∈ C.targets v a) : a ∈ C.labels v :=
  List.mem_map.mpr ⟨(a,t),(C.mem_targets v a t).mp h,rfl⟩

def Data.zero {d n} (C : Data d n) (v : Node n) : Bool :=
  C.zeroCodes.testBit v.val

def Data.zeroNext {d n} (C : Data d n) (v : Node n) : Node n :=
  finCode n (C.zeroNextCodes.get v.val)

def Data.leftVal {d n} (C : Data d n) : List Sym → Option (LState d)
  | [] => some C.start
  | a::r => (C.leftVal r).bind (fun l => C.push l a)

def Data.accept {d n} (C : Data d n) : List Sym → Node n → Prop
  | [],v => C.zero v = true
  | a::r,v => ∃ t ∈ C.targets v a, C.accept r t

def Data.zeroCheck {d n} (C : Data d n) (v : Node n) : Bool :=
  if C.zero v then
    C.zero (C.zeroNext v) && decide (C.zeroNext v ∈ C.targets v Sym.zero)
  else true

def Data.baseCheck {d n} (C : Data d n) : Bool :=
  decide (C.push C.start Sym.zero = some C.start) &&
    C.zero (C.control C.start 0 true) && (List.finRange (n+1)).all C.zeroCheck

def Data.predCheckAt {d n} (C : Data d n) (l : LState d) (b : Sym) : Bool :=
  match C.push l b with
  | none => true
  | some j => decide ((l,b) ∈ C.predecessors j)

def Data.predCheck {d n} (C : Data d n) : Bool :=
  (List.finRange (d+1)).all fun l => symbols.all (C.predCheckAt l)

def Data.inclusion {d n} (C : Data d n) (v p : Node n) : Bool :=
  (!C.zero v || C.zero p) &&
    (C.edges v).all fun edge => decide (edge ∈ C.edges p)

def Data.leftCheck {d n} (C : Data d n) (p : Node n) (a : Sym) (e : Exit)
    (pre : LState d × Sym) : Bool :=
  let (l,b) := pre
  let u := C.auxiliary l e.q b
  decide (u ∈ C.targets (C.control l e.q false) b) &&
    (C.targets p a).all fun v => decide (v ∈ C.targets u e.w)

def Data.rowCheck {d n} (C : Data d n) (M : Table) (l : LState d) (q : Q)
    (dir : Bool) (a : Sym) : Bool :=
  let p := C.control l q dir
  if (C.targets p a).isEmpty then true else
  match blockExit M q dir a with
  | none => false
  | some e =>
    if e.dir then
      match C.push l e.w with
      | none => false
      | some j => (C.targets p a).all fun v => C.inclusion v (C.control j e.q true)
    else (C.predecessors l).all (C.leftCheck p a e)

def Data.rowsAt {d n} (C : Data d n) (M : Table) (l : LState d) : Bool :=
  (List.finRange 6).all fun q => [false,true].all fun dir =>
    (C.labels (C.control l q dir)).all (C.rowCheck M l q dir)

def Data.rowsCheck {d n} (C : Data d n) (M : Table) : Bool :=
  (List.finRange (d+1)).all (C.rowsAt M)

def Data.Valid {d n} (C : Data d n) (M : Table) : Prop :=
  C.baseCheck = true ∧ C.predCheck = true ∧ C.rowsCheck M = true

theorem Data.leftVal_pop {d n} (C : Data d n) (hzero : C.push C.start Sym.zero = some C.start)
    (r : List Sym) (l : LState d) (h : C.leftVal r = some l) :
    ∃ j, C.leftVal r.tail = some j ∧ C.push j (r.headD Sym.zero) = some l := by
  cases r with
  | nil =>
    simp [Data.leftVal] at h
    subst l
    exact ⟨C.start,rfl,hzero⟩
  | cons a r =>
    simp only [Data.leftVal] at h
    cases hj : C.leftVal r with
    | none => simp [hj] at h
    | some j => exact ⟨j,hj,by simpa [hj] using h⟩

theorem Data.accept_pop {d n} (C : Data d n) (hzero : ∀ v, C.zeroCheck v = true)
    (r : List Sym) (v : Node n) (h : C.accept r v) :
    ∃ t ∈ C.targets v (r.headD Sym.zero), C.accept r.tail t := by
  cases r with
  | cons a r => exact h
  | nil =>
    have hz : C.zero v = true := h
    have H := hzero v
    simp [Data.zeroCheck,hz] at H
    exact ⟨C.zeroNext v,H.2,H.1⟩

theorem Data.inclusion_sound {d n} (C : Data d n) (v p : Node n)
    (h : C.inclusion v p = true) (r : List Sym) (hr : C.accept r v) : C.accept r p := by
  simp only [Data.inclusion,Bool.and_eq_true,Bool.or_eq_true] at h
  cases r with
  | nil =>
    rcases h.1 with hv|hp
    · have h' : C.zero v = true := hr
      simp [h'] at hv
    · exact hp
  | cons a r =>
    obtain ⟨t,ht,hrest⟩ := hr
    have H := List.all_eq_true.mp h.2 (a,t) ((C.mem_targets v a t).mp ht)
    exact ⟨t,(C.mem_targets p a t).mpr (of_decide_eq_true H),hrest⟩

def Data.Invariant {d n} (C : Data d n) (c : BlockConfig) : Prop :=
  ∃ l, C.leftVal c.l = some l ∧ C.accept c.r (C.control l c.q c.dir)

theorem Data.blank_invariant {d n} (C : Data d n) (h : C.baseCheck = true) : C.Invariant blockBlank := by
  simp only [Data.baseCheck,Bool.and_eq_true,decide_eq_true_eq] at h
  exact ⟨C.start,rfl,h.1.2⟩

theorem Data.closed {d n} (C : Data d n) (M : Table) (h : C.Valid M)
    (c : BlockConfig) (hc : C.Invariant c) :
    ∃ e, blockExit M c.q c.dir (c.r.headD Sym.zero) = some e ∧ C.Invariant (c.next e.q e.dir e.w) := by
  obtain ⟨l,hl,hr⟩ := hc
  have hb := h.1
  simp only [Data.baseCheck,Bool.and_eq_true,decide_eq_true_eq] at hb
  have hz (v : Node n) : C.zeroCheck v = true := List.all_eq_true.mp hb.2 v (List.mem_finRange v)
  obtain ⟨v,hv,hrest⟩ := C.accept_pop hz c.r _ hr
  let a := c.r.headD Sym.zero
  let p := C.control l c.q c.dir
  have hrows := List.all_eq_true.mp h.2.2 l (List.mem_finRange l)
  have hq := List.all_eq_true.mp hrows c.q (List.mem_finRange c.q)
  have hdir := List.all_eq_true.mp hq c.dir (by cases c.dir <;> simp)
  have H := List.all_eq_true.mp hdir a (C.mem_labels p a v hv)
  have hn : (C.targets p a).isEmpty = false := by
    cases hh : C.targets p a with
    | nil => change v ∈ C.targets p a at hv; simp [hh] at hv
    | cons x xs => rfl
  change C.rowCheck M l c.q c.dir a = true at H
  unfold Data.rowCheck at H
  change (if (C.targets p a).isEmpty then true else _) = true at H
  rw [hn] at H
  simp only [Bool.false_eq_true,ite_false] at H
  cases he : blockExit M c.q c.dir a with
  | none => simp [he] at H
  | some e =>
    refine ⟨e,rfl,?_⟩
    rw [he] at H
    cases hed : e.dir with
    | true =>
      simp only [hed,ite_true] at H
      cases hj : C.push l e.w with
      | none => simp [hj] at H
      | some j =>
        rw [hj] at H
        have hi := List.all_eq_true.mp H v hv
        refine ⟨j,?_,?_⟩
        · simp [BlockConfig.next,Data.leftVal,hl,hj]
        · exact C.inclusion_sound v (C.control j e.q true) hi c.r.tail hrest
    | false =>
      simp only [hed,Bool.false_eq_true,ite_false] at H
      obtain ⟨j,hj,hpush⟩ := C.leftVal_pop hb.1.1 c.l l hl
      have hpc := List.all_eq_true.mp h.2.1 j (List.mem_finRange j)
      have hp := List.all_eq_true.mp hpc (c.l.headD Sym.zero) (symbols_complete _)
      unfold Data.predCheckAt at hp
      rw [hpush] at hp
      have hmem := of_decide_eq_true hp
      have hh := List.all_eq_true.mp H (j,c.l.headD Sym.zero) hmem
      simp only [Data.leftCheck,Bool.and_eq_true,decide_eq_true_eq] at hh
      refine ⟨j,?_,?_⟩
      · simpa [BlockConfig.next,hed] using hj
      · change C.accept (c.l.headD Sym.zero::e.w::c.r.tail) (C.control j e.q false)
        exact ⟨_,hh.1,v,of_decide_eq_true (List.all_eq_true.mp hh.2 v hv),hrest⟩

/-- Finite certificate soundness. Every blank-start primitive transition
    of the partial table exists; hence no missing row can ever be queried. -/
theorem Data.sound {d n} (C : Data d n) (M : Table) (h : C.Valid M) :
    ∀ k, ∃ c, run M k primBlank = some c := by
  rw [← render_blank]
  exact forever_of_invariant M C.Invariant (C.closed M h) blockBlank (C.blank_invariant h.1)

#print axioms Data.mem_targets
#print axioms Data.closed
#print axioms Data.sound
end BB6.Agent6SparseBlockFAR5

namespace BB6.Agent6SparseBlockFAR5

def rangeCheck (d : Nat) (f : Fin (d+1) → Bool) (lo len : Nat) : Bool :=
  (List.range' lo len).all (fun i => f (finCode d i))

theorem rangeCheck_join (d : Nat) (f : Fin (d+1) → Bool) (lo m n : Nat)
    (h1 : rangeCheck d f lo m = true) (h2 : rangeCheck d f (lo+m) n = true) :
    rangeCheck d f lo (m+n) = true := by
  unfold rangeCheck at h1 h2 ⊢
  rw [← List.range'_append, List.all_append, h1, Nat.one_mul, h2]
  rfl

theorem rangeCheck_full (d : Nat) (f : Fin (d+1) → Bool)
    (h : rangeCheck d f 0 (d+1) = true) : (List.finRange (d+1)).all f = true := by
  apply List.all_eq_true.mpr
  intro l _
  have hm : l.val ∈ List.range' 0 (d+1) := by simp [List.mem_range',l.isLt]
  have he : finCode d l.val = l := Fin.ext (Nat.mod_eq_of_lt l.isLt)
  simpa only [he] using List.all_eq_true.mp h l.val hm
end BB6.Agent6SparseBlockFAR5
