import BlockFAR

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace BB6BlockFAR

/-- Finite, possibly partial left DFA and a forward NFA for the right block
    word. The checker trusts neither the state abstraction nor its synthesis.
    Missing DFA edges are allowed only because every reachable left word
    is proved to have a defined path. -/
structure SparseData (d n : Nat) where
  start : Fin (d+1)
  pushCodes : Nat → Nat
  controlCodes : Nat → Nat
  auxiliaryCodes : Nat → Nat
  predecessorCodes : Nat → List Nat
  edgeCodes : Nat → List Nat
  zeroCodes : Nat
  zeroNextCodes : Nat → Nat

def SparseData.push {d n} (C : SparseData d n) (l : LState d) (a : Sym) : Option (LState d) :=
  match C.pushCodes (8*l.val+a.code) with
  | 0 => none
  | j+1 => some (finCode d j)

def SparseData.control {d n} (C : SparseData d n) (l : LState d) (q : Q) (dir : Bool) : Node n :=
  finCode n (C.controlCodes (12*l.val+2*q.val+dir.toNat))

def SparseData.auxiliary {d n} (C : SparseData d n) (l : LState d) (q : Q) (b : Sym) : Node n :=
  finCode n (C.auxiliaryCodes (48*l.val+8*q.val+b.code))

def SparseData.predecessors {d n} (C : SparseData d n) (l : LState d) : List (LState d × Sym) :=
  (C.predecessorCodes l.val).map fun x => (finCode d (x/8),Sym.ofCode (x%8))

def SparseData.targets {d n} (C : SparseData d n) (v : Node n) (a : Sym) : List (Node n) :=
  (C.edgeCodes (8*v.val+a.code)).map (finCode n)

def SparseData.zero {d n} (C : SparseData d n) (v : Node n) : Bool :=
  C.zeroCodes.testBit v.val

def SparseData.zeroNext {d n} (C : SparseData d n) (v : Node n) : Node n :=
  finCode n (C.zeroNextCodes v.val)

def SparseData.leftVal {d n} (C : SparseData d n) : List Sym → Option (LState d)
  | [] => some C.start
  | a::r => (C.leftVal r).bind (fun l => C.push l a)

def SparseData.accept {d n} (C : SparseData d n) : List Sym → Node n → Prop
  | [],v => C.zero v = true
  | a::r,v => ∃ t ∈ C.targets v a, C.accept r t

def SparseData.zeroCheck {d n} (C : SparseData d n) (v : Node n) : Bool :=
  if C.zero v then
    C.zero (C.zeroNext v) && decide (C.zeroNext v ∈ C.targets v Sym.zero)
  else true

def SparseData.baseCheck {d n} (C : SparseData d n) : Bool :=
  decide (C.push C.start Sym.zero = some C.start) &&
    C.zero (C.control C.start 0 true) && (List.finRange (n+1)).all C.zeroCheck

def SparseData.predCheckAt {d n} (C : SparseData d n) (l : LState d) (b : Sym) : Bool :=
  match C.push l b with
  | none => true
  | some j => decide ((l,b) ∈ C.predecessors j)

def SparseData.predCheck {d n} (C : SparseData d n) : Bool :=
  (List.finRange (d+1)).all fun l => symbols.all (C.predCheckAt l)

def SparseData.inclusion {d n} (C : SparseData d n) (v p : Node n) : Bool :=
  (!C.zero v || C.zero p) &&
    symbols.all fun a => (C.targets v a).all fun t => decide (t ∈ C.targets p a)

def SparseData.leftCheck {d n} (C : SparseData d n) (p : Node n) (a : Sym) (e : Exit)
    (pre : LState d × Sym) : Bool :=
  let (l,b) := pre
  let u := C.auxiliary l e.q b
  decide (u ∈ C.targets (C.control l e.q false) b) &&
    (C.targets p a).all fun v => decide (v ∈ C.targets u e.w)

def SparseData.rowCheck {d n} (C : SparseData d n) (M : Table) (l : LState d) (q : Q)
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

def SparseData.rowsAt {d n} (C : SparseData d n) (M : Table) (l : LState d) : Bool :=
  (List.finRange 6).all fun q => [false,true].all fun dir => symbols.all (C.rowCheck M l q dir)

def SparseData.rowsCheck {d n} (C : SparseData d n) (M : Table) : Bool :=
  (List.finRange (d+1)).all (C.rowsAt M)

def SparseData.Valid {d n} (C : SparseData d n) (M : Table) : Prop :=
  C.baseCheck = true ∧ C.predCheck = true ∧ C.rowsCheck M = true

theorem SparseData.leftVal_pop {d n} (C : SparseData d n) (hzero : C.push C.start Sym.zero = some C.start)
    (r : List Sym) (l : LState d) (h : C.leftVal r = some l) :
    ∃ j, C.leftVal r.tail = some j ∧ C.push j (r.headD Sym.zero) = some l := by
  cases r with
  | nil =>
    simp [SparseData.leftVal] at h
    subst l
    exact ⟨C.start,rfl,hzero⟩
  | cons a r =>
    simp only [SparseData.leftVal] at h
    cases hj : C.leftVal r with
    | none => simp [hj] at h
    | some j => exact ⟨j,hj,by simpa [hj] using h⟩

theorem SparseData.accept_pop {d n} (C : SparseData d n) (hzero : ∀ v, C.zeroCheck v = true)
    (r : List Sym) (v : Node n) (h : C.accept r v) :
    ∃ t ∈ C.targets v (r.headD Sym.zero), C.accept r.tail t := by
  cases r with
  | cons a r => exact h
  | nil =>
    have hz : C.zero v = true := h
    have H := hzero v
    simp [SparseData.zeroCheck,hz] at H
    exact ⟨C.zeroNext v,H.2,H.1⟩

theorem SparseData.inclusion_sound {d n} (C : SparseData d n) (v p : Node n)
    (h : C.inclusion v p = true) (r : List Sym) (hr : C.accept r v) : C.accept r p := by
  simp only [SparseData.inclusion,Bool.and_eq_true,Bool.or_eq_true] at h
  cases r with
  | nil =>
    rcases h.1 with hv|hp
    · have h' : C.zero v = true := hr
      simp [h'] at hv
    · exact hp
  | cons a r =>
    obtain ⟨t,ht,hrest⟩ := hr
    have H := List.all_eq_true.mp h.2 a (symbols_complete a)
    exact ⟨t,of_decide_eq_true (List.all_eq_true.mp H t ht),hrest⟩

def SparseData.Invariant {d n} (C : SparseData d n) (c : BlockConfig) : Prop :=
  ∃ l, C.leftVal c.l = some l ∧ C.accept c.r (C.control l c.q c.dir)

theorem SparseData.blank_invariant {d n} (C : SparseData d n) (h : C.baseCheck = true) : C.Invariant blockBlank := by
  simp only [SparseData.baseCheck,Bool.and_eq_true,decide_eq_true_eq] at h
  exact ⟨C.start,rfl,h.1.2⟩

theorem SparseData.closed {d n} (C : SparseData d n) (M : Table) (h : C.Valid M)
    (c : BlockConfig) (hc : C.Invariant c) :
    ∃ e, blockExit M c.q c.dir (c.r.headD Sym.zero) = some e ∧ C.Invariant (c.next e.q e.dir e.w) := by
  obtain ⟨l,hl,hr⟩ := hc
  have hb := h.1
  simp only [SparseData.baseCheck,Bool.and_eq_true,decide_eq_true_eq] at hb
  have hz (v : Node n) : C.zeroCheck v = true := List.all_eq_true.mp hb.2 v (List.mem_finRange v)
  obtain ⟨v,hv,hrest⟩ := C.accept_pop hz c.r _ hr
  let a := c.r.headD Sym.zero
  let p := C.control l c.q c.dir
  have hrows := List.all_eq_true.mp h.2.2 l (List.mem_finRange l)
  have hq := List.all_eq_true.mp hrows c.q (List.mem_finRange c.q)
  have hdir := List.all_eq_true.mp hq c.dir (by cases c.dir <;> simp)
  have H := List.all_eq_true.mp hdir a (symbols_complete a)
  have hn : (C.targets p a).isEmpty = false := by
    cases hh : C.targets p a with
    | nil => change v ∈ C.targets p a at hv; simp [hh] at hv
    | cons x xs => rfl
  change C.rowCheck M l c.q c.dir a = true at H
  unfold SparseData.rowCheck at H
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
        · simp [BlockConfig.next,SparseData.leftVal,hl,hj]
        · exact C.inclusion_sound v (C.control j e.q true) hi c.r.tail hrest
    | false =>
      simp only [hed,Bool.false_eq_true,ite_false] at H
      obtain ⟨j,hj,hpush⟩ := C.leftVal_pop hb.1.1 c.l l hl
      have hpc := List.all_eq_true.mp h.2.1 j (List.mem_finRange j)
      have hp := List.all_eq_true.mp hpc (c.l.headD Sym.zero) (symbols_complete _)
      unfold SparseData.predCheckAt at hp
      rw [hpush] at hp
      have hmem := of_decide_eq_true hp
      have hh := List.all_eq_true.mp H (j,c.l.headD Sym.zero) hmem
      simp only [SparseData.leftCheck,Bool.and_eq_true,decide_eq_true_eq] at hh
      refine ⟨j,?_,?_⟩
      · simpa [BlockConfig.next,hed] using hj
      · change C.accept (c.l.headD Sym.zero::e.w::c.r.tail) (C.control j e.q false)
        exact ⟨_,hh.1,v,of_decide_eq_true (List.all_eq_true.mp hh.2 v hv),hrest⟩

/-- Finite certificate soundness. Every blank-start primitive transition
    of the partial table exists; hence no missing row can ever be queried. -/
theorem SparseData.sound {d n} (C : SparseData d n) (M : Table) (h : C.Valid M) :
    ∀ k, ∃ c, run M k primBlank = some c := by
  rw [← render_blank]
  exact forever_of_invariant M C.Invariant (C.closed M h) blockBlank (C.blank_invariant h.1)

#print axioms SparseData.closed
#print axioms SparseData.sound
end BB6BlockFAR
