import SparseBlockFAR
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace BB6BlockFAR

/-- Sparse rows are their own support: no externally asserted support list. -/
def activeLookup {α : Type} (key : Nat) : List (Nat × α) → Option α
  | [] => none
  | (k,v)::r => if k = key then some v else activeLookup key r

theorem activeLookup_mem {α : Type} {key : Nat} {rows : List (Nat × α)} {v : α}
    (h : activeLookup key rows = some v) : (key,v) ∈ rows := by
  induction rows with
  | nil => simp [activeLookup] at h
  | cons hd tl ih =>
    rcases hd with ⟨k,w⟩
    by_cases hk : k = key
    · subst k
      simp [activeLookup] at h
      subst w
      exact List.mem_cons_self
    · simp [activeLookup,hk] at h
      exact List.mem_cons_of_mem _ (ih h)

private theorem code_lt (a : Sym) : a.code < 8 := by
  rcases a with ⟨a,b,c⟩
  cases a <;> cases b <;> cases c <;> decide

private theorem code_roundtrip (a : Sym) : Sym.ofCode a.code = a := by
  rcases a with ⟨a,b,c⟩
  cases a <;> cases b <;> cases c <;> decide

private theorem key_div (i : Nat) (a : Sym) : (8*i+a.code)/8 = i := by
  have h := code_lt a
  omega

private theorem key_mod (i : Nat) (a : Sym) : (8*i+a.code)%8 = a.code := by
  have h := code_lt a
  omega

structure ActiveData (d n : Nat) where
  start : Fin (d+1)
  pushRows : Nat → List (Nat × Nat)
  controlCodes : Nat → Nat
  auxiliaryCodes : Nat → Nat
  predecessorCodes : Nat → List Nat
  edgeRows : Nat → List (Nat × List Nat)
  zeroCodes : Nat
  zeroNextCodes : Nat → Nat

def ActiveData.sparse {d n} (C : ActiveData d n) : SparseData d n :=
  { start := C.start
    pushCodes := fun i => (activeLookup (i%8) (C.pushRows (i/8))).getD 0
    controlCodes := C.controlCodes
    auxiliaryCodes := C.auxiliaryCodes
    predecessorCodes := C.predecessorCodes
    edgeCodes := fun i => (activeLookup (i%8) (C.edgeRows (i/8))).getD []
    zeroCodes := C.zeroCodes
    zeroNextCodes := C.zeroNextCodes }

private theorem push_eq {d n} (C : ActiveData d n) (l : LState d) (a : Sym) :
    C.sparse.push l a =
      match (activeLookup a.code (C.pushRows l.val)).getD 0 with
      | 0 => none
      | j+1 => some (finCode d j) := by
  simp only [SparseData.push,ActiveData.sparse,key_div,key_mod]
  rfl

private theorem targets_eq {d n} (C : ActiveData d n) (v : Node n) (a : Sym) :
    C.sparse.targets v a = ((activeLookup a.code (C.edgeRows v.val)).getD []).map (finCode n) := by
  simp only [SparseData.targets,ActiveData.sparse,key_div,key_mod]

/-- The full predecessor completeness check is obtained by checking only the
    defined DFA edges. Missing keys literally have no push transition. -/
def ActiveData.fastPredAt {d n} (C : ActiveData d n) (l : LState d) : Bool :=
  (C.pushRows l.val).all fun e => C.sparse.predCheckAt l (Sym.ofCode e.1)

theorem ActiveData.fastPredAt_sound {d n} (C : ActiveData d n) (l : LState d)
    (h : C.fastPredAt l = true) : symbols.all (C.sparse.predCheckAt l) = true := by
  apply List.all_eq_true.mpr
  intro a _
  cases he : activeLookup a.code (C.pushRows l.val) with
  | none => simp [SparseData.predCheckAt,push_eq,he]
  | some v =>
    have hh := List.all_eq_true.mp h (a.code,v) (activeLookup_mem he)
    simpa only [code_roundtrip] using hh

/-- Only nonempty rows of the source NFA node can constrain inclusion. -/
def ActiveData.fastInclusion {d n} (C : ActiveData d n) (v p : Node n) : Bool :=
  (!C.sparse.zero v || C.sparse.zero p) &&
    (C.edgeRows v.val).all fun e =>
      (C.sparse.targets v (Sym.ofCode e.1)).all fun t => decide (t ∈ C.sparse.targets p (Sym.ofCode e.1))

theorem ActiveData.fastInclusion_sound {d n} (C : ActiveData d n) (v p : Node n)
    (h : C.fastInclusion v p = true) : C.sparse.inclusion v p = true := by
  simp only [ActiveData.fastInclusion,Bool.and_eq_true] at h
  simp only [SparseData.inclusion,Bool.and_eq_true]
  refine ⟨h.1,?_⟩
  apply List.all_eq_true.mpr
  intro a _
  cases he : activeLookup a.code (C.edgeRows v.val) with
  | none => simp [targets_eq,he]
  | some ts =>
    have hh := List.all_eq_true.mp h.2 (a.code,ts) (activeLookup_mem he)
    simpa only [code_roundtrip] using hh

def ActiveData.fastRow {d n} (C : ActiveData d n) (M : Table) (l : LState d) (q : Q)
    (dir : Bool) (a : Sym) : Bool :=
  let p := C.sparse.control l q dir
  if (C.sparse.targets p a).isEmpty then true else
  match blockExit M q dir a with
  | none => false
  | some e =>
    if e.dir then
      match C.sparse.push l e.w with
      | none => false
      | some j => (C.sparse.targets p a).all fun v => C.fastInclusion v (C.sparse.control j e.q true)
    else (C.sparse.predecessors l).all (C.sparse.leftCheck p a e)

theorem ActiveData.fastRow_sound {d n} (C : ActiveData d n) (M : Table) (l : LState d)
    (q : Q) (dir : Bool) (a : Sym) (h : C.fastRow M l q dir a = true) :
    C.sparse.rowCheck M l q dir a = true := by
  by_cases hz : (C.sparse.targets (C.sparse.control l q dir) a).isEmpty = true
  · simp [SparseData.rowCheck,hz]
  · simp only [ActiveData.fastRow,SparseData.rowCheck,hz,ite_false] at h ⊢
    cases he : blockExit M q dir a with
    | none => simpa [he] using h
    | some e =>
      cases hd : e.dir with
      | false => simpa [he,hd] using h
      | true =>
        cases hj : C.sparse.push l e.w with
        | none => simpa [he,hd,hj] using h
        | some j =>
          simp [he,hd,hj] at h ⊢
          intro v hv
          exact C.fastInclusion_sound _ _ (h v hv)

def ActiveData.fastRowsAt {d n} (C : ActiveData d n) (M : Table) (l : LState d) : Bool :=
  (List.finRange 6).all fun q => [false,true].all fun dir =>
    (C.edgeRows (C.sparse.control l q dir).val).all fun e => C.fastRow M l q dir (Sym.ofCode e.1)

theorem ActiveData.fastRowsAt_sound {d n} (C : ActiveData d n) (M : Table) (l : LState d)
    (h : C.fastRowsAt M l = true) : C.sparse.rowsAt M l = true := by
  apply List.all_eq_true.mpr
  intro q hq
  apply List.all_eq_true.mpr
  intro dir hd
  have h := List.all_eq_true.mp (List.all_eq_true.mp h q hq) dir hd
  apply List.all_eq_true.mpr
  intro a _
  let p := C.sparse.control l q dir
  cases he : activeLookup a.code (C.edgeRows p.val) with
  | none =>
    have ht : C.sparse.targets p a = [] := by simp [targets_eq,he]
    simp [SparseData.rowCheck,show C.sparse.targets (C.sparse.control l q dir) a = [] from ht]
  | some ts =>
    have hh := List.all_eq_true.mp h (a.code,ts) (activeLookup_mem he)
    exact C.fastRow_sound M l q dir a (by simpa only [code_roundtrip] using hh)

theorem ActiveData.valid_of_checks {d n} (C : ActiveData d n) (M : Table)
    (base : C.sparse.baseCheck = true)
    (pred : (List.finRange (d+1)).all C.fastPredAt = true)
    (rows : (List.finRange (d+1)).all (C.fastRowsAt M) = true) : C.sparse.Valid M := by
  refine ⟨base,?_,?_⟩
  · apply List.all_eq_true.mpr
    intro l hl
    exact C.fastPredAt_sound l (List.all_eq_true.mp pred l hl)
  · apply List.all_eq_true.mpr
    intro l hl
    exact C.fastRowsAt_sound M l (List.all_eq_true.mp rows l hl)

#print axioms ActiveData.valid_of_checks
end BB6BlockFAR
