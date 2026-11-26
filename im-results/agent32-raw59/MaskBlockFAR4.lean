import BlockFAR4
import MaskMap

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace BB6BlockFAR4
open BB6.Agent32MaskBiDFA (Map Cell listMask listMask_mem subset subset_sound)

private theorem code_roundtrip (a : Sym) : Sym.ofCode a.code = a := by
  rcases a with ⟨a,b,c,d⟩
  cases a <;> cases b <;> cases c <;> cases d <;> decide

/-- Sparse NFA with actual bitset edge relation and a sparse push domain.
    The list in each edge cell is used only for enumeration; coverage of the
    mask is checked before it can establish any universal property. -/
structure MaskData (d n : Nat) where
  start : LState d
  pushRows : Map (Map Nat)
  controlCodes : Map Nat
  auxiliaryCodes : Map Nat
  predecessorCodes : Map (List Nat)
  edgeRows : Map (Map Cell)
  zeroCodes : Nat
  zeroNextCodes : Map Nat

def MaskData.pushRow {d n} (C : MaskData d n) (l : LState d) : Map Nat :=
  (C.pushRows.lookup l.val).getD .empty

def MaskData.push {d n} (C : MaskData d n) (l : LState d) (a : Sym) : Option (LState d) :=
  match (C.pushRow l).lookup a.code with
  | none => none
  | some j => some (finCode d j)

def MaskData.control {d n} (C : MaskData d n) (l : LState d) (q : Q) (dir : Bool) : Node n :=
  finCode n ((C.controlCodes.lookup (12*l.val+2*q.val+dir.toNat)).getD n)

def MaskData.auxiliary {d n} (C : MaskData d n) (l : LState d) (q : Q) (b : Sym) : Node n :=
  finCode n ((C.auxiliaryCodes.lookup (96*l.val+16*q.val+b.code)).getD n)

def MaskData.predecessors {d n} (C : MaskData d n) (l : LState d) : List (LState d × Sym) :=
  ((C.predecessorCodes.lookup l.val).getD []).map fun x => (finCode d (x/16),Sym.ofCode (x%16))

def MaskData.edges {d n} (C : MaskData d n) (v : Node n) : Map Cell :=
  (C.edgeRows.lookup v.val).getD .empty

def MaskData.cell {d n} (C : MaskData d n) (v : Node n) (a : Nat) : Cell :=
  ((C.edges v).lookup a).getD ⟨0,[]⟩

def MaskData.target {d n} (C : MaskData d n) (v : Node n) (a : Sym) (t : Node n) : Bool :=
  (C.cell v a.code).mask.testBit t.val

def MaskData.zero {d n} (C : MaskData d n) (v : Node n) : Bool := C.zeroCodes.testBit v.val

def MaskData.zeroNext {d n} (C : MaskData d n) (v : Node n) : Node n :=
  finCode n ((C.zeroNextCodes.lookup v.val).getD n)

def MaskData.leftVal {d n} (C : MaskData d n) : List Sym → Option (LState d)
  | [] => some C.start
  | a::r => (C.leftVal r).bind fun l => C.push l a

def MaskData.accept {d n} (C : MaskData d n) : List Sym → Node n → Prop
  | [], v => C.zero v = true
  | a::r, v => ∃ t, C.target v a t = true ∧ C.accept r t

def MaskData.zeroCheck {d n} (C : MaskData d n) (v : Node n) : Bool :=
  if C.zero v then C.zero (C.zeroNext v) && C.target v Sym.zero (C.zeroNext v) else true

def MaskData.coreCheck {d n} (C : MaskData d n) : Bool :=
  decide (C.push C.start Sym.zero = some C.start) && (List.finRange (n+1)).all C.zeroCheck

def MaskData.predCheckAt {d n} (C : MaskData d n) (l : LState d) : Bool :=
  (C.pushRow l).all fun a j => decide ((l,Sym.ofCode a) ∈ C.predecessors (finCode d j))

def MaskData.predCheck {d n} (C : MaskData d n) : Bool :=
  (List.finRange (d+1)).all C.predCheckAt

def MaskData.inclusion {d n} (C : MaskData d n) (v p : Node n) : Bool :=
  (!C.zero v || C.zero p) && (C.edges v).all (fun a x => subset x.mask (C.cell p a).mask)

def MaskData.leftCheck {d n} (C : MaskData d n) (x : Cell) (e : Exit) (pre : LState d × Sym) : Bool :=
  let (l,b) := pre
  let u := C.auxiliary l e.q b
  C.target (C.control l e.q false) b u && subset x.mask (C.cell u e.w.code).mask

def MaskData.rowCellCheck {d n} (C : MaskData d n) (M : Table) (l : LState d) (q : Q)
    (dir : Bool) (a : Nat) (x : Cell) : Bool :=
  if x.mask = 0 then true else
  match blockExit M q dir (Sym.ofCode a) with
  | none => false
  | some e =>
    if e.dir then
      match C.push l e.w with
      | none => false
      | some j => subset x.mask (listMask x.indices) &&
        x.indices.all (fun v => C.inclusion (finCode n v) (C.control j e.q true))
    else (C.predecessors l).all (C.leftCheck x e)

def MaskData.rowsAt {d n} (C : MaskData d n) (M : Table) (l : LState d) : Bool :=
  (List.finRange 6).all fun q => [false,true].all fun dir =>
    (C.edges (C.control l q dir)).all (C.rowCellCheck M l q dir)

def MaskData.rowsCheck {d n} (C : MaskData d n) (M : Table) : Bool :=
  (List.finRange (d+1)).all (C.rowsAt M)

def MaskData.CoreValid {d n} (C : MaskData d n) (M : Table) : Prop :=
  C.coreCheck = true ∧ C.predCheck = true ∧ C.rowsCheck M = true

theorem MaskData.pred_sound {d n} (C : MaskData d n) {l j : LState d} {a : Sym}
    (hc : C.predCheckAt l = true) (h : C.push l a = some j) : (l,a) ∈ C.predecessors j := by
  unfold MaskData.push at h
  cases hk : (C.pushRow l).lookup a.code with
  | none => simp [hk] at h
  | some i =>
    simp only [hk,Option.some.injEq] at h
    subst j
    have hh := Map.all_sound hc hk
    simpa only [code_roundtrip,decide_eq_true_eq] using hh

theorem MaskData.leftVal_pop {d n} (C : MaskData d n) (hzero : C.push C.start Sym.zero = some C.start)
    (r : List Sym) (l : LState d) (h : C.leftVal r = some l) :
    ∃ j, C.leftVal r.tail = some j ∧ C.push j (r.headD Sym.zero) = some l := by
  cases r with
  | nil =>
    simp [MaskData.leftVal] at h
    subst l
    exact ⟨C.start,rfl,hzero⟩
  | cons a r =>
    simp only [MaskData.leftVal] at h
    cases hj : C.leftVal r with
    | none => simp [hj] at h
    | some j => exact ⟨j,hj,by simpa [hj] using h⟩

theorem MaskData.accept_pop {d n} (C : MaskData d n) (hzero : ∀ v, C.zeroCheck v = true)
    (r : List Sym) (v : Node n) (h : C.accept r v) :
    ∃ t, C.target v (r.headD Sym.zero) t = true ∧ C.accept r.tail t := by
  cases r with
  | cons a r => exact h
  | nil =>
    have hz : C.zero v = true := h
    have H := hzero v
    simp [MaskData.zeroCheck,hz] at H
    exact ⟨C.zeroNext v,H.2,H.1⟩

theorem MaskData.target_cell {d n} (C : MaskData d n) {v t : Node n} {a : Sym}
    (h : C.target v a t = true) :
    ∃ x, (C.edges v).lookup a.code = some x ∧ x.mask.testBit t.val = true := by
  unfold MaskData.target MaskData.cell at h
  cases he : (C.edges v).lookup a.code with
  | none => simp [he] at h
  | some x => exact ⟨x,rfl,by simpa [he] using h⟩

theorem MaskData.inclusion_sound {d n} (C : MaskData d n) (v p : Node n)
    (h : C.inclusion v p = true) (r : List Sym) (hr : C.accept r v) : C.accept r p := by
  simp only [MaskData.inclusion,Bool.and_eq_true,Bool.or_eq_true] at h
  cases r with
  | nil =>
    rcases h.1 with hv|hp
    · have h' : C.zero v = true := hr
      simp [h'] at hv
    · exact hp
  | cons a r =>
    obtain ⟨t,ht,hrest⟩ := hr
    obtain ⟨x,hx,hbit⟩ := C.target_cell ht
    have hs : subset x.mask (C.cell p a.code).mask = true :=
      Map.all_sound (m := C.edges v) (f := fun a x => subset x.mask (C.cell p a).mask) h.2 hx
    exact ⟨t,subset_sound hs hbit,hrest⟩

def MaskData.Invariant {d n} (C : MaskData d n) (c : BlockConfig) : Prop :=
  ∃ l, C.leftVal c.l = some l ∧ C.accept c.r (C.control l c.q c.dir)

theorem MaskData.closed {d n} (C : MaskData d n) (M : Table) (h : C.CoreValid M)
    (c : BlockConfig) (hc : C.Invariant c) :
    ∃ e, blockExit M c.q c.dir (c.r.headD Sym.zero) = some e ∧ C.Invariant (c.next e.q e.dir e.w) := by
  obtain ⟨l,hl,hr⟩ := hc
  have hb := h.1
  simp only [MaskData.coreCheck,Bool.and_eq_true,decide_eq_true_eq] at hb
  have hz (v : Node n) : C.zeroCheck v = true := List.all_eq_true.mp hb.2 v (List.mem_finRange v)
  obtain ⟨v,hv,hrest⟩ := C.accept_pop hz c.r _ hr
  let a := c.r.headD Sym.zero
  let p := C.control l c.q c.dir
  have hrows := List.all_eq_true.mp h.2.2 l (List.mem_finRange l)
  have hq := List.all_eq_true.mp hrows c.q (List.mem_finRange c.q)
  have hdir := List.all_eq_true.mp hq c.dir (by cases c.dir <;> simp)
  obtain ⟨x,hx,hbit⟩ := C.target_cell hv
  have H := Map.all_sound hdir hx
  have hn : x.mask ≠ 0 := by
    intro he
    simp [he] at hbit
  simp only [MaskData.rowCellCheck,hn,ite_false,code_roundtrip] at H
  change (match blockExit M c.q c.dir a with | none => false | some e => _) = true at H
  cases he : blockExit M c.q c.dir a with
  | none => rw [he] at H; contradiction
  | some e =>
    refine ⟨e,rfl,?_⟩
    change (match blockExit M c.q c.dir a with | none => false | some e => _) = true at H
    rw [he] at H
    cases hed : e.dir with
    | true =>
      simp only [hed,ite_true] at H
      cases hj : C.push l e.w with
      | none => simp [hj] at H
      | some j =>
        rw [hj] at H
        simp only [Bool.and_eq_true] at H
        have hmem := listMask_mem (subset_sound H.1 hbit)
        have hi := List.all_eq_true.mp H.2 v.val hmem
        have hf : finCode n v.val = v := Fin.ext (Nat.mod_eq_of_lt v.isLt)
        rw [hf] at hi
        refine ⟨j,?_,?_⟩
        · simp [BlockConfig.next,MaskData.leftVal,hl,hj]
        · exact C.inclusion_sound v (C.control j e.q true) hi c.r.tail hrest
    | false =>
      simp only [hed,Bool.false_eq_true,ite_false] at H
      obtain ⟨j,hj,hpush⟩ := C.leftVal_pop hb.1 c.l l hl
      have hpc := List.all_eq_true.mp h.2.1 j (List.mem_finRange j)
      have hmem := C.pred_sound hpc hpush
      have hh := List.all_eq_true.mp H (j,c.l.headD Sym.zero) hmem
      simp only [MaskData.leftCheck,Bool.and_eq_true] at hh
      refine ⟨j,?_,?_⟩
      · simpa [BlockConfig.next,hed] using hj
      · change C.accept (c.l.headD Sym.zero::e.w::c.r.tail) (C.control j e.q false)
        exact ⟨_,hh.1,v,subset_sound hh.2 hbit,hrest⟩

def MaskData.acceptCheck {d n} (C : MaskData d n) : List Sym → Node n → Bool
  | [],v => C.zero v
  | a::r,v => ((C.cell v a.code).indices).any fun i =>
    C.target v a (finCode n i) && C.acceptCheck r (finCode n i)

theorem MaskData.acceptCheck_sound {d n} (C : MaskData d n) (r : List Sym) (v : Node n)
    (h : C.acceptCheck r v = true) : C.accept r v := by
  induction r generalizing v with
  | nil => exact h
  | cons a r ih =>
    obtain ⟨i,_,hh⟩ := List.any_eq_true.mp h
    simp only [Bool.and_eq_true] at hh
    exact ⟨finCode n i,hh.1,ih _ hh.2⟩

def MaskData.entryCheck {d n} (C : MaskData d n) (c : BlockConfig) : Bool :=
  match C.leftVal c.l with
  | none => false
  | some l => C.acceptCheck c.r (C.control l c.q c.dir)

theorem MaskData.entryCheck_sound {d n} (C : MaskData d n) (c : BlockConfig)
    (h : C.entryCheck c = true) : C.Invariant c := by
  unfold MaskData.entryCheck at h
  cases hl : C.leftVal c.l with
  | none => simp [hl] at h
  | some l => exact ⟨l,hl,C.acceptCheck_sound _ _ (by simpa [hl] using h)⟩

theorem MaskData.soundFrom {d n} (C : MaskData d n) (M : Table)
    (h : C.CoreValid M) (entry : BlockConfig) (he : C.entryCheck entry = true)
    (t : Nat) (ht : run M t primBlank = some entry.render) :
    ∀ k, ∃ c, run M k primBlank = some c := by
  intro k
  by_cases hk : t ≤ k
  · obtain ⟨c,hc⟩ := forever_of_invariant M C.Invariant (C.closed M h)
      entry (C.entryCheck_sound entry he) (k-t)
    refine ⟨c,?_⟩
    rw [show k=t+(k-t) by omega,run_add,ht]
    exact hc
  · have hh := ht
    rw [show t=k+(t-k) by omega,run_add] at hh
    cases hr : run M k primBlank with
    | none => simp [hr] at hh
    | some c => exact ⟨c,rfl⟩

theorem MaskData.sound {d n} (C : MaskData d n) (M : Table)
    (h : C.CoreValid M) (he : C.entryCheck blockBlank = true) :
    ∀ k, ∃ c, run M k primBlank = some c :=
  C.soundFrom M h blockBlank he 0 (by rw [render_blank]; rfl)

#print axioms MaskData.closed
#print axioms MaskData.soundFrom
#print axioms MaskData.sound
end BB6BlockFAR4
