import BlockFAR4

set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace BB6BlockFAR4

/-- Closure checks independent of the position of the initially blank head. -/
def Data.coreCheck {d n} (C : Data d n) : Bool :=
  decide (C.push C.start Sym.zero = some C.start) &&
    (List.finRange (n+1)).all C.zeroCheck

def Data.CoreValid {d n} (C : Data d n) (M : Table) : Prop :=
  C.coreCheck = true ∧ C.predCheck = true ∧ C.rowsCheck M = true

theorem Data.closedFrom {d n} (C : Data d n) (M : Table) (h : C.CoreValid M)
    (c : BlockConfig) (hc : C.Invariant c) :
    ∃ e, blockExit M c.q c.dir (c.r.headD Sym.zero) = some e ∧ C.Invariant (c.next e.q e.dir e.w) := by
  obtain ⟨l,hl,hr⟩ := hc
  have hb := h.1
  simp only [Data.coreCheck,Bool.and_eq_true,decide_eq_true_eq] at hb
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
      obtain ⟨j,hj,hpush⟩ := C.leftVal_pop hb.1 c.l l hl
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

def Data.acceptCheck {d n} (C : Data d n) : List Sym → Node n → Bool
  | [], v => C.zero v
  | a::r, v => (C.targets v a).any (C.acceptCheck r)

theorem Data.acceptCheck_sound {d n} (C : Data d n) (r : List Sym) (v : Node n)
    (h : C.acceptCheck r v = true) : C.accept r v := by
  induction r generalizing v with
  | nil => exact h
  | cons a r ih =>
    obtain ⟨t,ht,hrest⟩ := List.any_eq_true.mp h
    exact ⟨t,ht,ih t hrest⟩

def Data.entryCheck {d n} (C : Data d n) (c : BlockConfig) : Bool :=
  match C.leftVal c.l with
  | none => false
  | some l => C.acceptCheck c.r (C.control l c.q c.dir)

theorem Data.entryCheck_sound {d n} (C : Data d n) (c : BlockConfig)
    (h : C.entryCheck c = true) : C.Invariant c := by
  unfold Data.entryCheck at h
  cases hl : C.leftVal c.l with
  | none => simp [hl] at h
  | some l => exact ⟨l,hl,C.acceptCheck_sound _ _ (by simpa [hl] using h)⟩

/-- Every prefix is live once a checked finite initial trace enters the
    invariant, even when the original head is not at a block boundary. -/
theorem Data.soundFrom {d n} (C : Data d n) (M : Table)
    (h : C.CoreValid M) (entry : BlockConfig) (he : C.entryCheck entry = true)
    (t : Nat) (ht : run M t primBlank = some entry.render) :
    ∀ k, ∃ c, run M k primBlank = some c := by
  intro k
  by_cases hk : t ≤ k
  · obtain ⟨c,hc⟩ := forever_of_invariant M C.Invariant (C.closedFrom M h)
      entry (C.entryCheck_sound entry he) (k-t)
    refine ⟨c,?_⟩
    rw [show k=t+(k-t) by omega,run_add,ht]
    exact hc
  · have hh := ht
    rw [show t=k+(t-k) by omega,run_add] at hh
    cases hr : run M k primBlank with
    | none => simp [hr] at hh
    | some c => exact ⟨c,rfl⟩

theorem offset_blank (p : Pos) : render 0 p Sym.zero [] [] = primBlank := by
  cases p <;> simp [render,primBlank,Sym.zero,leftRay,rightRay,blank_cons]

#print axioms Data.closedFrom
#print axioms Data.soundFrom
end BB6BlockFAR4
