import Raw13Coupled6OneRABatch
namespace BB6Coverage.Agent31Pump.Raw13Coupled6OneRAReplay
open BB6Coverage Agent31Pump Raw13Coupled6OneRAHierarchy Raw13Coupled6OneRACost Raw13Coupled6OneRABatch
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def TapeEq (a b : List Bool) : Prop := ∀ i, a.getD i false = b.getD i false

theorem tape_refl (a : List Bool) : TapeEq a a := fun _ => rfl
theorem tape_symm {a b} (h : TapeEq a b) : TapeEq b a := fun i => (h i).symm
theorem tape_trans {a b c} (h : TapeEq a b) (g : TapeEq b c) : TapeEq a c := fun i => (h i).trans (g i)
theorem tape_cons (x : Bool) {a b} (h : TapeEq a b) : TapeEq (x::a) (x::b) := by
  intro i; cases i with
  | zero => rfl
  | succ i => simpa using h i

theorem tape_head {a b} (h : TapeEq a b) : a.headD false = b.headD false := by
  rw [Agent50Zipper.headD_getD,Agent50Zipper.headD_getD]; exact h 0

theorem tape_tail {a b} (h : TapeEq a b) : TapeEq a.tail b.tail := by
  intro i; rw [Agent50Zipper.getD_tail,Agent50Zipper.getD_tail]; exact h (i+1)

theorem tape_append (pre : List Bool) {a b} (h : TapeEq a b) : TapeEq (pre++a) (pre++b) := by
  induction pre with
  | nil => exact h
  | cons x xs ih => exact tape_cons x ih

theorem tape_zero_nil : TapeEq [false] [] := by intro i; cases i <;> rfl

def ZEq (a b : Z0) : Prop := a.q=b.q ∧ TapeEq a.l b.l ∧ TapeEq a.r b.r

theorem zrefl (a : Z0) : ZEq a a := ⟨rfl,tape_refl _,tape_refl _⟩
theorem zsymm {a b} (h : ZEq a b) : ZEq b a := ⟨h.1.symm,tape_symm h.2.1,tape_symm h.2.2⟩
theorem ztrans {a b c} (h : ZEq a b) (g : ZEq b c) : ZEq a c :=
  ⟨h.1.trans g.1,tape_trans h.2.1 g.2.1,tape_trans h.2.2 g.2.2⟩

theorem move_eq (mv : Move) {a b} (h : ZEq a b) : ZEq (move0 mv a) (move0 mv b) := by
  cases hr : mv.right with
  | false =>
    simp only [move0,hr,Bool.false_eq_true,ite_false]
    change ZEq ⟨mv.next,a.l.tail,mv.write::a.r⟩ ⟨mv.next,b.l.tail,mv.write::b.r⟩
    exact ⟨rfl,tape_tail h.2.1,tape_cons _ h.2.2⟩
  | true =>
    simp only [move0,hr,ite_true]
    change ZEq ⟨mv.next,a.r.headD false::mv.write::a.l.tail,a.r.tail⟩
      ⟨mv.next,b.r.headD false::mv.write::b.l.tail,b.r.tail⟩
    rw [tape_head h.2.2]
    exact ⟨rfl,tape_cons _ (tape_cons _ (tape_tail h.2.1)),tape_tail h.2.2⟩

theorem step_eq {a b c} (h : ZEq a b) (hr : step0 p a = some c) :
    ∃ d, step0 p b = some d ∧ ZEq c d := by
  unfold step0 at hr ⊢
  have ht : (a.q,a.l.headD false)=(b.q,b.l.headD false) := by rw [h.1,tape_head h.2.1]
  rw [←ht]
  cases he : (p (a.q,a.l.headD false)).bind id with
  | none => rw [he] at hr; contradiction
  | some mv =>
    rw [he] at hr
    simp only [Option.map_some,Option.some.injEq] at hr
    subst c
    exact ⟨_,rfl,move_eq mv h⟩

theorem run_eq (n : Nat) {a b c} (h : ZEq a b) (hr : run0 p n a = some c) :
    ∃ d, run0 p n b = some d ∧ ZEq c d := by
  induction n generalizing a b with
  | zero =>
    have hc : a=c := Option.some.inj hr
    subst c
    exact ⟨b,rfl,h⟩
  | succ n ih =>
    cases hs : step0 p a with
    | none => simp [run0,hs] at hr
    | some e =>
      have ht : run0 p n e = some c := by simpa [run0,hs] using hr
      obtain ⟨f,hf,he⟩ := step_eq h hs
      obtain ⟨d,hd,hcd⟩ := ih he ht
      exact ⟨d,by simpa [run0,hf] using hd,hcd⟩

def trim : List Bool → List Bool
  | [] => []
  | b::bs => let t := trim bs; if b || !t.isEmpty then b::t else []

theorem trim_eq (a : List Bool) : TapeEq (trim a) a := by
  induction a with
  | nil => exact tape_refl _
  | cons b bs ih =>
    cases b with
    | true => exact tape_cons true ih
    | false =>
      cases h : trim bs with
      | nil =>
        simp only [trim,h,Bool.false_or,List.isEmpty_nil,Bool.not_true,ite_false]
        exact tape_trans (tape_symm tape_zero_nil) (tape_cons false (by simpa [h] using ih))
      | cons x xs =>
        simp only [trim,h,Bool.false_or,List.isEmpty_cons,Bool.not_false,ite_true]
        exact tape_cons false (by simpa [h] using ih)

def norm (z : Z0) : Z0 := ⟨z.q,trim z.l,trim z.r⟩
theorem norm_eq (z : Z0) : ZEq (norm z) z := ⟨rfl,trim_eq _,trim_eq _⟩

/-- Macro soundness allows only observational padding changes, never
    changes to an actual tape cell. -/
def MacroOK (z : Z0) (n : Nat) (out : Z0) : Prop := ∃ w, run0 p n z = some w ∧ ZEq w out

theorem macro_join {z a b : Z0} {n m : Nat} (h : MacroOK z n a) (g : MacroOK a m b) : MacroOK z (n+m) b := by
  obtain ⟨u,hu,he⟩ := h
  obtain ⟨v,hv,hf⟩ := g
  obtain ⟨w,hw,hg⟩ := run_eq m (zsymm he) hv
  exact ⟨w,join0 hu hw,ztrans (zsymm hg) hf⟩

theorem macro_of_run {z w : Z0} {n : Nat} (h : run0 p n z = some w) : MacroOK z n (norm w) :=
  ⟨w,h,zsymm (norm_eq w)⟩

theorem macro_transport {z z' w : Z0} {n : Nat} (he : ZEq z z') (h : MacroOK z' n w) : MacroOK z n w := by
  obtain ⟨v,hv,hvw⟩ := h
  obtain ⟨u,hu,hvu⟩ := run_eq n (zsymm he) hv
  exact ⟨u,hu,ztrans (zsymm hvu) hvw⟩

#print axioms macro_join
end BB6Coverage.Agent31Pump.Raw13Coupled6OneRAReplay
