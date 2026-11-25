import BlockFAR
import Frontier

namespace BB6BlockFAR

def sourceMove (mv : Move) : BB6Coverage.Move := ⟨mv.write,mv.right,mv.next⟩

def partialTable (M : Table) : BB6Coverage.PartialMachine :=
  fun s => (M s.1 s.2).map (fun mv => some (sourceMove mv))

/-- A head-relative ray configuration denotes the same tape at any
    absolute head coordinate. -/
def Related (c : BB6Coverage.Config) (x : Prim) : Prop :=
  c.state = x.q ∧
  (∀ i : Nat, c.tape (c.head - (i : Int) - 1) = x.l i) ∧
  (∀ i : Nat, c.tape (c.head + (i : Int)) = x.r i)

theorem related_blank : Related BB6Coverage.blank primBlank := by
  exact ⟨rfl,fun _ => rfl,fun _ => rfl⟩

theorem related_step (M : Table) (m : BB6Coverage.Machine)
    (hm : BB6Coverage.compatible (partialTable M) m)
    (c : BB6Coverage.Config) (x y : Prim) (hrel : Related c x)
    (hstep : primStep M x = some y) :
    ∃ d, BB6Coverage.rawStep m c = some d ∧ Related d y := by
  obtain ⟨hq,hl,hr⟩ := hrel
  cases hmv : M x.q (x.r 0) with
  | none => simp [primStep,hmv] at hstep
  | some mv =>
    have hread : c.tape c.head = x.r 0 := by simpa using hr 0
    have hknown : partialTable M (BB6Coverage.readSlot c) = some (some (sourceMove mv)) := by
      change (M c.state (c.tape c.head)).map _ = _
      rw [hq,hread,hmv]
      rfl
    have hs : BB6Coverage.rawStep m c = some (BB6Coverage.applyMove c (sourceMove mv)) := by
      unfold BB6Coverage.rawStep
      rw [hm _ _ hknown]
      rfl
    refine ⟨_,hs,?_⟩
    cases hd : mv.right with
    | true =>
      simp [primStep,hmv,hd] at hstep
      subst y
      refine ⟨rfl,?_,?_⟩
      · intro i
        simp only [BB6Coverage.applyMove,sourceMove,hd,ite_true]
        cases i with
        | zero => simp [cons]
        | succ i =>
          have he : c.head + 1 - (↑(i+1) : Int) - 1 = c.head - (i : Int) - 1 := by omega
          rw [he,if_neg (by omega)]
          exact hl i
      · intro i
        simp only [BB6Coverage.applyMove,sourceMove,hd,ite_true,tail]
        have he : c.head + 1 + (i : Int) = c.head + (↑(i+1) : Int) := by omega
        rw [he,if_neg (by omega)]
        exact hr (i+1)
    | false =>
      simp [primStep,hmv,hd] at hstep
      subst y
      refine ⟨rfl,?_,?_⟩
      · intro i
        simp only [BB6Coverage.applyMove,sourceMove,hd,Bool.false_eq_true,ite_false,tail]
        have he : c.head + (-1) - (i : Int) - 1 = c.head - (↑(i+1) : Int) - 1 := by omega
        rw [he,if_neg (by omega)]
        exact hl (i+1)
      · intro i
        simp only [BB6Coverage.applyMove,sourceMove,hd,Bool.false_eq_true,ite_false]
        cases i with
        | zero =>
          have he : c.head + (-1) + (↑(0:Nat) : Int) = c.head - (↑(0:Nat) : Int) - 1 := by omega
          rw [he,if_neg (by omega)]
          exact hl 0
        | succ i =>
          cases i with
          | zero =>
            have he : c.head + (-1) + (↑(0+1:Nat) : Int) = c.head := by omega
            rw [he,if_pos rfl]
            rfl
          | succ i =>
            have he : c.head + (-1) + (↑(i+1+1:Nat) : Int) = c.head + (↑(i+1) : Int) := by omega
            rw [he,if_neg (by omega)]
            exact hr (i+1)

theorem run_succ_last (M : Table) (n : Nat) (c : Prim) :
    run M (n+1) c = (run M n c).bind (primStep M) := by
  rw [run_add]
  cases run M n c <;> simp [run]

/-- Any forever-defined partial primitive execution is forever-defined for
    every completion in the original coverage semantics. -/
theorem transfer_never (M : Table) (m : BB6Coverage.Machine)
    (hm : BB6Coverage.compatible (partialTable M) m)
    (forever : ∀ k, ∃ c, run M k primBlank = some c) : BB6Coverage.NeverHalts m := by
  have h : ∀ n, ∃ c x, BB6Coverage.run m n BB6Coverage.blank = some c ∧
      run M n primBlank = some x ∧ Related c x := by
    intro n
    induction n with
    | zero => exact ⟨_,_,rfl,rfl,related_blank⟩
    | succ n ih =>
      obtain ⟨c,x,hc,hx,hr⟩ := ih
      obtain ⟨y,hy⟩ := forever (n+1)
      rw [run_succ_last,hx] at hy
      change primStep M x = some y at hy
      obtain ⟨d,hd,hrel⟩ := related_step M m hm c x y hr hy
      refine ⟨d,y,?_,?_,hrel⟩
      · simp [BB6Coverage.run,hc,hd]
      · rw [run_succ_last,hx]
        exact hy
  intro n
  obtain ⟨c,x,hc,_,_⟩ := h n
  simp [hc]

theorem Data.source_never {d n} (C : Data d n) (M : Table) (h : C.Valid M)
    (m : BB6Coverage.Machine) (hm : BB6Coverage.compatible (partialTable M) m) :
    BB6Coverage.NeverHalts m := transfer_never M m hm (C.sound M h)

#print axioms related_step
#print axioms transfer_never
#print axioms Data.source_never
end BB6BlockFAR
