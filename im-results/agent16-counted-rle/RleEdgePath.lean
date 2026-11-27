import RleCountedDispatch

open Mathlib Relation Nat Turing BusyBeaver BusyBeaver.RleStackEngine
namespace BB6.Agent17.RleCounted

/-- A certificate contains only compressed state transitions and exact costs.
    No decoded tape or long evaluator reduction occurs in the certificate. -/
inductive CountPath : RleFullState → RleFullState → Nat → Prop where
  | one {s t : RleFullState} {k : Nat} :
      s.halted = false → rleStep s = t → costRleStep s = k →
      CountPath s t k
  | trans {s t u : RleFullState} {k l : Nat} :
      CountPath s t k → CountPath t u l → CountPath s u (k+l)

theorem CountPath.back {M : Machine (Fin 2) (Fin 6)} [CountedRules M]
    {s t : RleFullState} {k : Nat} (p : CountPath s t k) :
    ∀ n, StateHaltsAt M t n → StateHaltsAt M s (k+n) := by
  induction p with
  | one hl hs hc =>
    intro n h
    rw [← hs] at h
    have hh := c_rleStep_halts _ n h
    rw [hc] at hh
    simpa only [StateHaltsAt, hl, Bool.false_eq_true, if_false] using hh
  | trans _ _ ih1 ih2 =>
    intro n h
    simpa only [Nat.add_assoc] using ih1 _ (ih2 _ h)

theorem CountPath.halt {M : Machine (Fin 2) (Fin 6)} [CountedRules M]
    {s t : RleFullState} {k : Nat} (p : CountPath s t k)
    (ht : t.halted = true) : StateHaltsAt M s k := by
  have h : StateHaltsAt M t 0 := by simp [StateHaltsAt, ht]
  simpa only [Nat.add_zero] using p.back 0 h

#print axioms CountPath.back
#print axioms CountPath.halt
end BB6.Agent17.RleCounted
