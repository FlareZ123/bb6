import Raw140SevenOrbit
namespace Raw140Extra
open BB6BlockFAR Raw140Orbit
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def Extends (M : Table) : Prop := ∀ q b m, base q b = some m → M q b = some m

def fill (a f0 : Option Move) : Table := fun q b =>
  match base q b with
  | some m => some m
  | none => if q == 0 && b then a else if q == 5 && !b then f0 else none

theorem fill_extends (a f0 : Option Move) : Extends (fill a f0) := by
  intro q b m h
  simp [fill,h]

theorem step_ext (M : Table) (ext : Extends M) (c c' : Prim)
    (h : primStep base c = some c') : primStep M c = some c' := by
  cases hm : base c.q (c.r 0) with
  | none => simp [primStep,hm] at h
  | some m => simpa [primStep,hm,ext _ _ _ hm] using h

theorem run_ext (M : Table) (ext : Extends M) (n : Nat) (c c' : Prim)
    (h : run base n c = some c') : run M n c = some c' := by
  induction n generalizing c with
  | zero => exact h
  | succ n ih =>
    rw [run] at h ⊢
    cases hm : primStep base c with
    | none => simp [hm] at h
    | some d => simp only [hm,Option.bind_some] at h; rw [step_ext M ext c d hm]; exact ih d h

theorem growth (M : Table) (ext : Extends M) (n : Nat) :
    run M (36*n+198) (familyA n) = some (familyA (n+6)) := by
  have h := join (phaseA n) (phaseB (n+3))
  rw [show (18*n+62)+(18*(n+3)+82)=36*n+198 by omega, show n+3+3=n+6 by omega] at h
  exact run_ext M ext _ _ _ h

def start : BState := ⟨2,true,[S 6],[]⟩

theorem base_start : run base 2 primBlank = some start.prim := by
  simp [run, primStep, base, primBlank, start, BState.prim, boundary, render, S, Sym.ofCode, leftRay, rightRay, blankRay, cons, tail] <;> simp [Sym.zero,blank_cons] <;> rfl

theorem infinite_family (M : Table) (ext : Extends M) (n k : Nat) : ∃ c, run M k (familyA n) = some c := by
  induction k using Nat.strongRecOn generalizing n with
  | ind k ih =>
    have h := growth M ext n
    by_cases hle : 36*n+198 ≤ k
    · obtain ⟨c,hc⟩ := ih (k-(36*n+198)) (by omega) (n+6)
      exact ⟨c, by rw [show k=(36*n+198)+(k-(36*n+198)) by omega,run_add,h]; exact hc⟩
    · rw [show 36*n+198=k+(36*n+198-k) by omega,run_add] at h
      cases he : run M k (familyA n) with
      | none => simp [he] at h
      | some c => exact ⟨c,rfl⟩

theorem foreverA (M : Table) (ext : Extends M) (t n : Nat)
    (entry : run M t primBlank = some (familyA n)) (k : Nat) : ∃ c, run M k primBlank = some c := by
  by_cases hle : t ≤ k
  · obtain ⟨c,hc⟩ := infinite_family M ext n (k-t)
    exact ⟨c,by rw [show k=t+(k-t) by omega,run_add,entry]; exact hc⟩
  · rw [show t=k+(t-k) by omega,run_add] at entry
    cases he : run M k primBlank with
    | none => simp [he] at entry
    | some c => exact ⟨c,rfl⟩

theorem foreverB (M : Table) (ext : Extends M) (t n : Nat)
    (entry : run M t primBlank = some (familyB n)) (k : Nat) : ∃ c, run M k primBlank = some c :=
  foreverA M ext (t+(18*n+82)) (n+3) (join entry (run_ext M ext _ _ _ (phaseB n))) k

#print axioms foreverA
#print axioms foreverB
end Raw140Extra
