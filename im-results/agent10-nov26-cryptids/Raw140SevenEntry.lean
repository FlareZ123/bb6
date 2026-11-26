import Raw140SevenOrbit
namespace Raw140Orbit
open BB6BlockFAR
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def start : BState := ⟨2,true,[S 6],[]⟩
def goal : BState := ⟨1,true,[S 5],U 2 40 ++ [S 1,S 5]⟩
def counts : Fin 7 → Nat := fun v => ([2514,2512,2516,2516,2510,2514,2512] : List Nat)[v.val]!
def cost : Fin 7 → Nat := fun v => ([7294,7286,7304,7296,7284,7300,7292] : List Nat)[v.val]!
theorem start_ok (v : Fin 7) : run (variant v) 2 primBlank = some start.prim := by
  simp [run, primStep, variant, base, primBlank, start, BState.prim, boundary, render, S, Sym.ofCode, leftRay, rightRay, blankRay, cons, tail]
  simp [Sym.zero,blank_cons]
  rfl

theorem entry_macro (v : Fin 7) : execute (variant v) (counts v) start = some (cost v - 2,goal) := by
  have hv : v = 0 ∨ v = 1 ∨ v = 2 ∨ v = 3 ∨ v = 4 ∨ v = 5 ∨ v = 6 := by omega
  rcases hv with h|h|h|h|h|h|h <;> subst v <;> decide +kernel

theorem entry (v : Fin 7) : run (variant v) (cost v) primBlank = some (familyA 40) := by
  have h := join (start_ok v) (execute_sound (variant v) (counts v) (cost v - 2) start goal (entry_macro v))
  have hcost : 2 ≤ cost v := by
    have hv : v = 0 ∨ v = 1 ∨ v = 2 ∨ v = 3 ∨ v = 4 ∨ v = 5 ∨ v = 6 := by omega
    rcases hv with h|h|h|h|h|h|h <;> subst v <;> decide
  rw [show 2+(cost v-2)=cost v by omega] at h
  exact h

theorem infinite_family (v : Fin 7) (n k : Nat) : ∃ c, run (variant v) k (familyA n) = some c := by
  induction k using Nat.strongRecOn generalizing n with
  | ind k ih =>
    have h := growth v n
    by_cases hle : 36*n+198 ≤ k
    · obtain ⟨c,hc⟩ := ih (k-(36*n+198)) (by omega) (n+6)
      exact ⟨c, by rw [show k=(36*n+198)+(k-(36*n+198)) by omega,run_add,h]; exact hc⟩
    · rw [show 36*n+198=k+(36*n+198-k) by omega,run_add] at h
      cases he : run (variant v) k (familyA n) with
      | none => simp [he] at h
      | some c => exact ⟨c,rfl⟩

theorem forever (v : Fin 7) (k : Nat) : ∃ c, run (variant v) k primBlank = some c := by
  have h := entry v
  by_cases hle : cost v ≤ k
  · obtain ⟨c,hc⟩ := infinite_family v 40 (k-cost v)
    exact ⟨c,by rw [show k=cost v+(k-cost v) by omega,run_add,h]; exact hc⟩
  · rw [show cost v=k+(cost v-k) by omega,run_add] at h
    cases he : run (variant v) k primBlank with
    | none => simp [he] at h
    | some c => exact ⟨c,rfl⟩

#print axioms phaseA
#print axioms phaseB
#print axioms growth
#print axioms entry_macro
#print axioms forever
end Raw140Orbit
