import OrbitPerms
import F287RenamedRoots
import AllHaltsFreedom

set_option maxRecDepth 16384
set_option maxHeartbeats 20000000

namespace BB6Coverage

/-- A bijection of state labels fixing A preserves blank-start nonhalting. -/
theorem rename_never (e : StatePerm) (hz : e.forward 0 = 0)
    (m : Machine) (h : NeverHalts m) : NeverHalts (renameTable e m) := by
  intro n
  have hr := rename_run e m blank n
  have hb : renameConfig e blank = blank := by
    simp [renameConfig, blank, hz]
  rw [hb] at hr
  rw [hr]
  cases hc : run m n blank with
  | none =>
      have hsome := h n
      simp [hc] at hsome
  | some c => rfl

/-- Reflecting the whole infinite tape preserves nonhalting. -/
theorem mirror_never (m : Machine) (h : NeverHalts m) :
    NeverHalts (reflectTable m) := by
  intro n
  have hr := mirror_run m blank n
  rw [mirror_blank] at hr
  rw [hr]
  cases hc : run m n blank with
  | none =>
      have hsome := h n
      simp [hc] at hsome
  | some c => rfl

open BB6.F287

/-- Three originally source-authenticated distinct blank roots, normalized
so that each starts in the standard state A. -/
def threeRoot (r : Fin 3) : Machine :=
  if r=0 then expectedRLE else if r=1 then dLiteral else eLiteral

theorem threeRoot_never (r : Fin 3) : NeverHalts (threeRoot r) := by
  have hr : r.val = 0 ∨ r.val = 1 ∨ r.val = 2 := by omega
  rcases hr with h | h | h
  · have heq : r = 0 := Fin.ext h
    subst r
    simpa [threeRoot] using literal_never
  · have heq : r = 1 := Fin.ext h
    subst r
    simpa [threeRoot] using d_literal_never
  · have heq : r = 2 := Fin.ext h
    subst r
    simpa [threeRoot] using e_literal_never

/-- All 3 source-verified blank roots, 120 label permutations, two mirrors. -/
def orbitMachine (r : Fin 3) (i : Fin 120) (mirror : Bool) : Machine :=
  normalizedTable (rootedPerm i) mirror (threeRoot r)

theorem orbitNever (r : Fin 3) (i : Fin 120) (b : Bool) :
    NeverHalts (orbitMachine r i b) := by
  have h := threeRoot_never r
  have hnorm : ∀ m : Machine, NeverHalts m →
      NeverHalts (renameTable (rootedPerm i) m) := by
    intro m hm
    exact rename_never (rootedPerm i) (fwd_zero i) m hm
  cases b with
  | false => exact hnorm _ h
  | true => exact hnorm _ (mirror_never _ h)

def orbitCylinder (r : Fin 3) (i : Fin 120) (b : Bool) : PartialMachine :=
  freeAllHalts (orbitMachine r i b)

theorem orbitCover (r : Fin 3) (i : Fin 120) (b : Bool) (bound : Nat) :
    Cover (DecidedBelow bound) (orbitCylinder r i b) :=
  freeAllHalts_cover bound (orbitMachine r i b) (orbitNever r i b)

#print axioms orbitCover
end BB6Coverage
