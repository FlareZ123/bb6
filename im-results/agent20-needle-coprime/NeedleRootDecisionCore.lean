import Lean.Elab.Tactic.Omega

/-!
A reusable, executable inverse reachability checker for a strictly increasing
partial map of natural counters with a complete finite list of predecessors.
The theorem is entirely generic and uses no Space Needle assumptions.
-/

namespace NeedleRootDecisionCore

variable (next : Nat → Option Nat)

/-- A structurally recursive forward trace, starting at natural counter one. -/
def run : Nat → Option Nat
  | 0 => some 1
  | n+1 => (run n).bind next

def Reached (d : Nat) : Prop := ∃ n, run next n = some d

theorem run_succ (n : Nat) :
    run next (n+1) = (run next n).bind next := rfl

theorem reached_initial : Reached next 1 := ⟨0, rfl⟩

theorem reached_step (p d : Nat)
    (hp : Reached next p) (hstep : next p=some d) :
    Reached next d := by
  obtain ⟨n,hn⟩ := hp
  refine ⟨n+1, ?_⟩
  rw [run_succ,hn]
  exact hstep

theorem reached_noninitial_parent (d : Nat)
    (hd : Reached next d) (hne : d ≠ 1) :
    ∃ p, Reached next p ∧ next p=some d := by
  obtain ⟨n,hn⟩ := hd
  cases n with
  | zero =>
    have : d=1 := by simpa [run] using hn.symm
    exact False.elim (hne this)
  | succ n =>
    rw [run_succ] at hn
    cases hp : run next n with
    | none => simp [hp] at hn
    | some p =>
      have hstep : next p=some d := by simpa [hp] using hn
      exact ⟨p,⟨n,hp⟩,hstep⟩

variable (parents : Nat → List Nat)

/-- The search fuel is the maximum possible reverse-chain length. -/
def reverseCheck : Nat → Nat → Bool
  | 0, _ => false
  | fuel+1, d =>
      if d=1 then true else
        (parents d).any (reverseCheck fuel)

/-- Completeness, soundness, and termination are proved at each bounded
target. The backward process only uses exact predecessors, and every
genuine predecessor has smaller counter. -/
theorem reverseCheck_spec
    (hparents : ∀ p d, p ∈ parents d ↔ next p=some d)
    (hincreasing : ∀ p d, next p=some d → p<d)
    (fuel d : Nat) (hdf : d<fuel) :
    reverseCheck parents fuel d = true ↔ Reached next d := by
  induction fuel generalizing d with
  | zero => omega
  | succ fuel ih =>
    by_cases hinit : d=1
    · subst d
      have hseed : Reached next 1 := reached_initial next
      simpa [reverseCheck] using hseed
    · have hbound : d ≤ fuel := by omega
      simp only [reverseCheck, if_neg hinit, List.any_eq_true]
      constructor
      · rintro ⟨p,hp,hchecked⟩
        have hstep : next p = some d := (hparents p d).mp hp
        have hpfuel : p<fuel := by
          have := hincreasing p d hstep
          omega
        exact reached_step next p d ((ih p hpfuel).mp hchecked) hstep
      · intro hreach
        obtain ⟨p,hp,hstep⟩ :=
          reached_noninitial_parent next d hreach hinit
        have hpfuel : p<fuel := by
          have := hincreasing p d hstep
          omega
        exact ⟨p,(hparents p d).mpr hstep,(ih p hpfuel).mpr hp⟩

/-- A uniform, exact Boolean decision of reachability for each given
target, using fuel d+1. There is no uniform classification over all
targets in this theorem. -/
theorem exact_fixed_target
    (hparents : ∀ p d, p ∈ parents d ↔ next p=some d)
    (hincreasing : ∀ p d, next p=some d → p<d)
    (d : Nat) :
    reverseCheck parents (d+1) d = true ↔ Reached next d := by
  exact reverseCheck_spec next parents hparents hincreasing
    (d+1) d (by omega)

#print axioms exact_fixed_target
end NeedleRootDecisionCore
