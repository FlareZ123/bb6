import Machine623Path
import TotalHaltAudit
import Lean.Elab.Tactic.Omega

namespace BB6Coverage

/-- The unique genuine missing raw transition in the original #623 table. -/
def machine623HaltSlot : Slot := (⟨5, by decide⟩, false)

theorem machine623_halts_only_at_F0 (s : Slot) :
    machine623 s = none ↔ s = machine623HaltSlot := by
  rcases s with ⟨q,b⟩
  have hq : q = 0 ∨ q = 1 ∨ q = 2 ∨ q = 3 ∨ q = 4 ∨ q = 5 := by
    have hlt := q.isLt
    omega
  rcases hq with hq|hq|hq|hq|hq|hq <;> subst q <;> cases b <;> decide

/-- The eleven actually visited inputs fix every original table entry
    except F/0; this is an exact identity of sparse tables. -/
theorem machine623_visited_eq_free_halt :
    machine623Prefix 11 =
       freeHaltCylinder machine623 machine623HaltSlot := by
  funext s
  rcases s with ⟨q,b⟩
  have hq : q = 0 ∨ q = 1 ∨ q = 2 ∨ q = 3 ∨ q = 4 ∨ q = 5 := by
    have hlt := q.isLt
    omega
  rcases hq with hq|hq|hq|hq|hq|hq <;> subst q <;> cases b <;> decide

/-- The 24 nonhalting choices for F/0 are syntactically total machines
    and hence have never-halting blank-tape runs. The sole remaining
    possibility is precisely the original #623 source machine. -/
theorem machine623_only_one_nontrivial_completion
    (m : Machine) (hcomp : compatible (machine623Prefix 11) m) :
    m = machine623 ∨ NeverHalts m := by
  have hc : compatible (freeHaltCylinder machine623 machine623HaltSlot) m := by
    simpa [machine623_visited_eq_free_halt] using hcomp
  by_cases hh : m machine623HaltSlot = none
  · exact Or.inl (one_halt_freedom_nontrivial_singleton machine623 m
      machine623HaltSlot ((machine623_halts_only_at_F0 _).2 rfl) hc hh)
  · right
    exact one_halt_freedom_trivial_part machine623 m machine623HaltSlot
      (by
        intro s hs
        have h := (machine623_halts_only_at_F0 s).mp
        intro hh2
        exact hs (h hh2))
      hc hh

/-- The only remaining local obligation to close this entire 25-machine
    cylinder is the original rooted #623 never-halting theorem. -/
theorem machine623_full_cylinder_if_never (B : Nat)
    (hroot : NeverHalts machine623) :
    Cover (DecidedBelow B) (machine623Prefix 11) := by
  rw [machine623_visited_eq_free_halt]
  exact freeHaltCylinder_cover B machine623 machine623HaltSlot
    ((machine623_halts_only_at_F0 _).2 rfl) hroot

#print axioms machine623_halts_only_at_F0
#print axioms machine623_visited_eq_free_halt
#print axioms machine623_only_one_nontrivial_completion
#print axioms machine623_full_cylinder_if_never

end BB6Coverage
