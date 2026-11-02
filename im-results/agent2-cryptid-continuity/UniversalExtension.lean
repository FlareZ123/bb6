import Lean.Elab.Tactic.Omega
import BRunSource
import BExit
import AHaltCylinder
import EHaltCylinder

namespace BB6.CryptidUniversalExtension
open CryptidBoundary
open BB6.CryptidBRun

/-- An F-on-zero section with v+2 unary ones is exactly the original
    source-machine initial section carrying v additional ones. -/
theorem section_init (v : Nat) (ys : List Bool) :
    I (v+2) ys = init (List.replicate v true ++ ys) := by
  have hr : List.replicate (v+2) true =
      [true,true] ++ List.replicate v true := by
    rw [show v+2=2+v by omega]
    exact (List.replicate_append_replicate (n:=2) (m:=v) (a:=true)).symm
  simp [I,init,hr]

theorem halt_A_section (k : Nat) (ys : List Bool) :
    (run (12*k*k+41*k+101)
      (I (3*k+3) (false::(BB6.CryptidAHalt.haltWord ++ ys)))).st = 6 := by
  have hn : 3*k+3 = (3*k+1)+2 := by omega
  rw [hn,section_init]
  exact BB6.CryptidAHalt.full_A_halt k ys

theorem halt_E_section (k : Nat) (ys : List Bool) :
    (run (12*k*k+41*k+99)
      (I (3*k+4) (false::(BB6.CryptidEHalt.haltWord ++ ys)))).st = 6 := by
  have hn : 3*k+4 = (3*k+2)+2 := by omega
  rw [hn,section_init]
  exact BB6.CryptidEHalt.full_E_halt k ys

/-- For every unary length n >= 2, at least one finite right suffix
    makes the ORIGINAL D-start six-state Turing machine halt.

    This is an existence theorem about prepared F-on-zero tape sections.
    It says nothing about whether the machine's actual BLANK trajectory
    visits any such suffix, nor whether all suffixes halt. -/
theorem every_unary_has_halting_extension (n : Nat) (hn : 2 ≤ n) :
    ∃ (xs : List Bool) (t : Nat), (run t (I n xs)).st = 6 := by
  obtain ⟨j,z,hj,hzmod⟩ := eventually_non_B n
  have hzge : 2 ≤ z := Nat.le_trans hn (run_nondecreasing hj)
  have hres : z%3=0 ∨ z%3=1 := by omega
  rcases hres with h0 | h1
  · obtain ⟨k,hk⟩ : ∃ k, z=3*k+3 := ⟨z/3-1, by omega⟩
    obtain ⟨t1,ht1⟩ := source_B_chain (false::BB6.CryptidAHalt.haltWord) hj
    refine ⟨List.replicate j false ++ (false::BB6.CryptidAHalt.haltWord),
      t1+(12*k*k+41*k+101), ?_⟩
    rw [run_add, ht1, hk]
    simpa using (halt_A_section k [])
  · obtain ⟨k,hk⟩ : ∃ k, z=3*k+4 := ⟨z/3-1, by omega⟩
    obtain ⟨t1,ht1⟩ := source_B_chain (false::BB6.CryptidEHalt.haltWord) hj
    refine ⟨List.replicate j false ++ (false::BB6.CryptidEHalt.haltWord),
      t1+(12*k*k+41*k+99), ?_⟩
    rw [run_add, ht1, hk]
    simpa using (halt_E_section k [])

#print axioms section_init
#print axioms halt_A_section
#print axioms halt_E_section
#print axioms every_unary_has_halting_extension
end BB6.CryptidUniversalExtension
