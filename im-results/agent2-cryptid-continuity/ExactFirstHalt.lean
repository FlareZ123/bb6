import Lean.Elab.Tactic.Omega
import UniversalExtension

set_option maxRecDepth 8192

namespace BB6.CryptidExactHalt
open BB6.CryptidBRun
open BB6.CryptidUniversalExtension
open CryptidBoundary

/-- The arithmetic A-family halt occurs on the immediately following
    transition from an F-on-one machine configuration. -/
theorem halt_A_section_before (k : Nat) (ys : List Bool) :
    (run (12*k*k+41*k+100)
      (I (3*k+3) (false::(BB6.CryptidAHalt.haltWord ++ ys)))).st = 5 ∧
    (run (12*k*k+41*k+100)
      (I (3*k+3) (false::(BB6.CryptidAHalt.haltWord ++ ys)))).h = true := by
  have hn : 3*k+3 = (3*k+1)+2 := by omega
  simp only [hn,section_init]
  exact BB6.CryptidAHalt.full_A_before_halt k ys

theorem halt_E_section_before (k : Nat) (ys : List Bool) :
    (run (12*k*k+41*k+98)
      (I (3*k+4) (false::(BB6.CryptidEHalt.haltWord ++ ys)))).st = 5 ∧
    (run (12*k*k+41*k+98)
      (I (3*k+4) (false::(BB6.CryptidEHalt.haltWord ++ ys)))).h = true := by
  have hn : 3*k+4 = (3*k+2)+2 := by omega
  simp only [hn,section_init]
  exact BB6.CryptidEHalt.full_E_before_halt k ys

/-- A source-level precursor refinement to the arbitrary n>=2
    universal-halting-extension theorem. The machine is F reading one at t,
    and in the frozen state6 at t+1. -/
theorem every_unary_has_pre_halt_extension
    (n : Nat) (hn : 2 ≤ n) :
    ∃ (xs : List Bool) (t : Nat),
      (run t (I n xs)).st = 5 ∧
      (run t (I n xs)).h = true ∧
      (run (t+1) (I n xs)).st = 6 := by
  obtain ⟨j,z,hj,hzmod⟩ := eventually_non_B n
  have hzge : 2 ≤ z := Nat.le_trans hn (run_nondecreasing hj)
  have hres : z%3=0 ∨ z%3=1 := by omega
  rcases hres with h0 | h1
  · obtain ⟨k,hk⟩ : ∃ k, z=3*k+3 := ⟨z/3-1, by omega⟩
    obtain ⟨t1,ht1⟩ := source_B_chain (false::BB6.CryptidAHalt.haltWord) hj
    refine ⟨List.replicate j false ++ (false::BB6.CryptidAHalt.haltWord),
      t1+(12*k*k+41*k+100), ?_, ?_, ?_⟩
    · rw [run_add,ht1,hk]
      exact (halt_A_section_before k []).1
    · rw [run_add,ht1,hk]
      exact (halt_A_section_before k []).2
    · have ht : t1+(12*k*k+41*k+100)+1 = t1+(12*k*k+41*k+101) := by omega
      rw [ht,run_add,ht1,hk]
      exact halt_A_section k []
  · obtain ⟨k,hk⟩ : ∃ k, z=3*k+4 := ⟨z/3-1, by omega⟩
    obtain ⟨t1,ht1⟩ := source_B_chain (false::BB6.CryptidEHalt.haltWord) hj
    refine ⟨List.replicate j false ++ (false::BB6.CryptidEHalt.haltWord),
      t1+(12*k*k+41*k+98), ?_, ?_, ?_⟩
    · rw [run_add,ht1,hk]
      exact (halt_E_section_before k []).1
    · rw [run_add,ht1,hk]
      exact (halt_E_section_before k []).2
    · have ht : t1+(12*k*k+41*k+98)+1 = t1+(12*k*k+41*k+99) := by omega
      rw [ht,run_add,ht1,hk]
      exact halt_E_section k []

/-- n=0,1 have direct kernel-computed F-on-one predecessors. -/
theorem zero_unary_before_halt :
    (run 150
      (I 0 [false,false,false,true,true,false,true,true,false,false])).st = 5 ∧
    (run 150
      (I 0 [false,false,false,true,true,false,true,true,false,false])).h = true := by
  decide

theorem one_unary_before_halt :
    (run 73
      (I 1 [false,true,true,false,true,true,false,false])).st = 5 ∧
    (run 73
      (I 1 [false,true,true,false,true,true,false,false])).h = true := by
  decide

/-- For every unary F-section (including n=0,1), there exists a
    *prepared* finite input suffix for which an actual F-on-one halt
    transition exists at a certified exact raw machine time. -/
theorem every_unary_has_pre_halt_extension_all (n : Nat) :
    ∃ (xs : List Bool) (t : Nat),
      (run t (I n xs)).st = 5 ∧
      (run t (I n xs)).h = true ∧
      (run (t+1) (I n xs)).st = 6 := by
  by_cases hn : 2 ≤ n
  · exact every_unary_has_pre_halt_extension n hn
  · have hh : n=0 ∨ n=1 := by omega
    rcases hh with rfl | rfl
    · refine ⟨[false,false,false,true,true,false,true,true,false,false],150,
        zero_unary_before_halt.1,zero_unary_before_halt.2,?_⟩
      simpa using zero_unary_halts
    · refine ⟨[false,true,true,false,true,true,false,false],73,
        one_unary_before_halt.1,one_unary_before_halt.2,?_⟩
      simpa using one_unary_halts

#print axioms halt_A_section_before
#print axioms halt_E_section_before
#print axioms every_unary_has_pre_halt_extension
#print axioms zero_unary_before_halt
#print axioms one_unary_before_halt
#print axioms every_unary_has_pre_halt_extension_all
end BB6.CryptidExactHalt
