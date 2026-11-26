import Raw122Roster00
import Agent29Raw122Indexed008
import Agent29Raw122Indexed009
import Agent29Raw122Indexed010
import Agent29Raw122Indexed011
import Agent29Raw122Indexed012
import Agent29Raw122Indexed013
import Agent29Raw122Indexed014
import Agent29Raw122Indexed015
import Agent29Raw122Indexed016
import Agent29Raw122Indexed017
import Agent29Raw122Indexed018
import Agent29Raw122Indexed019
import Agent29Raw122Indexed020
import Agent29Raw122Indexed021
import Agent29Raw122Indexed022
import Agent29Raw122Indexed023
import Agent29Raw122Indexed024
import Agent29Raw122Indexed025
import Agent29Raw122Indexed026
import Agent29Raw122Indexed027
import Agent29Raw122Indexed028
import Agent29Raw122Indexed029
import Agent29Raw122Indexed030
import Agent29Raw122Indexed031
import Agent29Raw122Indexed032
import Agent29Raw122Indexed033
import Agent29Raw122Indexed102
import Raw122Direct15
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace BB6.Agent43Raw122Roster
open BB6Coverage BB6.Agent43Raw122ResidualCompose
theorem sharpWitnesses00 : ∀ p ∈ tables00, Covered 7014 p := by
  intro p hp
  simp only [tables00,List.mem_cons,List.not_mem_nil,or_false] at hp
  rcases hp with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
  · have he : p00_000 = BB6Coverage.Agent29Raw122Indexed.M009.table := by
      funext s
      rcases s with ⟨q,b⟩
      have hq : q = 0 ∨ q = 1 ∨ q = 2 ∨ q = 3 ∨ q = 4 ∨ q = 5 := by omega
      rcases hq with rfl|rfl|rfl|rfl|rfl|rfl <;> cases b <;> rfl
    rw [he]
    exact never_bound (BB6Coverage.Agent29Raw122Indexed.M009.never)
  · have he : p00_001 = BB6Coverage.Agent29Raw122Indexed.M010.table := by
      funext s
      rcases s with ⟨q,b⟩
      have hq : q = 0 ∨ q = 1 ∨ q = 2 ∨ q = 3 ∨ q = 4 ∨ q = 5 := by omega
      rcases hq with rfl|rfl|rfl|rfl|rfl|rfl <;> cases b <;> rfl
    rw [he]
    exact never_bound (BB6Coverage.Agent29Raw122Indexed.M010.never)
  · have he : p00_002 = BB6Coverage.Agent29Raw122Indexed.M008.table := by
      funext s
      rcases s with ⟨q,b⟩
      have hq : q = 0 ∨ q = 1 ∨ q = 2 ∨ q = 3 ∨ q = 4 ∨ q = 5 := by omega
      rcases hq with rfl|rfl|rfl|rfl|rfl|rfl <;> cases b <;> rfl
    rw [he]
    exact never_bound (BB6Coverage.Agent29Raw122Indexed.M008.never)
  · have he : p00_003 = BB6Coverage.Agent29Raw122Indexed.M102.table := by
      funext s
      rcases s with ⟨q,b⟩
      have hq : q = 0 ∨ q = 1 ∨ q = 2 ∨ q = 3 ∨ q = 4 ∨ q = 5 := by omega
      rcases hq with rfl|rfl|rfl|rfl|rfl|rfl <;> cases b <;> rfl
    rw [he]
    exact never_bound (BB6Coverage.Agent29Raw122Indexed.M102.never)
  · have he : p00_004 = BB6Coverage.Agent29Raw122Indexed.M011.table := by
      funext s
      rcases s with ⟨q,b⟩
      have hq : q = 0 ∨ q = 1 ∨ q = 2 ∨ q = 3 ∨ q = 4 ∨ q = 5 := by omega
      rcases hq with rfl|rfl|rfl|rfl|rfl|rfl <;> cases b <;> rfl
    rw [he]
    exact never_bound (BB6Coverage.Agent29Raw122Indexed.M011.never)
  · have he : p00_005 = BB6Coverage.Agent29Raw122Indexed.M012.table := by
      funext s
      rcases s with ⟨q,b⟩
      have hq : q = 0 ∨ q = 1 ∨ q = 2 ∨ q = 3 ∨ q = 4 ∨ q = 5 := by omega
      rcases hq with rfl|rfl|rfl|rfl|rfl|rfl <;> cases b <;> rfl
    rw [he]
    exact never_bound (BB6Coverage.Agent29Raw122Indexed.M012.never)
  · have he : p00_006 = BB6Coverage.Agent29Raw122Indexed.M014.table := by
      funext s
      rcases s with ⟨q,b⟩
      have hq : q = 0 ∨ q = 1 ∨ q = 2 ∨ q = 3 ∨ q = 4 ∨ q = 5 := by omega
      rcases hq with rfl|rfl|rfl|rfl|rfl|rfl <;> cases b <;> rfl
    rw [he]
    exact never_bound (BB6Coverage.Agent29Raw122Indexed.M014.never)
  · have he : p00_007 = BB6Coverage.Agent29Raw122Indexed.M016.table := by
      funext s
      rcases s with ⟨q,b⟩
      have hq : q = 0 ∨ q = 1 ∨ q = 2 ∨ q = 3 ∨ q = 4 ∨ q = 5 := by omega
      rcases hq with rfl|rfl|rfl|rfl|rfl|rfl <;> cases b <;> rfl
    rw [he]
    exact never_bound (BB6Coverage.Agent29Raw122Indexed.M016.never)
  · have he : p00_008 = BB6Coverage.Agent29Raw122Indexed.M013.table := by
      funext s
      rcases s with ⟨q,b⟩
      have hq : q = 0 ∨ q = 1 ∨ q = 2 ∨ q = 3 ∨ q = 4 ∨ q = 5 := by omega
      rcases hq with rfl|rfl|rfl|rfl|rfl|rfl <;> cases b <;> rfl
    rw [he]
    exact never_bound (BB6Coverage.Agent29Raw122Indexed.M013.never)
  · have he : p00_009 = BB6Coverage.Agent29Raw122Indexed.M015.table := by
      funext s
      rcases s with ⟨q,b⟩
      have hq : q = 0 ∨ q = 1 ∨ q = 2 ∨ q = 3 ∨ q = 4 ∨ q = 5 := by omega
      rcases hq with rfl|rfl|rfl|rfl|rfl|rfl <;> cases b <;> rfl
    rw [he]
    exact never_bound (BB6Coverage.Agent29Raw122Indexed.M015.never)
  · have he : p00_010 = BB6Coverage.Agent29Raw122Indexed.M020.table := by
      funext s
      rcases s with ⟨q,b⟩
      have hq : q = 0 ∨ q = 1 ∨ q = 2 ∨ q = 3 ∨ q = 4 ∨ q = 5 := by omega
      rcases hq with rfl|rfl|rfl|rfl|rfl|rfl <;> cases b <;> rfl
    rw [he]
    exact never_bound (BB6Coverage.Agent29Raw122Indexed.M020.never)
  · have he : p00_011 = BB6Coverage.Agent29Raw122Indexed.M017.table := by
      funext s
      rcases s with ⟨q,b⟩
      have hq : q = 0 ∨ q = 1 ∨ q = 2 ∨ q = 3 ∨ q = 4 ∨ q = 5 := by omega
      rcases hq with rfl|rfl|rfl|rfl|rfl|rfl <;> cases b <;> rfl
    rw [he]
    exact never_bound (BB6Coverage.Agent29Raw122Indexed.M017.never)
  · have he : p00_012 = BB6Coverage.Agent29Raw122Indexed.M021.table := by
      funext s
      rcases s with ⟨q,b⟩
      have hq : q = 0 ∨ q = 1 ∨ q = 2 ∨ q = 3 ∨ q = 4 ∨ q = 5 := by omega
      rcases hq with rfl|rfl|rfl|rfl|rfl|rfl <;> cases b <;> rfl
    rw [he]
    exact never_bound (BB6Coverage.Agent29Raw122Indexed.M021.never)
  · have he : p00_013 = BB6Coverage.Agent29Raw122Indexed.M019.table := by
      funext s
      rcases s with ⟨q,b⟩
      have hq : q = 0 ∨ q = 1 ∨ q = 2 ∨ q = 3 ∨ q = 4 ∨ q = 5 := by omega
      rcases hq with rfl|rfl|rfl|rfl|rfl|rfl <;> cases b <;> rfl
    rw [he]
    exact never_bound (BB6Coverage.Agent29Raw122Indexed.M019.never)
  · have he : p00_014 = BB6Coverage.Agent31Pump.Raw122DirectGrowth.M15.table := by
      funext s
      rcases s with ⟨q,b⟩
      have hq : q = 0 ∨ q = 1 ∨ q = 2 ∨ q = 3 ∨ q = 4 ∨ q = 5 := by omega
      rcases hq with rfl|rfl|rfl|rfl|rfl|rfl <;> cases b <;> rfl
    rw [he]
    exact never_bound (BB6Coverage.Agent31Pump.Raw122DirectGrowth.M15.never)
  · have he : p00_015 = BB6Coverage.Agent29Raw122Indexed.M018.table := by
      funext s
      rcases s with ⟨q,b⟩
      have hq : q = 0 ∨ q = 1 ∨ q = 2 ∨ q = 3 ∨ q = 4 ∨ q = 5 := by omega
      rcases hq with rfl|rfl|rfl|rfl|rfl|rfl <;> cases b <;> rfl
    rw [he]
    exact never_bound (BB6Coverage.Agent29Raw122Indexed.M018.never)
  · have he : p00_016 = BB6Coverage.Agent29Raw122Indexed.M022.table := by
      funext s
      rcases s with ⟨q,b⟩
      have hq : q = 0 ∨ q = 1 ∨ q = 2 ∨ q = 3 ∨ q = 4 ∨ q = 5 := by omega
      rcases hq with rfl|rfl|rfl|rfl|rfl|rfl <;> cases b <;> rfl
    rw [he]
    exact never_bound (BB6Coverage.Agent29Raw122Indexed.M022.never)
  · have he : p00_017 = BB6Coverage.Agent29Raw122Indexed.M023.table := by
      funext s
      rcases s with ⟨q,b⟩
      have hq : q = 0 ∨ q = 1 ∨ q = 2 ∨ q = 3 ∨ q = 4 ∨ q = 5 := by omega
      rcases hq with rfl|rfl|rfl|rfl|rfl|rfl <;> cases b <;> rfl
    rw [he]
    exact never_bound (BB6Coverage.Agent29Raw122Indexed.M023.never)
  · have he : p00_018 = BB6Coverage.Agent29Raw122Indexed.M024.table := by
      funext s
      rcases s with ⟨q,b⟩
      have hq : q = 0 ∨ q = 1 ∨ q = 2 ∨ q = 3 ∨ q = 4 ∨ q = 5 := by omega
      rcases hq with rfl|rfl|rfl|rfl|rfl|rfl <;> cases b <;> rfl
    rw [he]
    exact never_bound (BB6Coverage.Agent29Raw122Indexed.M024.never)
  · have he : p00_019 = BB6Coverage.Agent29Raw122Indexed.M026.table := by
      funext s
      rcases s with ⟨q,b⟩
      have hq : q = 0 ∨ q = 1 ∨ q = 2 ∨ q = 3 ∨ q = 4 ∨ q = 5 := by omega
      rcases hq with rfl|rfl|rfl|rfl|rfl|rfl <;> cases b <;> rfl
    rw [he]
    exact never_bound (BB6Coverage.Agent29Raw122Indexed.M026.never)
  · have he : p00_020 = BB6Coverage.Agent29Raw122Indexed.M025.table := by
      funext s
      rcases s with ⟨q,b⟩
      have hq : q = 0 ∨ q = 1 ∨ q = 2 ∨ q = 3 ∨ q = 4 ∨ q = 5 := by omega
      rcases hq with rfl|rfl|rfl|rfl|rfl|rfl <;> cases b <;> rfl
    rw [he]
    exact never_bound (BB6Coverage.Agent29Raw122Indexed.M025.never)
  · have he : p00_021 = BB6Coverage.Agent29Raw122Indexed.M027.table := by
      funext s
      rcases s with ⟨q,b⟩
      have hq : q = 0 ∨ q = 1 ∨ q = 2 ∨ q = 3 ∨ q = 4 ∨ q = 5 := by omega
      rcases hq with rfl|rfl|rfl|rfl|rfl|rfl <;> cases b <;> rfl
    rw [he]
    exact never_bound (BB6Coverage.Agent29Raw122Indexed.M027.never)
  · have he : p00_022 = BB6Coverage.Agent29Raw122Indexed.M028.table := by
      funext s
      rcases s with ⟨q,b⟩
      have hq : q = 0 ∨ q = 1 ∨ q = 2 ∨ q = 3 ∨ q = 4 ∨ q = 5 := by omega
      rcases hq with rfl|rfl|rfl|rfl|rfl|rfl <;> cases b <;> rfl
    rw [he]
    exact never_bound (BB6Coverage.Agent29Raw122Indexed.M028.never)
  · have he : p00_023 = BB6Coverage.Agent29Raw122Indexed.M029.table := by
      funext s
      rcases s with ⟨q,b⟩
      have hq : q = 0 ∨ q = 1 ∨ q = 2 ∨ q = 3 ∨ q = 4 ∨ q = 5 := by omega
      rcases hq with rfl|rfl|rfl|rfl|rfl|rfl <;> cases b <;> rfl
    rw [he]
    exact never_bound (BB6Coverage.Agent29Raw122Indexed.M029.never)
  · have he : p00_024 = BB6Coverage.Agent29Raw122Indexed.M031.table := by
      funext s
      rcases s with ⟨q,b⟩
      have hq : q = 0 ∨ q = 1 ∨ q = 2 ∨ q = 3 ∨ q = 4 ∨ q = 5 := by omega
      rcases hq with rfl|rfl|rfl|rfl|rfl|rfl <;> cases b <;> rfl
    rw [he]
    exact never_bound (BB6Coverage.Agent29Raw122Indexed.M031.never)
  · have he : p00_025 = BB6Coverage.Agent29Raw122Indexed.M030.table := by
      funext s
      rcases s with ⟨q,b⟩
      have hq : q = 0 ∨ q = 1 ∨ q = 2 ∨ q = 3 ∨ q = 4 ∨ q = 5 := by omega
      rcases hq with rfl|rfl|rfl|rfl|rfl|rfl <;> cases b <;> rfl
    rw [he]
    exact never_bound (BB6Coverage.Agent29Raw122Indexed.M030.never)
  · have he : p00_026 = BB6Coverage.Agent29Raw122Indexed.M032.table := by
      funext s
      rcases s with ⟨q,b⟩
      have hq : q = 0 ∨ q = 1 ∨ q = 2 ∨ q = 3 ∨ q = 4 ∨ q = 5 := by omega
      rcases hq with rfl|rfl|rfl|rfl|rfl|rfl <;> cases b <;> rfl
    rw [he]
    exact never_bound (BB6Coverage.Agent29Raw122Indexed.M032.never)
  · have he : p00_027 = BB6Coverage.Agent29Raw122Indexed.M033.table := by
      funext s
      rcases s with ⟨q,b⟩
      have hq : q = 0 ∨ q = 1 ∨ q = 2 ∨ q = 3 ∨ q = 4 ∨ q = 5 := by omega
      rcases hq with rfl|rfl|rfl|rfl|rfl|rfl <;> cases b <;> rfl
    rw [he]
    exact never_bound (BB6Coverage.Agent29Raw122Indexed.M033.never)
#print axioms sharpWitnesses00
end BB6.Agent43Raw122Roster

namespace BB6.Agent43Raw122Sharp
open BB6Coverage BB6.Agent13BlankDelay BB6.Agent43Raw122ResidualCompose
open BB6.Agent43Raw122Roster
theorem cover00 : Covered 7014 (BB6.Agent43Raw122.child ⟨false,false,0⟩) :=
  BB6.Agent43Raw122Roster.cover00 7014 (by decide) sharpWitnesses00
#print axioms cover00
end BB6.Agent43Raw122Sharp
