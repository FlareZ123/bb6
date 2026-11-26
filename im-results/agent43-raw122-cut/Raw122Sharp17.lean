import Raw122Roster17
import Agent29Raw122Indexed078
import Agent29Raw122Indexed079
import Agent29Raw122Indexed080
import Agent29Raw122Indexed081
import Agent29Raw122Indexed082
import Agent29Raw122Indexed083
import Agent29Raw122Indexed084
import Agent29Raw122Indexed085
import Agent29Raw122Indexed086
import Agent29Raw122Indexed087
import Agent29Raw122Indexed088
import Agent29Raw122Indexed089
import Agent29Raw122Indexed090
import Agent29Raw122Indexed091
import Agent29Raw122Indexed092
import Agent29Raw122Indexed093
import Agent29Raw122Indexed094
import Agent29Raw122Indexed095
import Agent29Raw122Indexed096
import Agent29Raw122Indexed097
import Agent29Raw122Indexed098
import Agent29Raw122Indexed099
import Raw122Direct104
import Raw122Counter17
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace BB6.Agent43Raw122Roster
open BB6Coverage BB6.Agent43Raw122ResidualCompose
theorem sharpWitnesses17 : ∀ p ∈ tables17, Covered 7014 p := by
  intro p hp
  simp only [tables17,List.mem_cons,List.not_mem_nil,or_false] at hp
  rcases hp with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
  · have he : p17_000 = BB6Coverage.Agent29Raw122Indexed.M078.table := by
      funext s
      rcases s with ⟨q,b⟩
      have hq : q = 0 ∨ q = 1 ∨ q = 2 ∨ q = 3 ∨ q = 4 ∨ q = 5 := by omega
      rcases hq with rfl|rfl|rfl|rfl|rfl|rfl <;> cases b <;> rfl
    rw [he]
    exact never_bound (BB6Coverage.Agent29Raw122Indexed.M078.never)
  · have he : p17_001 = BB6Coverage.Agent29Raw122Indexed.M082.table := by
      funext s
      rcases s with ⟨q,b⟩
      have hq : q = 0 ∨ q = 1 ∨ q = 2 ∨ q = 3 ∨ q = 4 ∨ q = 5 := by omega
      rcases hq with rfl|rfl|rfl|rfl|rfl|rfl <;> cases b <;> rfl
    rw [he]
    exact never_bound (BB6Coverage.Agent29Raw122Indexed.M082.never)
  · have he : p17_002 = BB6Coverage.Agent29Raw122Indexed.M080.table := by
      funext s
      rcases s with ⟨q,b⟩
      have hq : q = 0 ∨ q = 1 ∨ q = 2 ∨ q = 3 ∨ q = 4 ∨ q = 5 := by omega
      rcases hq with rfl|rfl|rfl|rfl|rfl|rfl <;> cases b <;> rfl
    rw [he]
    exact never_bound (BB6Coverage.Agent29Raw122Indexed.M080.never)
  · have he : p17_003 = BB6Coverage.Agent29Raw122Indexed.M079.table := by
      funext s
      rcases s with ⟨q,b⟩
      have hq : q = 0 ∨ q = 1 ∨ q = 2 ∨ q = 3 ∨ q = 4 ∨ q = 5 := by omega
      rcases hq with rfl|rfl|rfl|rfl|rfl|rfl <;> cases b <;> rfl
    rw [he]
    exact never_bound (BB6Coverage.Agent29Raw122Indexed.M079.never)
  · have he : p17_004 = BB6Coverage.Agent29Raw122Indexed.M081.table := by
      funext s
      rcases s with ⟨q,b⟩
      have hq : q = 0 ∨ q = 1 ∨ q = 2 ∨ q = 3 ∨ q = 4 ∨ q = 5 := by omega
      rcases hq with rfl|rfl|rfl|rfl|rfl|rfl <;> cases b <;> rfl
    rw [he]
    exact never_bound (BB6Coverage.Agent29Raw122Indexed.M081.never)
  · have he : p17_005 = BB6Coverage.Agent29Raw122Indexed.M083.table := by
      funext s
      rcases s with ⟨q,b⟩
      have hq : q = 0 ∨ q = 1 ∨ q = 2 ∨ q = 3 ∨ q = 4 ∨ q = 5 := by omega
      rcases hq with rfl|rfl|rfl|rfl|rfl|rfl <;> cases b <;> rfl
    rw [he]
    exact never_bound (BB6Coverage.Agent29Raw122Indexed.M083.never)
  · have he : p17_006 = BB6Coverage.Agent29Raw122Indexed.M088.table := by
      funext s
      rcases s with ⟨q,b⟩
      have hq : q = 0 ∨ q = 1 ∨ q = 2 ∨ q = 3 ∨ q = 4 ∨ q = 5 := by omega
      rcases hq with rfl|rfl|rfl|rfl|rfl|rfl <;> cases b <;> rfl
    rw [he]
    exact never_bound (BB6Coverage.Agent29Raw122Indexed.M088.never)
  · have he : p17_007 = BB6Coverage.Agent29Raw122Indexed.M086.table := by
      funext s
      rcases s with ⟨q,b⟩
      have hq : q = 0 ∨ q = 1 ∨ q = 2 ∨ q = 3 ∨ q = 4 ∨ q = 5 := by omega
      rcases hq with rfl|rfl|rfl|rfl|rfl|rfl <;> cases b <;> rfl
    rw [he]
    exact never_bound (BB6Coverage.Agent29Raw122Indexed.M086.never)
  · have he : p17_008 = BB6Coverage.Agent29Raw122Indexed.M084.table := by
      funext s
      rcases s with ⟨q,b⟩
      have hq : q = 0 ∨ q = 1 ∨ q = 2 ∨ q = 3 ∨ q = 4 ∨ q = 5 := by omega
      rcases hq with rfl|rfl|rfl|rfl|rfl|rfl <;> cases b <;> rfl
    rw [he]
    exact never_bound (BB6Coverage.Agent29Raw122Indexed.M084.never)
  · have he : p17_009 = BB6Coverage.Agent29Raw122Indexed.M085.table := by
      funext s
      rcases s with ⟨q,b⟩
      have hq : q = 0 ∨ q = 1 ∨ q = 2 ∨ q = 3 ∨ q = 4 ∨ q = 5 := by omega
      rcases hq with rfl|rfl|rfl|rfl|rfl|rfl <;> cases b <;> rfl
    rw [he]
    exact never_bound (BB6Coverage.Agent29Raw122Indexed.M085.never)
  · have he : p17_010 = BB6Coverage.Agent29Raw122Indexed.M087.table := by
      funext s
      rcases s with ⟨q,b⟩
      have hq : q = 0 ∨ q = 1 ∨ q = 2 ∨ q = 3 ∨ q = 4 ∨ q = 5 := by omega
      rcases hq with rfl|rfl|rfl|rfl|rfl|rfl <;> cases b <;> rfl
    rw [he]
    exact never_bound (BB6Coverage.Agent29Raw122Indexed.M087.never)
  · have he : p17_011 = BB6Coverage.Agent29Raw122Indexed.M089.table := by
      funext s
      rcases s with ⟨q,b⟩
      have hq : q = 0 ∨ q = 1 ∨ q = 2 ∨ q = 3 ∨ q = 4 ∨ q = 5 := by omega
      rcases hq with rfl|rfl|rfl|rfl|rfl|rfl <;> cases b <;> rfl
    rw [he]
    exact never_bound (BB6Coverage.Agent29Raw122Indexed.M089.never)
  · have he : p17_012 = BB6Coverage.Agent31Pump.Raw122DirectGrowth.M104.table := by
      funext s
      rcases s with ⟨q,b⟩
      have hq : q = 0 ∨ q = 1 ∨ q = 2 ∨ q = 3 ∨ q = 4 ∨ q = 5 := by omega
      rcases hq with rfl|rfl|rfl|rfl|rfl|rfl <;> cases b <;> rfl
    rw [he]
    exact never_bound (BB6Coverage.Agent31Pump.Raw122DirectGrowth.M104.never)
  · have he : p17_013 = BB6Coverage.Agent29Raw122Indexed.M090.table := by
      funext s
      rcases s with ⟨q,b⟩
      have hq : q = 0 ∨ q = 1 ∨ q = 2 ∨ q = 3 ∨ q = 4 ∨ q = 5 := by omega
      rcases hq with rfl|rfl|rfl|rfl|rfl|rfl <;> cases b <;> rfl
    rw [he]
    exact never_bound (BB6Coverage.Agent29Raw122Indexed.M090.never)
  · have he : p17_014 = BB6Coverage.Agent29Raw122Indexed.M091.table := by
      funext s
      rcases s with ⟨q,b⟩
      have hq : q = 0 ∨ q = 1 ∨ q = 2 ∨ q = 3 ∨ q = 4 ∨ q = 5 := by omega
      rcases hq with rfl|rfl|rfl|rfl|rfl|rfl <;> cases b <;> rfl
    rw [he]
    exact never_bound (BB6Coverage.Agent29Raw122Indexed.M091.never)
  · have he : p17_015 = BB6Coverage.Agent29Raw122Indexed.M092.table := by
      funext s
      rcases s with ⟨q,b⟩
      have hq : q = 0 ∨ q = 1 ∨ q = 2 ∨ q = 3 ∨ q = 4 ∨ q = 5 := by omega
      rcases hq with rfl|rfl|rfl|rfl|rfl|rfl <;> cases b <;> rfl
    rw [he]
    exact never_bound (BB6Coverage.Agent29Raw122Indexed.M092.never)
  · have he : p17_016 = BB6Coverage.Agent29Raw122Indexed.M093.table := by
      funext s
      rcases s with ⟨q,b⟩
      have hq : q = 0 ∨ q = 1 ∨ q = 2 ∨ q = 3 ∨ q = 4 ∨ q = 5 := by omega
      rcases hq with rfl|rfl|rfl|rfl|rfl|rfl <;> cases b <;> rfl
    rw [he]
    exact never_bound (BB6Coverage.Agent29Raw122Indexed.M093.never)
  · have he : p17_017 = BB6Coverage.Agent29Raw122Indexed.M097.table := by
      funext s
      rcases s with ⟨q,b⟩
      have hq : q = 0 ∨ q = 1 ∨ q = 2 ∨ q = 3 ∨ q = 4 ∨ q = 5 := by omega
      rcases hq with rfl|rfl|rfl|rfl|rfl|rfl <;> cases b <;> rfl
    rw [he]
    exact never_bound (BB6Coverage.Agent29Raw122Indexed.M097.never)
  · have he : p17_018 = BB6Coverage.Agent29Raw122Indexed.M095.table := by
      funext s
      rcases s with ⟨q,b⟩
      have hq : q = 0 ∨ q = 1 ∨ q = 2 ∨ q = 3 ∨ q = 4 ∨ q = 5 := by omega
      rcases hq with rfl|rfl|rfl|rfl|rfl|rfl <;> cases b <;> rfl
    rw [he]
    exact never_bound (BB6Coverage.Agent29Raw122Indexed.M095.never)
  · have he : p17_019 = BB6Coverage.Agent29Raw122Indexed.M094.table := by
      funext s
      rcases s with ⟨q,b⟩
      have hq : q = 0 ∨ q = 1 ∨ q = 2 ∨ q = 3 ∨ q = 4 ∨ q = 5 := by omega
      rcases hq with rfl|rfl|rfl|rfl|rfl|rfl <;> cases b <;> rfl
    rw [he]
    exact never_bound (BB6Coverage.Agent29Raw122Indexed.M094.never)
  · have he : p17_020 = BB6Coverage.Agent29Raw122Indexed.M096.table := by
      funext s
      rcases s with ⟨q,b⟩
      have hq : q = 0 ∨ q = 1 ∨ q = 2 ∨ q = 3 ∨ q = 4 ∨ q = 5 := by omega
      rcases hq with rfl|rfl|rfl|rfl|rfl|rfl <;> cases b <;> rfl
    rw [he]
    exact never_bound (BB6Coverage.Agent29Raw122Indexed.M096.never)
  · have he : p17_021 = BB6Coverage.Agent29Raw122Indexed.M098.table := by
      funext s
      rcases s with ⟨q,b⟩
      have hq : q = 0 ∨ q = 1 ∨ q = 2 ∨ q = 3 ∨ q = 4 ∨ q = 5 := by omega
      rcases hq with rfl|rfl|rfl|rfl|rfl|rfl <;> cases b <;> rfl
    rw [he]
    exact never_bound (BB6Coverage.Agent29Raw122Indexed.M098.never)
  · have he : p17_022 = BB6Coverage.Agent43Raw122Counter17.table := by
      funext s
      rcases s with ⟨q,b⟩
      have hq : q = 0 ∨ q = 1 ∨ q = 2 ∨ q = 3 ∨ q = 4 ∨ q = 5 := by omega
      rcases hq with rfl|rfl|rfl|rfl|rfl|rfl <;> cases b <;> rfl
    rw [he]
    exact never_bound (BB6Coverage.Agent43Raw122Counter17.never)
  · have he : p17_023 = BB6Coverage.Agent29Raw122Indexed.M099.table := by
      funext s
      rcases s with ⟨q,b⟩
      have hq : q = 0 ∨ q = 1 ∨ q = 2 ∨ q = 3 ∨ q = 4 ∨ q = 5 := by omega
      rcases hq with rfl|rfl|rfl|rfl|rfl|rfl <;> cases b <;> rfl
    rw [he]
    exact never_bound (BB6Coverage.Agent29Raw122Indexed.M099.never)
#print axioms sharpWitnesses17
end BB6.Agent43Raw122Roster

namespace BB6.Agent43Raw122Sharp
open BB6Coverage BB6.Agent13BlankDelay BB6.Agent43Raw122ResidualCompose
open BB6.Agent43Raw122Roster
theorem cover17 : Covered 7014 (BB6.Agent43Raw122.child ⟨true,false,5⟩) :=
  BB6.Agent43Raw122Roster.cover17 7014 (by decide) sharpWitnesses17
#print axioms cover17
end BB6.Agent43Raw122Sharp
