import Raw122Roster05
import Agent29Raw122Indexed050
import Agent29Raw122Indexed051
import Agent29Raw122Indexed052
import Agent29Raw122Indexed053
import Agent29Raw122Indexed054
import Agent29Raw122Indexed055
import Agent29Raw122Indexed056
import Agent29Raw122Indexed057
import Agent29Raw122Indexed058
import Agent29Raw122Indexed059
import Agent29Raw122Indexed060
import Raw122Counter05
import Raw122Shift05
import Raw122Pair05
import Raw122AHole05
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace BB6.Agent43Raw122Roster
open BB6Coverage BB6.Agent43Raw122ResidualCompose
theorem witnesses05 (hLate : Covered 6766859 p05_007) : ∀ p ∈ tables05, Covered 6766859 p := by
  intro p hp
  simp only [tables05,List.mem_cons,List.not_mem_nil,or_false] at hp
  rcases hp with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
  · have he : p05_000 = BB6Coverage.Agent29Raw122Indexed.M052.table := by
      funext s
      rcases s with ⟨q,b⟩
      have hq : q = 0 ∨ q = 1 ∨ q = 2 ∨ q = 3 ∨ q = 4 ∨ q = 5 := by omega
      rcases hq with rfl|rfl|rfl|rfl|rfl|rfl <;> cases b <;> rfl
    rw [he]
    exact never_bound (BB6Coverage.Agent29Raw122Indexed.M052.never)
  · have he : p05_001 = BB6Coverage.Agent29Raw122Indexed.M050.table := by
      funext s
      rcases s with ⟨q,b⟩
      have hq : q = 0 ∨ q = 1 ∨ q = 2 ∨ q = 3 ∨ q = 4 ∨ q = 5 := by omega
      rcases hq with rfl|rfl|rfl|rfl|rfl|rfl <;> cases b <;> rfl
    rw [he]
    exact never_bound (BB6Coverage.Agent29Raw122Indexed.M050.never)
  · have he : p05_002 = BB6Coverage.Agent29Raw122Indexed.M053.table := by
      funext s
      rcases s with ⟨q,b⟩
      have hq : q = 0 ∨ q = 1 ∨ q = 2 ∨ q = 3 ∨ q = 4 ∨ q = 5 := by omega
      rcases hq with rfl|rfl|rfl|rfl|rfl|rfl <;> cases b <;> rfl
    rw [he]
    exact never_bound (BB6Coverage.Agent29Raw122Indexed.M053.never)
  · have he : p05_003 = BB6Coverage.Agent29Raw122Indexed.M051.table := by
      funext s
      rcases s with ⟨q,b⟩
      have hq : q = 0 ∨ q = 1 ∨ q = 2 ∨ q = 3 ∨ q = 4 ∨ q = 5 := by omega
      rcases hq with rfl|rfl|rfl|rfl|rfl|rfl <;> cases b <;> rfl
    rw [he]
    exact never_bound (BB6Coverage.Agent29Raw122Indexed.M051.never)
  · have he : p05_004 = BB6Coverage.Agent29Raw122Indexed.M055.table := by
      funext s
      rcases s with ⟨q,b⟩
      have hq : q = 0 ∨ q = 1 ∨ q = 2 ∨ q = 3 ∨ q = 4 ∨ q = 5 := by omega
      rcases hq with rfl|rfl|rfl|rfl|rfl|rfl <;> cases b <;> rfl
    rw [he]
    exact never_bound (BB6Coverage.Agent29Raw122Indexed.M055.never)
  · have he : p05_005 = BB6Coverage.Agent29Raw122Indexed.M054.table := by
      funext s
      rcases s with ⟨q,b⟩
      have hq : q = 0 ∨ q = 1 ∨ q = 2 ∨ q = 3 ∨ q = 4 ∨ q = 5 := by omega
      rcases hq with rfl|rfl|rfl|rfl|rfl|rfl <;> cases b <;> rfl
    rw [he]
    exact never_bound (BB6Coverage.Agent29Raw122Indexed.M054.never)
  · have he : p05_006 = BB6Coverage.Agent29Raw122Indexed.M056.table := by
      funext s
      rcases s with ⟨q,b⟩
      have hq : q = 0 ∨ q = 1 ∨ q = 2 ∨ q = 3 ∨ q = 4 ∨ q = 5 := by omega
      rcases hq with rfl|rfl|rfl|rfl|rfl|rfl <;> cases b <;> rfl
    rw [he]
    exact never_bound (BB6Coverage.Agent29Raw122Indexed.M056.never)
  · exact hLate
  · have he : p05_008 = BB6Coverage.Agent29Raw122Indexed.M059.table := by
      funext s
      rcases s with ⟨q,b⟩
      have hq : q = 0 ∨ q = 1 ∨ q = 2 ∨ q = 3 ∨ q = 4 ∨ q = 5 := by omega
      rcases hq with rfl|rfl|rfl|rfl|rfl|rfl <;> cases b <;> rfl
    rw [he]
    exact never_bound (BB6Coverage.Agent29Raw122Indexed.M059.never)
  · have he : p05_009 = BB6Coverage.Agent43Raw122Counter05.table .ld1 := by
      funext s
      rcases s with ⟨q,b⟩
      have hq : q = 0 ∨ q = 1 ∨ q = 2 ∨ q = 3 ∨ q = 4 ∨ q = 5 := by omega
      rcases hq with rfl|rfl|rfl|rfl|rfl|rfl <;> cases b <;> rfl
    rw [he]
    exact never_bound (BB6Coverage.Agent43Raw122Counter05.never .ld1)
  · have he : p05_010 = BB6Coverage.Agent43Raw122Counter05.table .rd1 := by
      funext s
      rcases s with ⟨q,b⟩
      have hq : q = 0 ∨ q = 1 ∨ q = 2 ∨ q = 3 ∨ q = 4 ∨ q = 5 := by omega
      rcases hq with rfl|rfl|rfl|rfl|rfl|rfl <;> cases b <;> rfl
    rw [he]
    exact never_bound (BB6Coverage.Agent43Raw122Counter05.never .rd1)
  · have he : p05_011 = BB6Coverage.Agent43Raw122Counter05.table .le0 := by
      funext s
      rcases s with ⟨q,b⟩
      have hq : q = 0 ∨ q = 1 ∨ q = 2 ∨ q = 3 ∨ q = 4 ∨ q = 5 := by omega
      rcases hq with rfl|rfl|rfl|rfl|rfl|rfl <;> cases b <;> rfl
    rw [he]
    exact never_bound (BB6Coverage.Agent43Raw122Counter05.never .le0)
  · have he : p05_012 = BB6Coverage.Agent43Raw122Shift05.table := by
      funext s
      rcases s with ⟨q,b⟩
      have hq : q = 0 ∨ q = 1 ∨ q = 2 ∨ q = 3 ∨ q = 4 ∨ q = 5 := by omega
      rcases hq with rfl|rfl|rfl|rfl|rfl|rfl <;> cases b <;> rfl
    rw [he]
    exact never_bound (BB6Coverage.Agent43Raw122Shift05.never)
  · have he : p05_013 = BB6Coverage.Agent43Raw122Counter05.table .lf0 := by
      funext s
      rcases s with ⟨q,b⟩
      have hq : q = 0 ∨ q = 1 ∨ q = 2 ∨ q = 3 ∨ q = 4 ∨ q = 5 := by omega
      rcases hq with rfl|rfl|rfl|rfl|rfl|rfl <;> cases b <;> rfl
    rw [he]
    exact never_bound (BB6Coverage.Agent43Raw122Counter05.never .lf0)
  · have he : p05_014 = BB6Coverage.Agent29Raw122Indexed.M060.table := by
      funext s
      rcases s with ⟨q,b⟩
      have hq : q = 0 ∨ q = 1 ∨ q = 2 ∨ q = 3 ∨ q = 4 ∨ q = 5 := by omega
      rcases hq with rfl|rfl|rfl|rfl|rfl|rfl <;> cases b <;> rfl
    rw [he]
    exact never_bound (BB6Coverage.Agent29Raw122Indexed.M060.never)
  · have he : p05_015 = BB6Coverage.Agent29Raw122Indexed.M058.table := by
      funext s
      rcases s with ⟨q,b⟩
      have hq : q = 0 ∨ q = 1 ∨ q = 2 ∨ q = 3 ∨ q = 4 ∨ q = 5 := by omega
      rcases hq with rfl|rfl|rfl|rfl|rfl|rfl <;> cases b <;> rfl
    rw [he]
    exact never_bound (BB6Coverage.Agent29Raw122Indexed.M058.never)
  · have he : p05_016 = BB6Coverage.Agent29Raw122Indexed.M057.table := by
      funext s
      rcases s with ⟨q,b⟩
      have hq : q = 0 ∨ q = 1 ∨ q = 2 ∨ q = 3 ∨ q = 4 ∨ q = 5 := by omega
      rcases hq with rfl|rfl|rfl|rfl|rfl|rfl <;> cases b <;> rfl
    rw [he]
    exact never_bound (BB6Coverage.Agent29Raw122Indexed.M057.never)
  · have he : p05_017 = BB6Coverage.Agent43Raw122Pair05.table true := by
      funext s
      rcases s with ⟨q,b⟩
      have hq : q = 0 ∨ q = 1 ∨ q = 2 ∨ q = 3 ∨ q = 4 ∨ q = 5 := by omega
      rcases hq with rfl|rfl|rfl|rfl|rfl|rfl <;> cases b <;> rfl
    rw [he]
    exact never_bound (BB6Coverage.Agent43Raw122Pair05.never true)
  · have he : p05_018 = BB6Coverage.Agent43Raw122Pair05.table false := by
      funext s
      rcases s with ⟨q,b⟩
      have hq : q = 0 ∨ q = 1 ∨ q = 2 ∨ q = 3 ∨ q = 4 ∨ q = 5 := by omega
      rcases hq with rfl|rfl|rfl|rfl|rfl|rfl <;> cases b <;> rfl
    rw [he]
    exact never_bound (BB6Coverage.Agent43Raw122Pair05.never false)
  · have he : p05_019 = BB6Coverage.Agent43Raw122AHole05.table := by
      funext s
      rcases s with ⟨q,b⟩
      have hq : q = 0 ∨ q = 1 ∨ q = 2 ∨ q = 3 ∨ q = 4 ∨ q = 5 := by omega
      rcases hq with rfl|rfl|rfl|rfl|rfl|rfl <;> cases b <;> rfl
    rw [he]
    exact never_bound (BB6Coverage.Agent43Raw122AHole05.never)
#print axioms witnesses05
end BB6.Agent43Raw122Roster
