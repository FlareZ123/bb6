import Raw122Roster16
import Agent29Raw122Indexed067
import Agent29Raw122Indexed068
import Agent29Raw122Indexed069
import Agent29Raw122Indexed070
import Agent29Raw122Indexed071
import Agent29Raw122Indexed072
import Agent29Raw122Indexed073
import Agent29Raw122Indexed074
import Agent29Raw122Indexed075
import Agent29Raw122Indexed076
import Agent29Raw122Indexed077
import Raw122Direct90
import LateCheck1
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace BB6.Agent43Raw122Roster
open BB6Coverage BB6.Agent43Raw122ResidualCompose
theorem witnesses16 : ∀ p ∈ tables16, Covered 6766859 p := by
  intro p hp
  simp only [tables16,List.mem_cons,List.not_mem_nil,or_false] at hp
  rcases hp with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
  · have he : p16_000 = BB6Coverage.Agent29Raw122Indexed.M067.table := by
      funext s
      rcases s with ⟨q,b⟩
      have hq : q = 0 ∨ q = 1 ∨ q = 2 ∨ q = 3 ∨ q = 4 ∨ q = 5 := by omega
      rcases hq with rfl|rfl|rfl|rfl|rfl|rfl <;> cases b <;> rfl
    rw [he]
    exact never_bound (BB6Coverage.Agent29Raw122Indexed.M067.never)
  · have he : p16_001 = BB6Coverage.Agent29Raw122Indexed.M068.table := by
      funext s
      rcases s with ⟨q,b⟩
      have hq : q = 0 ∨ q = 1 ∨ q = 2 ∨ q = 3 ∨ q = 4 ∨ q = 5 := by omega
      rcases hq with rfl|rfl|rfl|rfl|rfl|rfl <;> cases b <;> rfl
    rw [he]
    exact never_bound (BB6Coverage.Agent29Raw122Indexed.M068.never)
  · have he : p16_002 = BB6Coverage.Agent29Raw122Indexed.M071.table := by
      funext s
      rcases s with ⟨q,b⟩
      have hq : q = 0 ∨ q = 1 ∨ q = 2 ∨ q = 3 ∨ q = 4 ∨ q = 5 := by omega
      rcases hq with rfl|rfl|rfl|rfl|rfl|rfl <;> cases b <;> rfl
    rw [he]
    exact never_bound (BB6Coverage.Agent29Raw122Indexed.M071.never)
  · have he : p16_003 = BB6Coverage.Agent29Raw122Indexed.M069.table := by
      funext s
      rcases s with ⟨q,b⟩
      have hq : q = 0 ∨ q = 1 ∨ q = 2 ∨ q = 3 ∨ q = 4 ∨ q = 5 := by omega
      rcases hq with rfl|rfl|rfl|rfl|rfl|rfl <;> cases b <;> rfl
    rw [he]
    exact never_bound (BB6Coverage.Agent29Raw122Indexed.M069.never)
  · have he : p16_004 = BB6Coverage.Agent29Raw122Indexed.M070.table := by
      funext s
      rcases s with ⟨q,b⟩
      have hq : q = 0 ∨ q = 1 ∨ q = 2 ∨ q = 3 ∨ q = 4 ∨ q = 5 := by omega
      rcases hq with rfl|rfl|rfl|rfl|rfl|rfl <;> cases b <;> rfl
    rw [he]
    exact never_bound (BB6Coverage.Agent29Raw122Indexed.M070.never)
  · have he : p16_005 = BB6Coverage.Agent29Raw122Indexed.M073.table := by
      funext s
      rcases s with ⟨q,b⟩
      have hq : q = 0 ∨ q = 1 ∨ q = 2 ∨ q = 3 ∨ q = 4 ∨ q = 5 := by omega
      rcases hq with rfl|rfl|rfl|rfl|rfl|rfl <;> cases b <;> rfl
    rw [he]
    exact never_bound (BB6Coverage.Agent29Raw122Indexed.M073.never)
  · have he : p16_006 = BB6Coverage.Agent29Raw122Indexed.M074.table := by
      funext s
      rcases s with ⟨q,b⟩
      have hq : q = 0 ∨ q = 1 ∨ q = 2 ∨ q = 3 ∨ q = 4 ∨ q = 5 := by omega
      rcases hq with rfl|rfl|rfl|rfl|rfl|rfl <;> cases b <;> rfl
    rw [he]
    exact never_bound (BB6Coverage.Agent29Raw122Indexed.M074.never)
  · have he : p16_007 = BB6Coverage.Agent29Raw122Indexed.M072.table := by
      funext s
      rcases s with ⟨q,b⟩
      have hq : q = 0 ∨ q = 1 ∨ q = 2 ∨ q = 3 ∨ q = 4 ∨ q = 5 := by omega
      rcases hq with rfl|rfl|rfl|rfl|rfl|rfl <;> cases b <;> rfl
    rw [he]
    exact never_bound (BB6Coverage.Agent29Raw122Indexed.M072.never)
  · have he : p16_008 = BB6Coverage.Agent29Raw122Indexed.M076.table := by
      funext s
      rcases s with ⟨q,b⟩
      have hq : q = 0 ∨ q = 1 ∨ q = 2 ∨ q = 3 ∨ q = 4 ∨ q = 5 := by omega
      rcases hq with rfl|rfl|rfl|rfl|rfl|rfl <;> cases b <;> rfl
    rw [he]
    exact never_bound (BB6Coverage.Agent29Raw122Indexed.M076.never)
  · have he : p16_009 = BB6Coverage.Agent29Raw122Indexed.M075.table := by
      funext s
      rcases s with ⟨q,b⟩
      have hq : q = 0 ∨ q = 1 ∨ q = 2 ∨ q = 3 ∨ q = 4 ∨ q = 5 := by omega
      rcases hq with rfl|rfl|rfl|rfl|rfl|rfl <;> cases b <;> rfl
    rw [he]
    exact never_bound (BB6Coverage.Agent29Raw122Indexed.M075.never)
  · have he : p16_010 = BB6Coverage.Agent31Pump.Raw122DirectGrowth.M90.table := by
      funext s
      rcases s with ⟨q,b⟩
      have hq : q = 0 ∨ q = 1 ∨ q = 2 ∨ q = 3 ∨ q = 4 ∨ q = 5 := by omega
      rcases hq with rfl|rfl|rfl|rfl|rfl|rfl <;> cases b <;> rfl
    rw [he]
    exact never_bound (BB6Coverage.Agent31Pump.Raw122DirectGrowth.M90.never)
  · have he : p16_011 = BB6Coverage.Agent29Raw122Indexed.M077.table := by
      funext s
      rcases s with ⟨q,b⟩
      have hq : q = 0 ∨ q = 1 ∨ q = 2 ∨ q = 3 ∨ q = 4 ∨ q = 5 := by omega
      rcases hq with rfl|rfl|rfl|rfl|rfl|rfl <;> cases b <;> rfl
    rw [he]
    exact never_bound (BB6Coverage.Agent29Raw122Indexed.M077.never)
  · have he : p16_012 = BB6Coverage.Agent29PackedLate.M1.table := by
      funext s
      rcases s with ⟨q,b⟩
      have hq : q = 0 ∨ q = 1 ∨ q = 2 ∨ q = 3 ∨ q = 4 ∨ q = 5 := by omega
      rcases hq with rfl|rfl|rfl|rfl|rfl|rfl <;> cases b <;> rfl
    intro m hm
    have hm' : compatible BB6Coverage.Agent29PackedLate.M1.table m := by
      rw [← he]
      exact hm
    exact BB6Coverage.Agent29PackedLate.M1.bound m hm'
#print axioms witnesses16
end BB6.Agent43Raw122Roster
