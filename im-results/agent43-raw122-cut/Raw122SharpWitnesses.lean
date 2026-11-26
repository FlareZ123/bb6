import Raw122SharpLate
import Raw122Sharp00
import Raw122Roster05Witnesses
import Raw122Roster16Witnesses
import Raw122Sharp17
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace BB6.Agent43Raw122Roster
open BB6Coverage BB6.Agent43Raw122ResidualCompose
end BB6.Agent43Raw122Roster
namespace BB6.Agent43Raw122Roster
open BB6Coverage BB6.Agent43Raw122ResidualCompose
theorem sharpWitnesses05 (hLate : Covered 6659487 p05_007) : ∀ p ∈ tables05, Covered 6659487 p := by
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
#print axioms sharpWitnesses05
end BB6.Agent43Raw122Roster
namespace BB6.Agent43Raw122Roster
open BB6Coverage BB6.Agent43Raw122ResidualCompose
theorem sharpWitnesses16 : ∀ p ∈ tables16, Covered 1296926 p := by
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
    exact BB6.Agent43Raw122Sharp.late1_bound m hm'
#print axioms sharpWitnesses16
end BB6.Agent43Raw122Roster
namespace BB6.Agent43Raw122Roster
open BB6Coverage BB6.Agent43Raw122ResidualCompose
end BB6.Agent43Raw122Roster
namespace BB6.Agent43Raw122Sharp
open BB6Coverage BB6.Agent13BlankDelay BB6.Agent43Raw122ResidualCompose
open BB6.Agent43Raw122Roster

theorem cover05 : Covered 6659487 (BB6.Agent43Raw122.child ⟨false,false,5⟩) :=
  BB6.Agent43Raw122Roster.cover05 6659487 (by decide) (sharpWitnesses05 late0_bound)

theorem cover16 : Covered 1296926 (BB6.Agent43Raw122.child ⟨true,false,4⟩) :=
  BB6.Agent43Raw122Roster.cover16 1296926 (by decide) sharpWitnesses16

mport Raw122SharpLate
import Raw122Sharp00
import Raw122Roster05Witnesses
import Raw122Roster16Witnesses
import Raw122Sharp17
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace BB6.Agent43Raw122Roster
open BB6Coverage BB6.Agent43Raw122ResidualCompose
end BB6.Agent43Raw122Roster
namespace BB6.Agent43Raw122Roster
open BB6Coverage BB6.Agent43Raw122ResidualCompose
theorem sharpWitnesses05 (hLate : Covered 6659487 p05_007) : ∀ p ∈ tables05, Covered 6659487 p := by
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
#print axioms sharpWitnesses05
end BB6.Agent43Raw122Roster
namespace BB6.Agent43Raw122Roster
open BB6Coverage BB6.Agent43Raw122ResidualCompose
theorem sharpWitnesses16 : ∀ p ∈ tables16, Covered 1296926 p := by
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
    exact BB6.Agent43Raw122Sharp.late1_bound m hm'
#print axioms sharpWitnesses16
end BB6.Agent43Raw122Roster
namespace BB6.Agent43Raw122Roster
open BB6Coverage BB6.Agent43Raw122ResidualCompose
end BB6.Agent43Raw122Roster
namespace BB6.Agent43Raw122Sharp
open BB6Coverage BB6.Agent13BlankDelay BB6.Agent43Raw122ResidualCompose
open BB6.Agent43Raw122Roster

theorem cover05 : Covered 6659487 (BB6.Agent43Raw122.child ⟨false,false,5⟩) :=
  BB6.Agent43Raw122Roster.cover05 6659487 (by decide) (sharpWitnesses05 late0_bound)

theorem cover16 : Covered 1296926 (BB6.Agent43Raw122.child ⟨true,false,4⟩) :=
  BB6.Agent43Raw122Roster.cover16 1296926 (by decide) sharpWitnesses16

theorem cover17 : Covered 7014 (BB6.Agent43Raw122.child ⟨true,false,5⟩) :=
  BB6.Agent43Raw122Roster.cover17 7014 (by decide) sharpWitnesses17
#print axioms cover05
#print axioms cover16
end BB6.Agent43Raw122Sharp
