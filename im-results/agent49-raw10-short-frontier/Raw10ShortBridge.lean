import Raw10ShortData
namespace BB6.Agent49Raw10Short
open BB6Coverage BB6.Agent13BlankDelay BB6.Agent49BoxBridge BB6.Agent49Box
open BB6.Agent13CrossRouteHeldLeaf109

def newTables : List PartialMachine := leaves.map (fun l => table l.1)
def combinedTables : List PartialMachine := sideTables ++ [held] ++ newTables
def remaining := remainder firstOneB0_1LC combinedTables

theorem newTables_sound (p : PartialMachine) (hp : p ∈ newTables) :
    ∀ m, compatible p m → WeightedBound 7014 m := by
  obtain ⟨l,hl,rfl⟩ := List.mem_map.mp hp
  exact leaves_sound l hl

def combinedCover (B : Nat) (hB : 7014 ≤ B)
    (hHeld : ∀ m, compatible held m → WeightedBound B m)
    (hOpen : ∀ r ∈ remaining, ∀ m, Fits r m → WeightedBound B m) :
    Cover (WeightedBound B) firstOneB0_1LC :=
  coverFromRemainder B firstOneB0_1LC combinedTables
    (fun q hq m hm => by
      rcases List.mem_append.mp hq with hprev | hnew
      · rcases List.mem_append.mp hprev with hs | hh
        · obtain ⟨w,hw,rfl⟩ := List.mem_map.mp hs
          have hb := b0_1lcSideWitnesses_safe w hw m hm
          intro k d hk hd
          exact Nat.le_trans (hb k d hk hd) hB
        · have he : q = held := by simpa using hh
          subst q
          exact hHeld m hm
      · have hb := newTables_sound q hnew m hm
        intro k d hk hd
        exact Nat.le_trans (hb k d hk hd) hB)
    hOpen

#print axioms combinedCover
end BB6.Agent49Raw10Short
