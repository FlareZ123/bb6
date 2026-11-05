import Lean

namespace BB429Count58

def live24 : List Nat :=
  [9,73,117,201,209,245,337,465,565,637,765,849,
   949,1021,1033,1097,1141,1233,1361,1673,1789,1917,1973,2045]

def excluded38 : List Nat :=
  [73,117,949,1033,1361,1917,2045,2121,2293,2613,2813,2997,
   3721,3837,4093,4105,4433,4561,4861,5193,5237,5329,
   5769,5885,6069,6153,6261,6353,6481,6609,6781,6993,
   7177,7241,7285,7377,7505,8117]

def lifts96 : List Nat :=
  (List.range 4).flatMap (fun k => live24.map (fun r => 2048*k+r))
def live58 : List Nat := lifts96.filter (fun r => !excluded38.contains r)

theorem lifts96_count : lifts96.length=96 := by decide
theorem lifts96_nodup : lifts96.Nodup := by decide
theorem live58_count : live58.length=58 := by decide
theorem live58_nodup : live58.Nodup := by decide

set_option maxHeartbeats 2000000

theorem live24_bound (r : Nat) (hr : r∈live24) : r<2048 := by
  simp [live24] at hr
  omega

theorem lifts_mem_iff (x : Nat) (hx : x<8192) :
    x∈lifts96 ↔ x%2048∈live24 := by
  constructor
  · intro hm
    obtain ⟨k,hk,hr⟩ := (List.mem_flatMap.mp hm)
    obtain ⟨r,hr,heq⟩ := (List.mem_map.mp hr)
    have hrb := live24_bound r hr
    have hm2 : x%2048 = r := by omega
    simpa [hm2] using hr
  · intro hr
    let k := x/2048
    have hk : k<4 := by dsimp [k]; omega
    have hh : 2048*k+x%2048=x := by
      have h := Nat.mod_add_div x 2048
      dsimp [k]
      omega
    apply List.mem_flatMap.mpr
    refine ⟨k,List.mem_range.mpr hk,?_⟩
    apply List.mem_map.mpr
    exact ⟨x%2048,hr,hh⟩

theorem live58_iff (u : Nat) :
    u%8192∈live58 ↔ u%2048∈live24 ∧ u%8192∉excluded38 := by
  have hl := lifts_mem_iff (u%8192) (Nat.mod_lt u (by decide))
  have hm : (u%8192)%2048=u%2048 := Nat.mod_mod_of_dvd u (by decide)
  simp only [live58, List.mem_filter]
  rw [hl, hm]
  simp

#print axioms live58_iff
#print axioms live58_count
end BB429Count58
