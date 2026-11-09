import SweepExactLevel
import SweepGateEntry

namespace CascadeFastReturn
open CascadeBitSweep

/-- Any successful even exit landing on the immediately higher fatal
    threshold comes from the single exact affine-deficit value 4k+10. -/
theorem adjacent_fatal_parent_deficit (k h u : Nat)
    (hk : firstFailIndex h=k)
    (ho : bitOutcome h=some u)
    (hu : firstFailIndex u=k+1)
    (hf : fatalAt u) :
    (h+k)%2=0 ∧ deficitAt k h=4*k+10 := by
  have hp : 4*2^(k+1)=8*2^k := by rw [Nat.pow_succ]; omega
  have hutarget : u+k+5=8*2^k := by
    dsimp [fatalAt] at hf
    rw [hu, hp] at hf
    omega
  have hbelow : u<8*2^k := by omega
  have heven : (h+k)%2=0 := by
    by_cases he : (h+k)%2=0
    · exact he
    · have hodd : (h+firstFailIndex h)%2=1 := by rw [hk]; omega
      have hc := bitOutcome_odd_crosses h u ho hodd
      rw [hk] at hc
      omega
  have hd := bitOutcome_even_deficit_halves h k u hk heven ho
  have hh := (firstFailIndex_spec h).2
  rw [hk] at hh
  have hupper : h≤8*2^k+k := by omega
  have uupper : u≤8*2^k+k := by omega
  dsimp [deficitAt] at hd ⊢
  constructor
  · exact heven
  · omega

/-- Every arbitrary-length same-level source path ending in a fatal
    adjacent-level entry has a power-of-two affine *initial* deficit. -/
theorem adjacent_fatal_after_same_level_path
    (k entry h u m : Nat)
    (hp : SameLevelPath k entry h m)
    (he : bitOutcome h=some u)
    (hu : firstFailIndex u=k+1)
    (hf : fatalAt u) :
    deficitAt k entry=2^m*(4*k+10) := by
  have hk := same_level_path_last k entry h m hp
  have hlast := (adjacent_fatal_parent_deficit k h u hk he hu hf).2
  have heq := same_level_path_exact_deficit k entry h m hp
  rw [hlast] at heq
  exact heq

/-- Unique exact height of an even parent of a fatal adjacent-level entry. -/
theorem adjacent_fatal_even_exact_parent
    (k h u : Nat)
    (hk : firstFailIndex h=k)
    (ho : bitOutcome h=some u)
    (hu : firstFailIndex u=k+1)
    (hf : fatalAt u) :
    h+(4*k+10)=8*2^k+k := by
  have hdef := (adjacent_fatal_parent_deficit k h u hk ho hu hf).2
  have hh := (firstFailIndex_spec h).2
  rw [hk] at hh
  have hbound : h≤8*2^k+k := by omega
  dsimp [deficitAt] at hdef
  omega

#print axioms adjacent_fatal_parent_deficit
#print axioms adjacent_fatal_after_same_level_path
#print axioms adjacent_fatal_even_exact_parent
end CascadeFastReturn
