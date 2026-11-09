import SweepLevelBound

namespace CascadeFastReturn
open CascadeBitSweep

private theorem kplus6_le_eight_pow (k : Nat) : k+6 ≤ 8*2^k := by
  induction k with
  | zero => decide
  | succ k ih =>
    rw [Nat.pow_succ]
    omega

/-- Every successful even source reset remains below its old 8·2^k boundary. -/
theorem even_edge_below_eight (h u : Nat)
    (ho : bitOutcome h=some u)
    (heven : (h+firstFailIndex h)%2=0) :
    u+3 ≤ 8*2^(firstFailIndex h) := by
  let k := firstFailIndex h
  have hf := (firstFailIndex_spec h).2
  have hnot : h+k+4 ≠ 4*2^k := by
    intro hdead
    have hn : bitOutcome h=none := by
      simp [bitOutcome, show firstFailIndex h=k from rfl, hdead]
    rw [hn] at ho
    cases ho
  have he : u=4*2^k+(h+k)/2 := by
    have hpar : (h+k)%2=0 := heven
    simp [bitOutcome, show firstFailIndex h=k from rfl, hnot, hpar] at ho
    exact ho.symm
  change u+3≤8*2^k
  rw [he]
  change h+k+5<8*2^k at hf
  omega

/-- Even source resets either stay in their level or advance exactly one level. -/
theorem even_edge_address_at_most_succ (h u : Nat)
    (ho : bitOutcome h=some u)
    (heven : (h+firstFailIndex h)%2=0) :
    firstFailIndex u ≤ firstFailIndex h+1 := by
  let k := firstFailIndex h
  have hb := even_edge_below_eight h u ho heven
  have hkplus := kplus6_le_eight_pow k
  have hnext : u+(k+1)+5<8*2^(k+1) := by
    rw [Nat.pow_succ]
    change u+3≤8*2^k at hb
    omega
  by_cases hle : firstFailIndex u≤k+1
  · exact hle
  · have hlt : k+1 < firstFailIndex u := by omega
    have hprior := (firstFailIndex_spec u).1 (k+1) hlt
    rw [Nat.pow_succ] at hprior
    omega

/-- Exact source level transition criterion for the even branch, including
    source reset heights below the simpler synthetic 4·2^k band. -/
theorem even_edge_same_iff_large_deficit (h u : Nat)
    (ho : bitOutcome h=some u)
    (heven : (h+firstFailIndex h)%2=0) :
    (firstFailIndex u=firstFailIndex h ↔
       4*firstFailIndex h+12 ≤ deficitAt (firstFailIndex h) h) := by
  let k := firstFailIndex h
  have hd := bitOutcome_even_deficit_halves h k u rfl heven ho
  have huge : h+k+5<8*2^k := (firstFailIndex_spec h).2
  have hmono := bitOutcome_address_monotone h u ho
  have hubound := even_edge_address_at_most_succ h u ho heven
  have hupper : h≤8*2^k+k := by omega
  have uupper : u≤8*2^k+k := by
    have hb := even_edge_below_eight h u ho heven
    change u+3≤8*2^k at hb
    omega
  constructor
  · intro heq
    have hh := (firstFailIndex_spec u).2
    rw [heq] at hh
    change u+k+5<8*2^k at hh
    change 8*2^k+k-h=2*(8*2^k+k-u) at hd
    change 4*k+12≤8*2^k+k-h
    omega
  · intro hbig
    have hnextlow : u+k+5<8*2^k := by
      change 8*2^k+k-h=2*(8*2^k+k-u) at hd
      change 4*k+12≤8*2^k+k-h at hbig
      omega
    by_cases heq : firstFailIndex u=k
    · exact heq
    · have hlt : k<firstFailIndex u := by omega
      have hp := (firstFailIndex_spec u).1 k hlt
      omega

/-- Exact complementary test for the unique one-level even exit. -/
theorem even_edge_advance_iff_small_deficit (h u : Nat)
    (ho : bitOutcome h=some u)
    (heven : (h+firstFailIndex h)%2=0) :
    (firstFailIndex u=firstFailIndex h+1 ↔
       deficitAt (firstFailIndex h) h<4*firstFailIndex h+12) := by
  have hmono := bitOutcome_address_monotone h u ho
  have hcap := even_edge_address_at_most_succ h u ho heven
  have hsame := even_edge_same_iff_large_deficit h u ho heven
  omega

#print axioms even_edge_below_eight
#print axioms even_edge_address_at_most_succ
#print axioms even_edge_same_iff_large_deficit
#print axioms even_edge_advance_iff_small_deficit
end CascadeFastReturn
