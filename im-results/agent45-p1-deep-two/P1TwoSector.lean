import P1TwoIff

namespace BB6.Agent45TwoRoot

private theorem power16_linear (q : Nat) : q+1 ≤ 2^(16*q) := by
  induction q with
  | zero => decide
  | succ q ih =>
      have hp : 2^(16*(q+1))=65536*2^(16*q) := by
        have he : 16*(q+1)=16*q+16 := by omega
        rw [he,Nat.pow_add]
        rw [show (2:Nat)^16=65536 by decide]
        omega
      rw [hp]
      omega

def u2 (q : Nat) : Nat := 7*2^(16*q)-4*q-3

private theorem pow16_even (q : Nat) (hq : 1≤q) : (2^(16*q))%2=0 := by
  have hh : 2^1 ∣ 2^(16*q) := Nat.pow_dvd_pow 2 (by omega)
  have hh2 : 2 ∣ 2^(16*q) := by simpa using hh
  exact Nat.dvd_iff_mod_eq_zero.mp hh2

private theorem u2_properties (q : Nat) (hq : 1≤q) :
    3 ≤ u2 q ∧ (u2 q)%2=1 ∧ u2 q+4*q+3=7*2^(16*q) := by
  have hp := power16_linear q
  have he := pow16_even q hq
  have hsum : u2 q+4*q+3=7*2^(16*q) := by
    dsimp [u2]
    omega
  constructor
  · omega
  constructor
  · omega
  · exact hsum

private theorem root_index_two (q : Nat) (hq : 1≤q) :
    14*2^(16*q+2)-2*(16*q+2)-16=8*u2 q+4 := by
  have hp : 2^(16*q+2)=4*2^(16*q) := by
    rw [Nat.pow_add]
    rw [show (2:Nat)^2=4 by decide]
    omega
  have hs := (u2_properties q hq).2.2
  omega

/-- Uniform all-natural n=16q+2 closure gateway: if that critical hub
    is reachable, then one of exactly two explicit earlier positive-odd
    feeders must already be blank-reachable. q=0 is the separately
    handled n=2 boundary critical index. -/
theorem two_sector_requires_two_feeders (q : Nat) (hq : 1≤q)
    (hr : BB6.Agent1.Reach
      (14*2^(16*q+2)-2*(16*q+2)-16) 3) :
    BB6.Agent1.Reach (4*u2 q-4) (4*u2 q+9) ∨
    BB6.Agent1.Reach (6*u2 q-2) (2*u2 q+5) := by
  have hid := root_index_two q hq
  rw [hid] at hr
  obtain ⟨hu,hodd,_⟩ := u2_properties q hq
  exact root_requires_one_of_two (u2 q) hodd hu hr

/-- Exact equivalence for all n=16q+2 (q≥1): a critical-root reachability
    query is equivalent to two explicit blank-reachability line queries. -/
theorem two_sector_iff_two_feeders (q : Nat) (hq : 1≤q) :
    BB6.Agent1.Reach
      (14*2^(16*q+2)-2*(16*q+2)-16) 3 ↔
    BB6.Agent1.Reach (4*u2 q-4) (4*u2 q+9) ∨
    BB6.Agent1.Reach (6*u2 q-2) (2*u2 q+5) := by
  rw [root_index_two q hq]
  obtain ⟨hu,hodd,_⟩ := u2_properties q hq
  exact root_reach_iff_two_feeders (u2 q) hodd hu

#print axioms two_sector_iff_two_feeders
#print axioms two_sector_requires_two_feeders
end BB6.Agent45TwoRoot
