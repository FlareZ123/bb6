import BB429NewResidue
import BB429RootEven8
import BB429Even16
import BB429RootOddRows
import BB429RootOddRowsStrong
import Lean.Elab.Tactic.Omega

namespace BB429ResetBoundaryRows

open BB429NewResidue

set_option maxHeartbeats 20000000
set_option maxRecDepth 20000

private theorem reach_even_eight (a b : Nat) (hr : Reach a b)
    (ha : 0<a) (he : a%2=0) : b%8=2 := by
  rcases hr with ⟨n,hn⟩
  exact BB429RootEven8.rooted_positive_even_eight n a b hn ha he

private theorem reach_even_sixteen (a b : Nat) (hr : Reach a b)
    (ha : 0<a) (he : a%2=0) :
    (a%4=0 → b%16=2) ∧ (a%4=2 → b%16=10) := by
  rcases hr with ⟨n,hn⟩
  exact BB429Even16.rooted_even_sixteen n a b hn ha he

/-- For an odd/odd root state with first counter 3 mod 4, the sum
of the counters is 2 mod 8. The second odd inverse alternative is
impossible, and the first predecessor is positive even. -/
theorem odd_odd_three_sum (a b : Nat) (hr : Reach a b)
    (ha : 13≤a) (hao : a%2=1) (hbo : b%2=1) (ha4 : a%4=3) :
    (a+b)%8=2 := by
  rcases odd_back a b ha hao hr with
    ⟨p,q,hp,hpa,hqb⟩ |
    ⟨p,q,hp,hpa,hqb,hb4⟩
  · have hpos : 0<p := by omega
    have heven : p%2=0 := by omega
    have hq8 := reach_even_eight p q hp hpos heven
    omega
  · omega

/-- Necessary odd/odd rows for genuine blank-root states. The rows
1 and 9 use the existing two inverse obstructions; rows 3,7,11,15
follow from the positive-even predecessor invariant. -/
theorem odd_odd_rows (a b : Nat) (hr : Reach a b)
    (ha : 33≤a) (hao : a%2=1) (hbo : b%2=1) :
    (a%16=1 → b%8=1) ∧
    (a%16=3 → b%8=7) ∧
    (a%16=5 → True) ∧
    (a%16=7 → b%8=3) ∧
    (a%16=9 → b%8=1) ∧
    (a%16=11 → b%8=7) ∧
    (a%16=13 → True) ∧
    (a%16=15 → b%8=3) := by
  have hall := reach_allowed a b hr
  unfold BB429Mod8.Allowed at hall
  have hsum : a%4=3 → (a+b)%8=2 := by
    intro h
    exact odd_odd_three_sum a b hr (by omega) hao hbo h
  have hnot15 : a%16=1 → b%8≠5 := by
    intro h
    rcases hr with ⟨n,hn⟩
    exact Agent6RootOddRows.rooted_not_1_5 n a b hn h
  have hnot95 : a%16=9 → b%8≠5 := by
    intro h hbad
    exact BB429RootOddRowsStrong.rooted_not_9_5 a b hr ha h hbad
  constructor
  · intro h
    have hbad := hnot15 h
    rcases hall with h0|h1|h2|h3|h4|h5|h6|h7 <;> omega
  constructor
  · intro h
    have hs := hsum (by omega)
    omega
  constructor
  · intro h
    trivial
  constructor
  · intro h
    have hs := hsum (by omega)
    omega
  constructor
  · intro h
    have hbad := hnot95 h
    rcases hall with h0|h1|h2|h3|h4|h5|h6|h7 <;> omega
  constructor
  · intro h
    have hs := hsum (by omega)
    omega
  constructor
  · intro h
    trivial
  · intro h
    have hs := hsum (by omega)
    omega

/-- All-time root restriction on the branch-4 boundary y=2x-2.
For x>=69, a genuine root state on this line has either x=6 mod 8
when x is even, or x=13 mod 16 when x is odd. -/
theorem rooted_minus_two_filter (a b : Nat) (hr : Reach a b)
    (ha : 69≤a) (hrel : b+2=2*a) :
    (a%2=0 → a%8=6) ∧ (a%2=1 → a%16=13) := by
  constructor
  · intro he
    have hs := reach_even_sixteen a b hr (by omega) he
    by_cases h0 : a%4=0
    · have hb16 := hs.1 h0
      have hcase : a%8=0 ∨ a%8=4 := by omega
      rcases hcase with h|h <;> omega
    · have h2 : a%4=2 := by omega
      have hb16 := hs.2 h2
      have hcase : a%8=2 ∨ a%8=6 := by omega
      rcases hcase with h|h <;> omega
  · intro ho
    have hb4 : b%4=0 := by omega
    rcases odd_back a b (by omega) ho hr with
      ⟨p,q,hp,hpa,hqb⟩ |
      ⟨p,q,hp,hpa,hqb,hb4'⟩
    · by_cases ha3 : a%4=3
      · have hpos : 0<p := by omega
        have heven : p%2=0 := by omega
        have hq8 := reach_even_eight p q hp hpos heven
        omega
      · have ha1 : a%4=1 := by omega
        have hpOdd : p%2=1 := by omega
        have hqOdd : q%2=1 := by omega
        have hrows := odd_odd_rows p q hp (by omega) hpOdd hqOdd
        rcases hrows with ⟨h1,h3,h5,h7,h9,h11,h13,h15⟩
        have hcase : a%16=1 ∨ a%16=5 ∨ a%16=9 ∨ a%16=13 := by omega
        rcases hcase with h|h|h|h
        · have hp8 : p%8=7 := by omega
          have hq8 : q%8=1 := by omega
          have hp16 : p%16=7 ∨ p%16=15 := by omega
          rcases hp16 with hp7|hp15
          · have := h7 hp7
            omega
          · have := h15 hp15
            omega
        · have hp8 : p%8=1 := by omega
          have hq8 : q%8=5 := by omega
          have hp16 : p%16=1 ∨ p%16=9 := by omega
          rcases hp16 with hp1|hp9
          · have := h1 hp1
            omega
          · have := h9 hp9
            omega
        · have hp8 : p%8=3 := by omega
          have hq8 : q%8=1 := by omega
          have hp16 : p%16=3 ∨ p%16=11 := by omega
          rcases hp16 with hp3|hp11
          · have := h3 hp3
            omega
          · have := h11 hp11
            omega
        · omega
    · omega

private theorem pow_lower_18 (n : Nat) (hn : 18 ≤ n) :
    3*n+77 ≤ 2^(n+2) := by
  let k := n-18
  have hnk : n = 18+k := by dsimp [k]; omega
  rw [hnk]
  have h : ∀ k : Nat, 3*(18+k)+77 ≤ 2^(20+k) := by
    intro k
    induction k with
    | zero => decide
    | succ k ih =>
      calc
        3*(18+(k+1))+77 = (3*(18+k)+77)+3 := by omega
        _ ≤ 2^(20+k)+3 := by omega
        _ ≤ 2^(20+k)*2 := by omega
        _ = 2^(20+(k+1)) := by
          have he : 20+(k+1)=(20+k)+1 := by omega
          rw [he, Nat.pow_succ]
  have he : 18+k+2=20+k := by omega
  rw [he]
  exact h k

/-- Branch 4 of the exact last-reset table has u0=0, w0=4x+8,
d=1, and y=2x-2. For n>=18, its root-reachable prestate can
occur only when n=17,49, or 61 mod 64. This removes 13 of the
16 possible n-classes modulo 64 (the branch itself remains open). -/
theorem branch4_long_burst_n_mod64 (n x y : Nat)
    (hn : 18≤n)
    (heq : 4*x+3*n+21=3*2^(n+2))
    (hrel : y+2=2*x)
    (hr : Reach x y) :
    n%64=17 ∨ n%64=49 ∨ n%64=61 := by
  have hp := pow_lower_18 n hn
  have hmul : 9*n+231 ≤ 3*2^(n+2) := Nat.mul_le_mul_left 3 hp
  have hxlarge : 69≤x := by omega
  have hfilter := rooted_minus_two_filter x y hr hxlarge hrel
  have hexp : n+2=6+(n-4) := by omega
  have hpow : 2^(n+2)=64*2^(n-4) := by
    rw [hexp, Nat.pow_add, show (2:Nat)^6=64 by decide]
  have hdiv : 64 ∣ 4*x+3*n+21 := by
    refine ⟨3*2^(n-4), ?_⟩
    rw [heq, hpow]
    simp [Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm]
  by_cases he : x%2=0
  · have hx8 := hfilter.1 he
    have hn32 : n%32=17 := by omega
    omega
  · have ho : x%2=1 := by omega
    have hx16 := hfilter.2 ho
    omega

#print axioms odd_odd_three_sum
#print axioms odd_odd_rows
#print axioms rooted_minus_two_filter
#print axioms branch4_long_burst_n_mod64

end BB429ResetBoundaryRows
