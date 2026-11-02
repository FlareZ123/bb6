import BounceAllExact
import Lean.Elab.Tactic.Omega

namespace BB6.Agent3
open BB6.Agent46

/-- A general elementary exponent cutoff extracted from a power-times-factor
    bound, valid uniformly over all natural arithmetic witnesses. -/
theorem pow_mul_log_bound (n b M : Nat)
    (hb : 1≤b) (hm : 2^n*b≤M) :
    n≤Nat.log2 M := by
  have hp : 2^n≤2^n*b := Nat.le_mul_of_pos_right (2^n) (by omega)
  have hpm : 2^n≤M := by omega
  have hmpos : M≠0 := by
    have pos:=Nat.pow_pos (by decide : 0<2) (n:=n)
    omega
  exact (Nat.le_log2 hmpos).2 hpm

theorem odd_witness_log (K x y n : Nat)
    (hs : x+y=2^n*(2*K+6)) :
    n≤Nat.log2 (x+y+6) := by
  apply pow_mul_log_bound n (2*K+6) (x+y+6) (by omega)
  omega

theorem even_three_witness_log (K x n : Nat)
    (hs : x+6=2^n*(2*K+8)) :
    n≤Nat.log2 (x+9) := by
  apply pow_mul_log_bound n (2*K+8) (x+9) (by omega)
  omega

theorem even_large_witness_log (K x y n : Nat)
    (hs : x+y+1=2^n*(2*K+8)) :
    n≤Nat.log2 (x+y+6) := by
  apply pow_mul_log_bound n (2*K+8) (x+y+6) (by omega)
  omega

/-- Complete original-bounce inverse reduced to a bounded existential:
    any successful output is witnessed by a depth <= log2(x+y+6). -/
def boundedBounce (K c x y : Nat) : Prop :=
  let B := Nat.log2 (x+y+6)
  (K%2=1 ∧ 4≤y ∧ ∃ n : Nat, n≤B ∧
    x+y=2^n*(2*K+6) ∧
    c+(2*K+6)+3*n=x+2*y) ∨
  (K%2=0 ∧
    ((y=3 ∧ ∃ n : Nat, n≤B ∧ x+6=2^n*(2*K+8) ∧
      c+(2*K+8)+3*n=x+10) ∨
     (5≤y ∧ ∃ n : Nat, n≤B ∧ x+y+1=2^n*(2*K+8) ∧
      c+(2*K+8)+3*n=x+2*y+2)))

/-- Every recursively successful original Machine C bounce has a logarithmic
    certificate. Converse: every bounded arithmetic certificate constructs
    the true source bounce, including all depths and the exceptional y=3. -/
theorem bounce_full_log_bounded (K c x y : Nat) :
    (bounce K c).2=some (x,y) ↔ boundedBounce K c x y := by
  rw [bounce_full_exact]
  simp only [boundedBounce]
  constructor
  · rintro (⟨hK,hy,n,hs,hc⟩ | ⟨hK,(⟨hy,n,hs,hc⟩ | ⟨hy,n,hs,hc⟩)⟩)
    · exact Or.inl ⟨hK,hy,n,odd_witness_log K x y n hs,hs,hc⟩
    · right
      refine ⟨hK,Or.inl ⟨hy,n,?_,hs,hc⟩⟩
      have hh := even_three_witness_log K x n hs
      simpa only [hy,show x+3+6=x+9 by omega] using hh
    · exact Or.inr ⟨hK,Or.inr ⟨hy,n,even_large_witness_log K x y n hs,hs,hc⟩⟩
  · rintro (⟨hK,hy,n,_,hs,hc⟩ | ⟨hK,(⟨hy,n,_,hs,hc⟩ | ⟨hy,n,_,hs,hc⟩)⟩)
    · exact Or.inl ⟨hK,hy,n,hs,hc⟩
    · exact Or.inr ⟨hK,Or.inl ⟨hy,n,hs,hc⟩⟩
    · exact Or.inr ⟨hK,Or.inr ⟨hy,n,hs,hc⟩⟩

#print axioms bounce_full_log_bounded
end BB6.Agent3
