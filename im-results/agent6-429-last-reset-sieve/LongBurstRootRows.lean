import OddOddRootRows
import Lean.Elab.Tactic.Omega

namespace BB429LastResetOddRows
open BB429NewResidue

private theorem pow_lower_18 (n : Nat) (hn : 18≤n) : 3*n+77 ≤ 2^(n+2) := by
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
          have he : 20+(k+1) = (20+k)+1 := by omega
          rw [he, Nat.pow_succ]
  have he : 18+k+2 = 20+k := by omega
  rw [he]
  exact h k

private theorem branch9_reduced_equation (n d x : Nat)
    (hn : 18≤n)
    (hx : 4*x+3*n+25 = 2^(n+2)*(d+10)+2*d) :
    4*x+3*n+25 = 64*(2^(n-4)*(d+10))+2*d := by
  have hexp : n+2=6+(n-4) := by omega
  have hpow : 2^(n+2)=64*2^(n-4) := by
    rw [hexp, Nat.pow_add]
  calc
    4*x+3*n+25 = 2^(n+2)*(d+10)+2*d := hx
    _ = (64*2^(n-4))*(d+10)+2*d := by rw [hpow]
    _ = 64*(2^(n-4)*(d+10))+2*d := by simp [Nat.mul_assoc]

private theorem branch10_reduced_equation (n d x : Nat)
    (hn : 18≤n)
    (hx : 4*x+3*n+21 = 2^(n+2)*(d+6)+2*d) :
    4*x+3*n+21 = 64*(2^(n-4)*(d+6))+2*d := by
  have hexp : n+2=6+(n-4) := by omega
  have hpow : 2^(n+2)=64*2^(n-4) := by
    rw [hexp, Nat.pow_add]
  calc
    4*x+3*n+21 = 2^(n+2)*(d+6)+2*d := hx
    _ = (64*2^(n-4))*(d+6)+2*d := by rw [hpow]
    _ = 64*(2^(n-4)*(d+6))+2*d := by simp [Nat.mul_assoc]

/-- Four branch-9 infinite d-progressions are impossible from the blank root.
The contradiction uses the new odd/odd row invariant, not a finite cutoff. -/
theorem branch9_bad_d_classes_unreachable (n d x y : Nat)
    (hn : 18≤n) (hd : 4≤d) (hdx : d≤x)
    (hcase :
      (n%32=5 ∧ d%16=10) ∨
      (n%32=13 ∧ d%16=6) ∨
      (n%32=21 ∧ d%16=2) ∨
      (n%32=29 ∧ d%16=14))
    (hx : 4*x+3*n+25 = 2^(n+2)*(d+10)+2*d)
    (hy : y=2*(x-d)+1)
    (hr : Reach x y) : False := by
  have hpow := pow_lower_18 n hn
  have hfac : 14≤d+10 := by omega
  have hbig0 : 14*(3*n+77) ≤ (d+10)*2^(n+2) := Nat.mul_le_mul hfac hpow
  have hbig : 14*(3*n+77) ≤ 2^(n+2)*(d+10) := by simpa [Nat.mul_comm] using hbig0
  have hxlarge : 13≤x := by omega
  let t := 2^(n-4)*(d+10)
  have hxt := branch9_reduced_equation n d x hn hx
  have hxt' : 4*x+3*n+25=64*t+2*d := by simpa [t] using hxt
  have hxcase : x%16=3 ∨ x%16=11 := by
    rcases hcase with ⟨h1,h2⟩ | ⟨h1,h2⟩ | ⟨h1,h2⟩ | ⟨h1,h2⟩ <;> omega
  have hybad : y%8≠7 := by
    rcases hcase with ⟨h1,h2⟩ | ⟨h1,h2⟩ | ⟨h1,h2⟩ | ⟨h1,h2⟩ <;> omega
  have hxodd : x%2=1 := by omega
  have hyodd : y%2=1 := by omega
  have hrows := rooted_odd_odd_rows x y hr hxlarge hxodd hyodd
  rcases hrows with ⟨_,h3,_,_,h11,_⟩
  have hforced : y%8=7 := by
    rcases hxcase with h | h
    · exact h3 h
    · exact h11 h
  omega

/-- Eight branch-10 infinite d-progressions are impossible from the blank root. -/
theorem branch10_bad_d_classes_unreachable (n d x y : Nat)
    (hn : 18≤n) (hd : 3≤d) (hdx : d≤x)
    (hcase :
      (n%32=3 ∧ d%16=5) ∨
      (n%32=7 ∧ d%16=11) ∨
      (n%32=11 ∧ d%16=1) ∨
      (n%32=15 ∧ d%16=7) ∨
      (n%32=19 ∧ d%16=13) ∨
      (n%32=23 ∧ d%16=3) ∨
      (n%32=27 ∧ d%16=9) ∨
      (n%32=31 ∧ d%16=15))
    (hx : 4*x+3*n+21 = 2^(n+2)*(d+6)+2*d)
    (hy : y=2*(x-d)+1)
    (hr : Reach x y) : False := by
  have hpow := pow_lower_18 n hn
  have hfac : 9≤d+6 := by omega
  have hbig0 : 9*(3*n+77) ≤ (d+6)*2^(n+2) := Nat.mul_le_mul hfac hpow
  have hbig : 9*(3*n+77) ≤ 2^(n+2)*(d+6) := by simpa [Nat.mul_comm] using hbig0
  have hxlarge : 13≤x := by omega
  let t := 2^(n-4)*(d+6)
  have hxt := branch10_reduced_equation n d x hn hx
  have hxt' : 4*x+3*n+21=64*t+2*d := by simpa [t] using hxt
  have hxcase : x%16=3 ∨ x%16=11 := by
    rcases hcase with ⟨h1,h2⟩ | ⟨h1,h2⟩ | ⟨h1,h2⟩ | ⟨h1,h2⟩ |
      ⟨h1,h2⟩ | ⟨h1,h2⟩ | ⟨h1,h2⟩ | ⟨h1,h2⟩ <;> omega
  have hybad : y%8≠7 := by
    rcases hcase with ⟨h1,h2⟩ | ⟨h1,h2⟩ | ⟨h1,h2⟩ | ⟨h1,h2⟩ |
      ⟨h1,h2⟩ | ⟨h1,h2⟩ | ⟨h1,h2⟩ | ⟨h1,h2⟩ <;> omega
  have hxodd : x%2=1 := by omega
  have hyodd : y%2=1 := by omega
  have hrows := rooted_odd_odd_rows x y hr hxlarge hxodd hyodd
  rcases hrows with ⟨_,h3,_,_,h11,_⟩
  have hforced : y%8=7 := by
    rcases hxcase with h | h
    · exact h3 h
    · exact h11 h
  omega

/-- Eight individual branch-10 lifts in four classes are excluded by the
row-1 restriction; this is the half-lift refinement beyond the twelve
whole (n mod 32, d mod 16) classes above. -/
theorem branch10_partial_lifts_unreachable (n d x y : Nat)
    (hn : 18≤n) (hd : 3≤d) (hdx : d≤x)
    (hcase :
      (n%64=7 ∧ d%32=23) ∨
      (n%64=39 ∧ d%32=7) ∨
      (n%64=15 ∧ d%32=3) ∨
      (n%64=47 ∧ d%32=19) ∨
      (n%64=23 ∧ d%32=15) ∨
      (n%64=55 ∧ d%32=31) ∨
      (n%64=31 ∧ d%32=27) ∨
      (n%64=63 ∧ d%32=11))
    (hx : 4*x+3*n+21 = 2^(n+2)*(d+6)+2*d)
    (hy : y=2*(x-d)+1)
    (hr : Reach x y) : False := by
  have hpow := pow_lower_18 n hn
  have hfac : 9≤d+6 := by omega
  have hbig0 : 9*(3*n+77) ≤ (d+6)*2^(n+2) := Nat.mul_le_mul hfac hpow
  have hbig : 9*(3*n+77) ≤ 2^(n+2)*(d+6) := by simpa [Nat.mul_comm] using hbig0
  have hxlarge : 13≤x := by omega
  let t := 2^(n-4)*(d+6)
  have hxt := branch10_reduced_equation n d x hn hx
  have hxt' : 4*x+3*n+21=64*t+2*d := by simpa [t] using hxt
  have hxone : x%16=1 := by
    rcases hcase with ⟨h1,h2⟩ | ⟨h1,h2⟩ | ⟨h1,h2⟩ | ⟨h1,h2⟩ |
      ⟨h1,h2⟩ | ⟨h1,h2⟩ | ⟨h1,h2⟩ | ⟨h1,h2⟩ <;> omega
  have hyfive : y%8=5 := by
    rcases hcase with ⟨h1,h2⟩ | ⟨h1,h2⟩ | ⟨h1,h2⟩ | ⟨h1,h2⟩ |
      ⟨h1,h2⟩ | ⟨h1,h2⟩ | ⟨h1,h2⟩ | ⟨h1,h2⟩ <;> omega
  have hxodd : x%2=1 := by omega
  have hyodd : y%2=1 := by omega
  have hrows := rooted_odd_odd_rows x y hr hxlarge hxodd hyodd
  exact (by omega : y%8≠1) (hrows.1 hxone)

#print axioms branch9_bad_d_classes_unreachable
#print axioms branch10_bad_d_classes_unreachable
#print axioms branch10_partial_lifts_unreachable

end BB429LastResetOddRows
