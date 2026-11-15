import BB429NewResidue
import BB429RootOddRowsStrong
import Lean.Elab.Tactic.Omega

namespace BB429LastResetRow95

open BB429NewResidue

/-- A simple exponential lower bound valid throughout the long-burst range. -/
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
      have hpos : 0 < (2:Nat)^k := Nat.pow_pos (by decide)
      have hlarge : 3 ≤ 2^(20+k) := by
        rw [Nat.pow_add]
        have hpowpos : 1 ≤ 2^k := by omega
        have hbase : 3 ≤ 2^20 := by decide
        calc
          3 = 3*1 := by omega
          _ ≤ 2^20*2^k := Nat.mul_le_mul hbase hpowpos
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

/-- Rewrite the branch-10 last-reset equation with its 2-adic factor exposed. -/
private theorem branch10_reduced_equation (n d x : Nat)
    (hn : 18 ≤ n)
    (hx : 4*x+3*n+21 = 2^(n+2)*(d+6)+2*d) :
    4*x+3*n+21 = 64*(2^(n-4)*(d+6))+2*d := by
  have hexp : n+2 = 6+(n-4) := by omega
  have hpow : 2^(n+2) = 64*2^(n-4) := by
    rw [hexp, Nat.pow_add]
  calc
    4*x+3*n+21 = 2^(n+2)*(d+6)+2*d := hx
    _ = (64*2^(n-4))*(d+6)+2*d := by rw [hpow]
    _ = 64*(2^(n-4)*(d+6))+2*d := by simp [Nat.mul_assoc]

/--
The eight refined branch-10 lifts with x ≡ 9 (mod 16), y ≡ 5 (mod 8)
are impossible on the authentic blank-root orbit. The only machine-specific
input is the all-time source-root inverse theorem rooted_not_9_5.
-/
theorem branch10_not_9_5_lifts_unreachable (n d x y : Nat)
    (hn : 18 ≤ n) (hd : 3 ≤ d) (hdx : d ≤ x)
    (hcase :
      (n%64=7 ∧ d%32=7) ∨
      (n%64=15 ∧ d%32=19) ∨
      (n%64=23 ∧ d%32=31) ∨
      (n%64=31 ∧ d%32=11) ∨
      (n%64=39 ∧ d%32=23) ∨
      (n%64=47 ∧ d%32=3) ∨
      (n%64=55 ∧ d%32=15) ∨
      (n%64=63 ∧ d%32=27))
    (hx : 4*x+3*n+21 = 2^(n+2)*(d+6)+2*d)
    (hy : y=2*(x-d)+1)
    (hr : Reach x y) : False := by
  have hpow := pow_lower_18 n hn
  have hfac : 9 ≤ d+6 := by omega
  have hbig0 : 9*(3*n+77) ≤ (d+6)*2^(n+2) :=
    Nat.mul_le_mul hfac hpow
  have hbig : 9*(3*n+77) ≤ 2^(n+2)*(d+6) := by
    simpa [Nat.mul_comm] using hbig0
  have hxlarge : 33 ≤ x := by omega
  let t := 2^(n-4)*(d+6)
  have hxt := branch10_reduced_equation n d x hn hx
  have hxt' : 4*x+3*n+21 = 64*t+2*d := by
    simpa [t] using hxt
  have hx9 : x%16=9 := by
    rcases hcase with ⟨h1,h2⟩ | ⟨h1,h2⟩ | ⟨h1,h2⟩ | ⟨h1,h2⟩ |
      ⟨h1,h2⟩ | ⟨h1,h2⟩ | ⟨h1,h2⟩ | ⟨h1,h2⟩ <;> omega
  have hy5 : y%8=5 := by
    rcases hcase with ⟨h1,h2⟩ | ⟨h1,h2⟩ | ⟨h1,h2⟩ | ⟨h1,h2⟩ |
      ⟨h1,h2⟩ | ⟨h1,h2⟩ | ⟨h1,h2⟩ | ⟨h1,h2⟩ <;> omega
  exact BB429RootOddRowsStrong.rooted_not_9_5 x y hr hxlarge hx9 hy5

#print axioms branch10_not_9_5_lifts_unreachable

/-- Expose one more 2-adic bit for the row-13/1 inverse obstruction. -/
private theorem branch10_reduced_equation_128 (n d x : Nat)
    (hn : 18 ≤ n)
    (hx : 4*x+3*n+21 = 2^(n+2)*(d+6)+2*d) :
    4*x+3*n+21 = 128*(2^(n-5)*(d+6))+2*d := by
  have hexp : n+2 = 7+(n-5) := by omega
  have hpow : 2^(n+2) = 128*2^(n-5) := by
    rw [hexp, Nat.pow_add]
  calc
    4*x+3*n+21 = 2^(n+2)*(d+6)+2*d := hx
    _ = (128*2^(n-5))*(d+6)+2*d := by rw [hpow]
    _ = 128*(2^(n-5)*(d+6))+2*d := by simp [Nat.mul_assoc]

/--
Eight additional branch-10 refined lifts force x ≡ 13 (mod 32),
y ≡ 1 (mod 8), which is forbidden by the new two-step root lemma.
-/
theorem branch10_13_1_lifts_unreachable (n d x y : Nat)
    (hn : 18 ≤ n) (hd : 3 ≤ d) (hdx : d ≤ x)
    (hcase :
      (n%128=19 ∧ d%32=1) ∨
      (n%128=27 ∧ d%32=13) ∨
      (n%128=35 ∧ d%32=25) ∨
      (n%128=67 ∧ d%32=9) ∨
      (n%128=75 ∧ d%32=21) ∨
      (n%128=107 ∧ d%32=5) ∨
      (n%128=115 ∧ d%32=17) ∨
      (n%128=123 ∧ d%32=29))
    (hx : 4*x+3*n+21 = 2^(n+2)*(d+6)+2*d)
    (hy : y=2*(x-d)+1)
    (hr : Reach x y) : False := by
  have hpow := pow_lower_18 n hn
  have hfac : 9 ≤ d+6 := by omega
  have hbig0 : 9*(3*n+77) ≤ (d+6)*2^(n+2) :=
    Nat.mul_le_mul hfac hpow
  have hbig : 9*(3*n+77) ≤ 2^(n+2)*(d+6) := by
    simpa [Nat.mul_comm] using hbig0
  have hxlarge : 33 ≤ x := by omega
  let t := 2^(n-5)*(d+6)
  have hxt := branch10_reduced_equation_128 n d x hn hx
  have hxt' : 4*x+3*n+21 = 128*t+2*d := by
    simpa [t] using hxt
  have hx13 : x%32=13 := by
    rcases hcase with ⟨h1,h2⟩ | ⟨h1,h2⟩ | ⟨h1,h2⟩ |
      ⟨h1,h2⟩ | ⟨h1,h2⟩ <;> omega
  have hy1 : y%8=1 := by
    rcases hcase with ⟨h1,h2⟩ | ⟨h1,h2⟩ | ⟨h1,h2⟩ |
      ⟨h1,h2⟩ | ⟨h1,h2⟩ <;> omega
  exact BB429RootOddRowsStrong.rooted_not_13_1 x y hr hxlarge hx13 hy1

#print axioms branch10_13_1_lifts_unreachable

/--
Eight further branch-10 refined lifts force x ≡ 5 (mod 32), y ≡ 1
(mod 8); the three-step inverse obstruction rules them out.
-/
theorem branch10_5_1_lifts_unreachable (n d x y : Nat)
    (hn : 18 ≤ n) (hd : 3 ≤ d) (hdx : d ≤ x)
    (hcase :
      (n%128=3 ∧ d%32=25) ∨
      (n%128=35 ∧ d%32=9) ∨
      (n%128=43 ∧ d%32=21) ∨
      (n%128=75 ∧ d%32=5) ∨
      (n%128=83 ∧ d%32=17) ∨
      (n%128=91 ∧ d%32=29) ∨
      (n%128=115 ∧ d%32=1) ∨
      (n%128=123 ∧ d%32=13))
    (hx : 4*x+3*n+21 = 2^(n+2)*(d+6)+2*d)
    (hy : y=2*(x-d)+1)
    (hr : Reach x y) : False := by
  have hpow := pow_lower_18 n hn
  have hfac : 9 ≤ d+6 := by omega
  have hbig0 : 9*(3*n+77) ≤ (d+6)*2^(n+2) :=
    Nat.mul_le_mul hfac hpow
  have hbig : 9*(3*n+77) ≤ 2^(n+2)*(d+6) := by
    simpa [Nat.mul_comm] using hbig0
  have hxlarge : 61 ≤ x := by omega
  let t := 2^(n-5)*(d+6)
  have hxt := branch10_reduced_equation_128 n d x hn hx
  have hxt' : 4*x+3*n+21 = 128*t+2*d := by
    simpa [t] using hxt
  have hx5 : x%32=5 := by
    rcases hcase with ⟨h1,h2⟩ | ⟨h1,h2⟩ | ⟨h1,h2⟩ |
      ⟨h1,h2⟩ | ⟨h1,h2⟩ | ⟨h1,h2⟩ | ⟨h1,h2⟩ | ⟨h1,h2⟩ <;> omega
  have hy1 : y%8=1 := by
    rcases hcase with ⟨h1,h2⟩ | ⟨h1,h2⟩ | ⟨h1,h2⟩ |
      ⟨h1,h2⟩ | ⟨h1,h2⟩ | ⟨h1,h2⟩ | ⟨h1,h2⟩ | ⟨h1,h2⟩ <;> omega
  exact BB429RootOddRowsStrong.rooted_not_5_1 x y hr hxlarge hx5 hy1

#print axioms branch10_5_1_lifts_unreachable



end BB429LastResetRow95
