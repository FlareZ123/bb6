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

end BB429LastResetRow95
