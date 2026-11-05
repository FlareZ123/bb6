import Lean
import Lean.Elab.Tactic.Omega

namespace BB6.Agent19Tower
variable (Reach : Nat → Nat → Prop)
variable (hrev : ∀ x y : Nat, 6 ≤ y → y%2=0 → (x+y)%8≠0 → (x+y)%8≠7 → Reach x y → Reach (x+y-2) ((y-2)/2))
variable (oddNo : ∀ x y : Nat, 5 ≤ y → y%2=1 → (x+y)%4=2 → ¬ Reach x y)

include hrev oddNo in
private theorem base (x w:Nat) (hw:7≤w) (hw4:w%4=3) (hx:x%8=7):
  ¬ Reach x (4*w-2) := by
  intro h
  have h1 : Reach (x+4*w-4) (2*w-2) := by
    have h1a:=hrev x (4*w-2) (by omega) (by omega) (by omega) (by omega) h
    have ex : x + (4*w-2) -2=x+4*w-4 := by omega
    have ey : ((4*w-2)-2)/2=2*w-2 := by omega
    simpa only [ex,ey] using h1a
  have h2 : Reach (x+6*w-8) (w-2) := by
    have h2a:=hrev (x+4*w-4) (2*w-2) (by omega) (by omega) (by omega) (by omega) h1
    have ex : x+4*w-4+(2*w-2)-2=x+6*w-8 := by omega
    have ey : ((2*w-2)-2)/2=w-2 := by omega
    simpa only [ex,ey] using h2a
  exact oddNo (x+6*w-8) (w-2) (by omega) (by omega) (by omega) h2

private theorem pow_mul8 (n w : Nat) : 2^(n+3)*w=8*(2^n*w) := by
  simp [Nat.pow_add, Nat.mul_assoc, Nat.mul_comm]

private theorem pow_mul4 (n w : Nat) : 2^(n+2)*w=4*(2^n*w) := by
  simp [Nat.pow_add, Nat.mul_assoc, Nat.mul_comm]

private theorem positive_factor (n w:Nat) (hw:7≤w) : 7≤2^n*w := by
  have hp: 0<2^n := Nat.pow_pos (by decide)
  have hm:=Nat.mul_le_mul_right w (show 1≤2^n by omega)
  omega

include hrev oddNo in
/-- Uniform variable-depth predecessor obstruction, under exact source hypotheses. -/
theorem tower (n x w:Nat) (hw:7≤w) (hw4:w%4=3)
    (hx:x%8=(if n%2=0 then 7 else 3)) :
    ¬ Reach x (2^(n+2)*w-2) := by
  induction n generalizing x with
  | zero =>
      simpa using base Reach hrev oddNo x w hw hw4 (by simpa using hx)
  | succ n ih =>
      intro h
      let q := 2^n*w
      have hq : 7≤q := positive_factor n w hw
      have hpow8 : 2^(n+1+2)*w=8*q := by
        simpa [q, show n+1+2=n+3 by omega] using pow_mul8 n w
      have hpow4 : 2^(n+2)*w=4*q := by
        simpa [q] using pow_mul4 n w
      have heven : (8*q-2)%2=0 := by omega
      have hmodx : x%8=3 ∨ x%8=7 := by
        by_cases hp : (n+1)%2=0
        · right
          simpa [hp] using hx
        · left
          simpa [hp] using hx
      have h0 : (x+(8*q-2))%8≠0 := by
        rcases hmodx with hh|hh <;> omega
      have h7 : (x+(8*q-2))%8≠7 := by
        rcases hmodx with hh|hh <;> omega
      have h1 : Reach (x+8*q-4) (4*q-2) := by
        have h1a:=hrev x (8*q-2) (by omega) heven h0 h7 (by simpa [hpow8] using h)
        have ex : x + (8*q-2) -2=x+8*q-4 := by omega
        have ey : ((8*q-2)-2)/2=4*q-2 := by omega
        simpa only [ex,ey] using h1a
      have hxnext : (x+8*q-4)%8=(if n%2=0 then 7 else 3) := by
        by_cases hp:n%2=0
        · have hn : (n+1)%2≠0 := by omega
          have hxold : x%8=3 := by simpa [hn] using hx
          have hxnew : (x+8*q-4)%8=7 := by omega
          simpa [hp] using hxnew
        · have hn : (n+1)%2=0 := by omega
          have hxold : x%8=7 := by simpa [hn] using hx
          have hxnew : (x+8*q-4)%8=3 := by omega
          simpa [hp] using hxnew
      exact ih (x+8*q-4) hxnext (by simpa [hpow4] using h1)

end BB6.Agent19Tower

#print axioms BB6.Agent19Tower.tower
