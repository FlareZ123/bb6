import Std

/-!
  Agent 40, 7 November 2026.
  Lean 4.36.0-rc2 standalone arithmetic model of the forced Sheep generic
  first-even return on all positive x congruent to 14 modulo 16.

  The exact genuine Sheep first-even formula here is forced(x)=(5*x+2)/4.
  The main theorem excludes a natural starting value whose ENTIRE forced
  orbit stays in the residue14 class. No original six-state machine sources
  are imported, and this does not decide the authentic blank-origin orbit.
-/

namespace SheepNoncompact

def forced (x : Nat) : Nat := (5*x+2)/4

theorem forced_identity (x : Nat) (hx : 16 ∣ x+2) :
    4*(forced x+2) = 5*(x+2) := by
  dsimp [forced]
  obtain ⟨k,hk⟩ := hx
  omega

theorem forced_cong (x : Nat) (hx : 64 ∣ x+2) :
    16 ∣ forced x + 2 := by
  have h16 : 16 ∣ x+2 := Nat.dvd_trans (by decide : 16 ∣ 64) hx
  have hident := forced_identity x h16
  obtain ⟨k,hk⟩ := hx
  refine ⟨5*k, ?_⟩
  omega

def orbit (x : Nat) : Nat → Nat
  | 0 => x
  | n+1 => forced (orbit x n)

theorem orbit_identity (x : Nat) (h : ∀ n : Nat, 16 ∣ orbit x n + 2)
    (n : Nat) : 4^n * (orbit x n + 2) = 5^n * (x+2) := by
  induction n with
  | zero => simp [orbit]
  | succ n ih =>
    have hs : 4*(orbit x (n+1)+2)=5*(orbit x n+2) := by
      simpa [orbit] using forced_identity (orbit x n) (h n)
    calc
      4^(n+1)*(orbit x (n+1)+2)
          = 4^n * (4*(orbit x (n+1)+2)) := by
              rw [show n+1 = n.succ by omega, Nat.pow_succ]
              ac_rfl
      _ = 4^n * (5*(orbit x n+2)) := by rw [hs]
      _ = 5*(5^n*(x+2)) := by
            calc
              4^n * (5*(orbit x n+2))
                  = 5*(4^n*(orbit x n+2)) := by ac_rfl
              _ = 5*(5^n*(x+2)) := by rw [ih]
      _ = 5^(n+1)*(x+2) := by
            rw [show n+1 = n.succ by omega, Nat.pow_succ]
            ac_rfl

theorem no_positive_infinite_selfloop (x : Nat)
    (h : ∀ n : Nat, 16 ∣ orbit x n + 2) : False := by
  let n := x+3
  have eqn := orbit_identity x h n
  have hd : 4^n ∣ 5^n*(x+2) := by
    refine ⟨orbit x n+2, ?_⟩
    exact eqn.symm
  have cop : Nat.Coprime (4^n) (5^n) :=
    Nat.Coprime.pow n n (by decide : Nat.Coprime 4 5)
  have hd2 : 4^n ∣ x+2 := Nat.Coprime.dvd_of_dvd_mul_left cop hd
  have he : 4^n ≤ x+2 := Nat.le_of_dvd (by omega) hd2
  have hl : n < 4^n := Nat.lt_pow_self (by decide : 1 < (4:Nat))
  dsimp [n] at he hl
  omega

#print axioms forced_identity
#print axioms forced_cong
#print axioms orbit_identity
#print axioms no_positive_infinite_selfloop

end SheepNoncompact
