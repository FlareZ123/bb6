import BB429Rank
import Lean.Elab.Tactic.Omega

namespace BB429FirstGateRays
open BB429

def grow : Nat → Nat → Nat
  | u, 0 => u
  | u, n+1 => grow (2*u+3) n

def anc : Nat → Nat → Nat
  | u, 0 => 2*u-1
  | u, n+1 => (2*u+3) + anc (2*u+3) n

theorem grow_pos (u n : Nat) (hu : 1 ≤ u) : 1 ≤ grow u n := by
  induction n generalizing u with
  | zero => simpa [grow] using hu
  | succ n ih => exact ih (2*u+3) (by omega)

theorem ray_run (u n : Nat) (hu : 1 ≤ u) :
    BB429.run n (u, anc u n) = some (grow u n, 2*grow u n-1) := by
  induction n generalizing u with
  | zero => rfl
  | succ n ih =>
    have hfirst : BB429.next (u, anc u (n+1)) =
        some (2*u+3, anc (2*u+3) n) := by
      change BB429.next (u, 2*u+3+anc (2*u+3) n) = _
      have hbound : 2*u+3 ≤ 2*u+3+anc (2*u+3) n := by omega
      simp [BB429.next, hbound]
      omega
    have hrest := ih (2*u+3) (by omega)
    calc
      BB429.run (n+1) (u, anc u (n+1)) =
          (BB429.run 1 (u, anc u (n+1))).bind (BB429.run n) := by
            simpa only [Nat.one_add] using (BB429.run_add 1 n (u, anc u (n+1)))
      _ = some (grow u (n+1), 2*grow u (n+1)-1) := by
        change (BB429.next (u, anc u (n+1))).bind (BB429.run n) = _
        rw [hfirst]
        simpa [grow] using hrest

theorem ray_halts (u n : Nat) (hu : 1 ≤ u) :
    BB429.run (n+1) (u, anc u n) = none := by
  have hr := ray_run u n hu
  have hg := grow_pos u n hu
  have hn := (BB429.next_none_iff_halt_line (grow u n) (2*grow u n-1)).mpr (by omega)
  simp only [BB429.run, hr, Option.bind_some, hn]

theorem anc_formula (u n : Nat) (hu : 1 ≤ u) :
    anc u n + 3*n + (2*u+13) = 4*(u+3)*2^n := by
  induction n generalizing u with
  | zero =>
      simp [anc]
      omega
  | succ n ih =>
      have hp : 4*((2*u+3)+3)*2^n = 4*(u+3)*2^(n+1) := by
        have hlin : 2*u+3+3 = 2*(u+3) := by omega
        rw [hlin, Nat.pow_add_one]
        simp only [Nat.mul_assoc]
        simp only [Nat.mul_comm, Nat.mul_assoc]
      have hx := ih (2*u+3) (by omega)
      rw [hp] at hx
      simp only [anc]
      omega

theorem two_pow_ge (n : Nat) : n+1 ≤ 2^n := by
  induction n with
  | zero => decide
  | succ n ih =>
      rw [Nat.pow_add_one]
      omega

def evenK (m : Nat) : Nat := 6*2^(4*(m+1)) - 12 - 3*m
def oddK (m : Nat) : Nat := 14*2^(4*m+1) - 12 - 3*m

theorem evenK_anc (m : Nat) :
    4*(evenK m)+17 = anc 3 (4*(m+1)) := by
  have h := anc_formula 3 (4*(m+1)) (by omega)
  have hp := two_pow_ge (4*(m+1))
  simp only [evenK]
  omega

theorem oddK_anc (m : Nat) :
    4*(oddK m)+10 = anc 11 (4*m+1) := by
  have h := anc_formula 11 (4*m+1) (by omega)
  have hp := two_pow_ge (4*m+1)
  simp only [oddK]
  omega

theorem even_gate_halts (m : Nat) :
    BB429.run (4*(m+1)+1) (3,4*(evenK m)+17) = none := by
  rw [evenK_anc]
  exact ray_halts 3 (4*(m+1)) (by omega)

theorem odd_gate_halts (m : Nat) :
    BB429.run (4*m+2) (11,4*(oddK m)+10) = none := by
  rw [oddK_anc]
  simpa [show 4*m+2=(4*m+1)+1 by omega] using
    (ray_halts 11 (4*m+1) (by omega))


/-- Each parameter family is genuinely infinite: its distinct synthetic
    right-five entry indices grow strictly at every increment. -/
theorem evenK_strict_succ (m : Nat) : evenK m < evenK (m+1) := by
  have hpow : 2^(4*(m+2)) = 16*2^(4*(m+1)) := by
    have he : 4*(m+2) = 4*(m+1)+4 := by omega
    rw [he, Nat.pow_add]
    simp only [show (2:Nat)^4=16 by decide]
    omega
  have hbound := two_pow_ge (4*(m+1))
  dsimp [evenK]
  rw [show 4*(m+1+1)=4*(m+2) by omega, hpow]
  omega

theorem oddK_strict_succ (m : Nat) : oddK m < oddK (m+1) := by
  have hpow : 2^(4*(m+1)+1) = 16*2^(4*m+1) := by
    have he : 4*(m+1)+1 = (4*m+1)+4 := by omega
    rw [he, Nat.pow_add]
    simp only [show (2:Nat)^4=16 by decide]
    omega
  have hbound := two_pow_ge (4*m+1)
  dsimp [oddK]
  rw [hpow]
  omega

#print axioms evenK_strict_succ
#print axioms oddK_strict_succ

#print axioms anc_formula
#print axioms even_gate_halts
#print axioms odd_gate_halts
#print axioms ray_halts
end BB429FirstGateRays
