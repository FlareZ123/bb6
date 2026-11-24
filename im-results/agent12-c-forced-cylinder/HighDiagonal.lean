import ForcedLattice
import Lean.Elab.Tactic.Omega
namespace BB6.Agent12ForcedLattice
open BB6.Agent3

def highX (j : Nat) : Nat := 2*j+3
def highY (j m : Nat) : Nat := 2^(2*m+2)*(j+3)-(j+3*m+5)

private theorem pow_ge (t : Nat) : t+1≤2^(16*t) := by
  induction t with
  | zero => decide
  | succ t ih =>
    rw [show 16*(t+1)=16*t+16 by omega,Nat.pow_add]
    change t+1+1≤2^(16*t)*65536
    omega

private theorem diag_y (t s : Nat) :
    ∃ v, highY (93+8*t+512*s) (6+8*t)=1572748+16*v ∧
      32 ∣ v+10*(t+64*s+2*v) := by
  let j := 93+8*t+512*s
  let m := 6+8*t
  let q := 2^(16*t)
  have hq : t+1≤q := pow_ge t
  have hp : 2^(2*m+2)=16384*q := by
    dsimp [m,q]
    rw [show 2*(6+8*t)+2=14+16*t by omega,Nat.pow_add]
  have hJ : 96≤j+3 := by dsimp [j]; omega
  have hprod : 96*q≤q*(j+3) := by
    simpa only [Nat.mul_comm q 96] using Nat.mul_le_mul_left q hJ
  have hJq : j+3≤q*(j+3) := by
    simpa using Nat.mul_le_mul_right (j+3) (show 1≤q by omega)
  have hs : 1572748+ (j+3*m+5) ≤ 16384*(q*(j+3)) := by
    dsimp [j,m] at *
    omega
  have he : highY j m+(j+3*m+5)=16384*(q*(j+3)) := by
    unfold highY
    rw [hp,Nat.mul_assoc]
    omega
  let w := q*(j+3)
  have hw : 1572748≤highY j m := by omega
  have he' : highY j m +32*t+512*s+116=16384*w := by
    dsimp [j,m,w] at *
    omega
  have h16 : (highY j m-1572748)%16=0 := by omega
  let v := (highY j m-1572748)/16
  refine ⟨v,?_,?_⟩
  · change highY j m=1572748+16*v
    dsimp [v]
    omega
  · have hv : highY j m=1572748+16*v := by dsimp [v]; omega
    apply Nat.dvd_of_mod_eq_zero
    omega

set_option maxRecDepth 100000
set_option maxHeartbeats 0
/-- Exact coupled diagonal exclusion for all natural t,s. -/
theorem high_diagonal (t s : Nat) :
    fullForcedExcluded (highX (93+8*t+512*s)) (highY (93+8*t+512*s) (6+8*t))=true := by
  have hb : fullForcedExcluded 189 1572748=true := by decide +kernel
  have hsig : signature 189 1572748=(32,10) := by decide +kernel
  obtain ⟨v,hy,hv⟩ := diag_y t s
  have hx : highX (93+8*t+512*s)=189+16*(t+64*s) := by unfold highX; omega
  rw [hx,hy]
  apply fullForcedExcluded_lattice _ _ _ _ hb
  unfold admissible
  rw [hsig]
  exact hv

theorem high_diagonal_blank_unreachable (t s time : Nat) :
    BB6.Agent8Section.run BB6.Agent46.secNext time (some (5,1)) ≠
      some (highX (93+8*t+512*s),highY (93+8*t+512*s) (6+8*t)) :=
  fullForcedExcluded_sound _ _ (high_diagonal t s) time

#print axioms high_diagonal
#print axioms high_diagonal_blank_unreachable
end BB6.Agent12ForcedLattice
