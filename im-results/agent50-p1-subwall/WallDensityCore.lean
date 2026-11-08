import Lean
import Lean.Elab.Tactic.Omega

set_option maxHeartbeats 2000000

namespace BB6.Agent50Density

/-- A source-shape shallow inverse creates a full dyadic wall deficit, provided
the transition cost is bounded and the power dominates the total budget. -/
theorem shallow_mass_gap
    (n P M b d m t k c : Nat)
    (hM : m+t+1 ≤ M)
    (hP : 32*(M+n+6) ≤ P)
    (hmass : b+d+2*m+2*n+13=14*P)
    (hbefore : (b+4*m+4*n+20)+2^(t+1)*(c+3)=28*P)
    (hafter : ((2*k-4)+4*(m+t+1)+4*n+20)+(c+3)=
       14*P+2*(m+n+t+4))
    (ht : t≤1) :
    ((2*k-4)+4*(m+t+1)+4*n+20)+P ≤ 12*P := by
  have hb : b+4*m+4*n+20≤14*P+2*m+2*n+7 := by omega
  have htp : 2^(t+1)≤4 := by
    by_cases hz : t=0
    · simp [hz]
    · have ht1 : t=1 := by omega
      simp [ht1]
  have hcMul : 2^(t+1)*(c+3)≤4*(c+3) :=
    Nat.mul_le_mul_right (c+3) htp
  have hcLower : 14*P≤4*(c+3)+2*m+2*n+7 := by omega
  have hNumeric : 10*m+10*n+8*t+39 ≤ 2*P := by omega
  have hC : 3*P+2*(m+n+t+4) ≤ c+3 := by omega
  omega

/-- The scaled wall buffer survives a genuine depth-two inverse reset. -/
theorem two_buffer_step
    (P A W W' q h : Nat) (hcost : q≤A)
    (hprev : W+32*A*8^(h+1) ≤12*P+16*A)
    (hrec : 8*W'=W+84*P+16*q) :
    W'+32*A*8^h ≤12*P+16*A := by
  rw [Nat.pow_succ] at hprev
  have hmul : 32*A*(8^h*8)=8*(32*A*8^h) := by ac_rfl
  rw [hmul] at hprev
  omega

/-- An exact-wall node is incompatible with a positive low-side buffer. -/
theorem buffer_excludes_wall
    (P A h W : Nat) (hA : 1≤A)
    (hbuffer : W+32*A*8^h ≤12*P+16*A)
    (hwall : W=12*P) : False := by
  have hp : 1≤8^h := Nat.one_le_pow h 8 (by decide)
  have hmul := Nat.mul_le_mul_left (32*A) hp
  omega

#print axioms BB6.Agent50Density.shallow_mass_gap
#print axioms BB6.Agent50Density.two_buffer_step
#print axioms BB6.Agent50Density.buffer_excludes_wall
end BB6.Agent50Density
