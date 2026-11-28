import Lean.Elab.Tactic.Omega

set_option maxRecDepth 8192
set_option maxHeartbeats 100000000

namespace BB6.Agent37OddDepthAffine

def liftH (h0 s : Nat) : Nat := h0 + 54*s
def liftK (d k0 s : Nat) : Nat := k0 + 3^(d+3)*s
def liftT (d t0 s : Nat) : Nat := t0 + 8^(d+1)*s
def endpoint (n t : Nat) : Nat := 512*t + 8*n + 380

/-- A single reset-factor solution generates an affine family by h -> h+54s. -/
theorem reset_affine (d k0 h0 s : Nat)
    (hbase : 2*k0+1 = 3^d*h0) :
    2*liftK d k0 s+1 = 3^d*liftH h0 s := by
  have h1 : 3^(d+3) = 3^d*27 := by simp [Nat.pow_add]
  have hl : 2*(3^d*27*s) = 54*(3^d*s) := by
    calc
      _ = (2*27)*(3^d*s) := by ac_rfl
      _ = _ := by rfl
  have hr : 3^d*(54*s) = 54*(3^d*s) := by ac_rfl
  simp only [liftK,liftH,h1,Nat.mul_add]
  rw [hl,hr]
  omega

/-- The same +54s perturbation preserves the double-B residue with
    t advancing by 8^(d+1)s. -/
theorem double_B_affine (d t0 h0 s : Nat)
    (hbase : 1+4*8^d*h0 = 27*t0+17) :
    1+4*8^d*liftH h0 s = 27*liftT d t0 s+17 := by
  have h8 : 8^(d+1) = 8^d*8 := by simp [Nat.pow_add]
  have hl : 4*8^d*(54*s) = 216*(8^d*s) := by
    calc
      _ = (4*54)*(8^d*s) := by ac_rfl
      _ = _ := by rfl
  have hr : 27*(8^d*8*s) = 216*(8^d*s) := by
    calc
      _ = (27*8)*(8^d*s) := by ac_rfl
      _ = _ := by rfl
  simp only [liftH,liftT,h8,Nat.mul_add]
  rw [hl,hr]
  omega

/-- For odd depth d=2n+1 the exact regular endpoint is affine in s. -/
theorem endpoint_affine (n t0 s : Nat) :
    endpoint n (liftT (2*n+1) t0 s) =
      endpoint n t0 + (512*8^(2*n+2))*s := by
  have hp : 8^(2*n+1+1)=8^(2*n+2) := by congr 1 <;> omega
  simp only [endpoint,liftT,hp,Nat.mul_add]
  have hm :
      512 * (8 ^ (2 * n + 2) * s) =
        (512 * 8 ^ (2*n+2))*s := by ac_rfl
  rw [hm]
  omega

/-- The endpoint stride is the power of two 2^(3d+12)=2^(6n+15). -/
theorem endpoint_stride_pow (n : Nat) :
    512*8^(2*n+2) = 2^(6*n+15) := by
  have h8 : 8^(2*n+2)=2^(3*(2*n+2)) := by
    calc
      8^(2*n+2) = (2^3)^(2*n+2) := by rfl
      _ = 2^(3*(2*n+2)) := by rw [← Nat.pow_mul]
  rw [h8]
  change 2^9 * 2^(3*(2*n+2)) = 2^(6*n+15)
  rw [← Nat.pow_add]
  congr 1
  omega

#print axioms reset_affine
#print axioms double_B_affine
#print axioms endpoint_affine
#print axioms endpoint_stride_pow

end BB6.Agent37OddDepthAffine
