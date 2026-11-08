import Lean.Elab.Tactic.Omega
import PacketSource

namespace BB6.Agent37EChain
open CryptidBoundary BB6.Agent31PacketSource
set_option maxHeartbeats 10000000
set_option maxRecDepth 4096

/-- Exact duration of a single guarded E packet operation. -/
def eTime (k q : Nat) := 12*k*k+49*k+58+6*q

/-- Physical-machine duration of an unbroken chain of d guarded E packets.
    h is the nonzero 3-adic quotient of the unary-prefix index. -/
def chainTime : Nat → Nat → Nat → Nat
  | 0, _, _ => 0
  | d+1, h, q => eTime (4*3^d*h-1) q + chainTime d (8*h) (q+2)

private theorem shift_first (d h : Nat) (hh : 1 ≤ h) :
    1+4*3^(d+1)*h=3*(4*3^d*h-1)+4 := by
  have hp : 1 ≤ 4*3^d*h := by
    have hpow : 0 < 3^d := Nat.pow_pos (by decide)
    have hbig : 0 < 4*3^d*h := Nat.mul_pos (Nat.mul_pos (by decide) hpow) (by omega)
    omega
  calc
    1+4*3^(d+1)*h = 3*(4*3^d*h)+1 := by rw [Nat.pow_succ]; ac_rfl
    _ = 3*(4*3^d*h-1)+4 := by
      have hs : (4*3^d*h-1)+1=4*3^d*h := Nat.sub_add_cancel hp
      omega

private theorem shift_next (d h : Nat) (hh : 1 ≤ h) :
    8*(4*3^d*h-1)+9=1+4*3^d*(8*h) := by
  have hp : 1 ≤ 4*3^d*h := by
    have hpow : 0 < 3^d := Nat.pow_pos (by decide)
    have hbig : 0 < 4*3^d*h := Nat.mul_pos (Nat.mul_pos (by decide) hpow) (by omega)
    omega
  calc
    8*(4*3^d*h-1)+9 = 8*(4*3^d*h)+1 := by
      have hs : (4*3^d*h-1)+1=4*3^d*h := Nat.sub_add_cancel hp
      omega
    _ = 1+4*3^d*(8*h) := by ac_rfl

/-- Universal arbitrary-depth E-only packet chain on the original D six-state
    Turing machine, including exact primitive time and arbitrary untouched tail.
    This is an endpoint theorem for d E source calls. It does not imply a
    blank-origin orbit nor claim minimality of intermediate physical returns. -/
theorem chain_return (d : Nat) : ∀ h q p (ys : List Bool), 1 ≤ h →
    run (chainTime d h q)
      (packet (1+4*3^d*h) q (3*d+p) ys) =
      packet (1+4*8^d*h) (q+2*d) p ys := by
  induction d with
  | zero =>
    intro h q p ys hh
    simp [chainTime, CryptidBoundary.run]
  | succ d ih =>
    intro h q p ys hh
    change run (eTime (4*3^d*h-1) q + chainTime d (8*h) (q+2))
       (packet (1+4*3^(d+1)*h) q (3*(d+1)+p) ys) =
      packet (1+4*8^(d+1)*h) (q+2*(d+1)) p ys
    rw [run_add, shift_first d h hh]
    have hp : 3*(d+1)+p=(3*d+p)+3 := by omega
    rw [hp]
    change run (chainTime d (8*h) (q+2))
      (run (12*(4*3^d*h-1)*(4*3^d*h-1)+49*(4*3^d*h-1)+58+6*q)
       (packet (3*(4*3^d*h-1)+4) q ((3*d+p)+3) ys)) = _
    rw [e_packet, shift_next d h hh]
    have h8 : 1 ≤ 8*h := by omega
    rw [ih (8*h) (q+2) p ys h8]
    have ha : 1+4*8^d*(8*h)=1+4*8^(d+1)*h := by
      rw [Nat.pow_succ]
      ac_rfl
    have hq : (q+2)+2*d=q+2*(d+1) := by omega
    rw [ha,hq]

#print axioms chain_return
end BB6.Agent37EChain
