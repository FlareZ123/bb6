import PacketSelector
import ManyShield
set_option maxHeartbeats 0
namespace CascadeFatalPacket
open CascadeOddRay CascadeFiveForced CascadeResetInverse

private theorem power_margin (n:Nat) (hn:10≤n):
    63*n+97≤2^n:=by
  have h: ∀k:Nat,63*(k+10)+97≤2^(k+10):=by
    intro k
    induction k with
    | zero=>decide
    | succ k ih=>
      rw [show k+1+10=k+10+1 by omega,Nat.pow_succ]
      omega
  have he:n=(n-10)+10:=by omega
  rw [he]
  exact h (n-10)

/-- Every actual surviving fatal gate n≥10 has a complete first six inverse
    steps within the high even-return band, allowing the exact packet theorem. -/
theorem first_packet_margin (n:Nat) (hn:10≤n):
    deficit n 5≤2^n:=by
  have hc:=deficit_closed n 5 (by omega:1≤n)
  have hp:(2:Nat)^5=32:=by decide
  rw [hp] at hc
  have hm:=power_margin n hn
  omega

/-- The original source fatal index reduces exactly to a depth-six even
    continuation or a root-attached odd predecessor at one computable fork. -/
theorem fatal_gate_one_six (n:Nat) (hn:10≤n)
    (hsector:n%6=4∨n%6=5):
    CascadeSweep.ReachC (2,0) (CascadeManyShield.fatal n,0) ↔
    CascadeSweep.ReachC (2,0) (ray n 6,0) ∨
      ∃q,CascadeSweep.ReachC (2,0) (q,0) ∧
        OddParent q (ray n (packetForkOffset n 0)):=by
  have hp:=exact_six_packet_selected n 0 (by omega) hsector
    (by decide) (by simpa only [Nat.zero_add] using first_packet_margin n hn)
  have hzero:ray n 0=CascadeManyShield.fatal n:=by
    dsimp [ray,deficit,CascadeManyShield.fatal]
    omega
  simpa only [rootedAt,oddRootAt,Nat.zero_add,hzero] using hp

#print axioms first_packet_margin
#print axioms fatal_gate_one_six
end CascadeFatalPacket
