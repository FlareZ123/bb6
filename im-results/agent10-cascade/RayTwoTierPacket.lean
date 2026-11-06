import RayTwoTierSelector
set_option maxHeartbeats 0
namespace CascadeRayTwoTierPacket
open CascadeOddRay CascadeFiveForced CascadeRayTwoTierSelector CascadeSweep

private theorem deficit_step (n j:Nat):deficit n j≤deficit n (j+1):=by
  change deficit n j≤2*deficit n j+(n-1)
  omega

private theorem deficit_shift (n j i:Nat):
  deficit n j≤deficit n (j+i):=by
  induction i with
  | zero=>simp
  | succ i ih=>
    have hh:=deficit_step n (j+i)
    have he:j+(i+1)=(j+i)+1:=by omega
    rw[he]
    omega

/-- Source-exact lossless six-packet selection in the high-margin part
    of the #746 canonical even ray. Every possible rooted odd fork at
    the one permissible even position has valuation >=2 or satisfies
    the two proved exceptional congruence gates. -/
theorem exact_two_tier_packet_root_reduction (n j:Nat) (hn:20≤n)
  (hsector:n%6=4 ∨ n%6=5) (hpar:j%2=0)
  (hm:2048*deficit n (j+5)+16384*n+16384≤2^n):
  rootedAt n j ↔ rootedAt n (j+6) ∨
    ∃(q k t d:Nat), ReachC (2,0) (q,0) ∧
      (d%2=1 ∧
        (6*2^k+1≤2^t*d ∧ 2^t*d≤8*2^k-1) ∧
        2*ray n (j+packetForkOffset n j)+5=3^(t+1)*d ∧
        2*(2^t*d)=8*2^k+q+k+5) ∧
      (2≤t ∨ (t=1 ∧
        ((2*q+5)%27=0 ∨
         (2*(2*q-(2*2^n+(n-2)))+5)%27=0))) :=by
  have hband:deficit n (j+5)≤2^n:=by omega
  have hoff:packetForkOffset n j≤4:=by
    unfold packetForkOffset
    split
    · omega
    · split <;> omega
  have hdef:deficit n (j+packetForkOffset n j)≤deficit n (j+5):=by
    have hh:=deficit_shift n (j+packetForkOffset n j) (5-packetForkOffset n j)
    have he:(j+packetForkOffset n j)+(5-packetForkOffset n j)=j+5:=by omega
    rw[he] at hh
    exact hh
  have hmroot:2048*deficit n (j+packetForkOffset n j)+16384*n+16384≤2^n:=by omega
  have hpacket:=exact_six_packet_selected n j (by omega) hsector hpar hband
  have hodd:=exact_odd_fork_two_tier_gate n (j+packetForkOffset n j)
    hn hsector hmroot
  exact hpacket.trans (or_congr Iff.rfl hodd)

#print axioms exact_two_tier_packet_root_reduction
end CascadeRayTwoTierPacket
