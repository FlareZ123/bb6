import ForkDecompose
set_option maxHeartbeats 0
namespace CascadeFiveForced
open CascadeOddRay CascadeRayPeriod CascadeResetInverse

/-- Complete six-node rooted inverse certificate before excluding the two
    arithmetically impossible odd branches. -/
theorem six_packet_all_odd_branches (n j:Nat) (hn:4≤n)
    (hpar:j%2=0) (hband:deficit n (j+5)≤2^n):
    rootedAt n j ↔ rootedAt n (j+6) ∨ oddRootAt n j ∨
      oddRootAt n (j+2) ∨ oddRootAt n (j+4) := by
  have hm0:=deficit_packet_bound n j 0 (by omega) hband
  have hm1:=deficit_packet_bound n j 1 (by omega) hband
  have hm2:=deficit_packet_bound n j 2 (by omega) hband
  have hm3:=deficit_packet_bound n j 3 (by omega) hband
  have hm4:=deficit_packet_bound n j 4 (by omega) hband
  have hm5:=deficit_packet_bound n j 5 (by omega) hband
  have h0:=exact_fork_root_iff n j hn hm0
  have h2:=exact_fork_root_iff n (j+2) hn hm2
  have h4:=exact_fork_root_iff n (j+4) hn hm4
  have h1:=CascadeOddRay.odd_ray_root_iff n (j+1) hn (by omega) (by omega: deficit n (j+1)≤2^n+1)
  have h3:=CascadeOddRay.odd_ray_root_iff n (j+3) hn (by omega) (by omega: deficit n (j+3)≤2^n+1)
  have h5:=CascadeOddRay.odd_ray_root_iff n (j+5) hn (by omega) (by omega: deficit n (j+5)≤2^n+1)
  dsimp [rootedAt,oddRootAt]
  rw [h0,h1,h2,h3,h4,h5]
  simp only [show j+5+1=j+6 by omega, or_assoc, or_left_comm, or_comm]

/-- The unique potential odd-fork position in a high-band six-packet. -/
def packetForkOffset (n j:Nat):Nat :=
  if signedZ n j%9=0 then 0
  else if signedZ n (j+2)%9=0 then 2 else 4

private theorem no_odd_when_nonfork (n j:Nat) (hn:4≤n)
    (hm:deficit n j≤2^n) (hz:signedZ n j%9≠0):
    ¬oddRootAt n j:=by
  rintro ⟨q,hroot,hodd⟩
  exact hz (odd_fork_requires_nine n j q hn hm hodd)

/-- Lossless six-step source-C root reachability, with a computed single
    possible fork index and all its algebraically genuine odd-arm parents. -/
theorem exact_six_packet_selected (n j:Nat) (hn:4≤n)
    (hsector:n%6=4 ∨ n%6=5) (hpar:j%2=0)
    (hband:deficit n (j+5)≤2^n):
    rootedAt n j ↔ rootedAt n (j+6) ∨
      oddRootAt n (j+packetForkOffset n j) := by
  have hthree:=six_packet_all_odd_branches n j hn hpar hband
  have hm0:=deficit_packet_bound n j 0 (by omega) hband
  have hm2:=deficit_packet_bound n j 2 (by omega) hband
  have hm4:=deficit_packet_bound n j 4 (by omega) hband
  have hp:=signed_ray_even_packet_permutation n j hsector hpar
  have case0 (hz:signedZ n j%9=0)
      (h2:signedZ n (j+2)%9≠0) (h4:signedZ n (j+4)%9≠0):
      rootedAt n j ↔ rootedAt n (j+6) ∨
      oddRootAt n (j+packetForkOffset n j):=by
    have no2:=no_odd_when_nonfork n (j+2) hn hm2 h2
    have no4:=no_odd_when_nonfork n (j+4) hn hm4 h4
    have hsel:packetForkOffset n j=0:=by simp [packetForkOffset,hz]
    simpa only [hsel,Nat.add_zero,or_false,no2,no4,or_assoc] using hthree
  have case2 (h0:signedZ n j%9≠0)
      (hz:signedZ n (j+2)%9=0) (h4:signedZ n (j+4)%9≠0):
      rootedAt n j ↔ rootedAt n (j+6) ∨
      oddRootAt n (j+packetForkOffset n j):=by
    have no0:=no_odd_when_nonfork n j hn (by simpa only [Nat.add_zero] using hm0) h0
    have no4:=no_odd_when_nonfork n (j+4) hn hm4 h4
    have hsel:packetForkOffset n j=2:=by simp [packetForkOffset,h0,hz]
    simpa only [hsel,no0,no4,not_false_eq_true,or_false,false_or,or_assoc] using hthree
  have case4 (h0:signedZ n j%9≠0)
      (h2:signedZ n (j+2)%9≠0):
      rootedAt n j ↔ rootedAt n (j+6) ∨
      oddRootAt n (j+packetForkOffset n j):=by
    have no0:=no_odd_when_nonfork n j hn (by simpa only [Nat.add_zero] using hm0) h0
    have no2:=no_odd_when_nonfork n (j+2) hn hm2 h2
    have hsel:packetForkOffset n j=4:=by simp [packetForkOffset,h0,h2]
    simpa only [hsel,no0,no2,not_false_eq_true,or_false,false_or,or_assoc] using hthree
  rcases hp with hp|hp|hp|hp|hp|hp
  · exact case0 hp.1 (by omega) (by omega)
  · exact case0 hp.1 (by omega) (by omega)
  · exact case2 (by omega) hp.2.1 (by omega)
  · exact case4 (by omega) (by omega)
  · exact case2 (by omega) hp.2.1 (by omega)
  · exact case4 (by omega) (by omega)

#print axioms six_packet_all_odd_branches
#print axioms exact_six_packet_selected
end CascadeFiveForced
