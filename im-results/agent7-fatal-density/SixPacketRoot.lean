import RayNonFork
set_option maxHeartbeats 0
namespace CascadeFiveForced
open CascadeOddRay CascadeRayPeriod CascadeResetInverse

def rootEdge (n j:Nat):Prop:=
  CascadeSweep.ReachC (2,0) (ray n j,0) ↔
  CascadeSweep.ReachC (2,0) (ray n (j+1),0)

private theorem deficit_step_le (n j:Nat):deficit n j≤deficit n (j+1):=by
  simp only[deficit]
  omega

private theorem deficit_shift_le (n j i:Nat):
    deficit n j≤deficit n (j+i):=by
  induction i with
  | zero=>simp
  | succ i ih=>
    have h := deficit_step_le n (j+i)
    have he:j+(i+1)=(j+i)+1:=by omega
    rw[he]
    omega

theorem deficit_packet_bound (n j i:Nat)
    (hi:i≤5) (hm:deficit n (j+5)≤2^n):
    deficit n (j+i)≤2^n:=by
  have h:=deficit_shift_le n (j+i) (5-i)
  have he:(j+i)+(5-i)=j+5:=by omega
  rw[he] at h
  omega

/-- On a complete high-band six-packet, five authentic reset-root equivalences
    hold. The sole possible exception is an even depth 0, 2 or 4. -/
theorem five_of_six_root_edges (n j:Nat) (hn:4≤n)
    (hsector:n%6=4 ∨ n%6=5) (hpar:j%2=0)
    (hband:deficit n (j+5)≤2^n):
    (rootEdge n (j+1) ∧ rootEdge n (j+2) ∧ rootEdge n (j+3) ∧
      rootEdge n (j+4) ∧ rootEdge n (j+5)) ∨
    (rootEdge n j ∧ rootEdge n (j+1) ∧ rootEdge n (j+3) ∧
      rootEdge n (j+4) ∧ rootEdge n (j+5)) ∨
    (rootEdge n j ∧ rootEdge n (j+1) ∧ rootEdge n (j+2) ∧
      rootEdge n (j+3) ∧ rootEdge n (j+5)) := by
  have hm0:=deficit_packet_bound n j 0 (by omega) hband
  have hm1:=deficit_packet_bound n j 1 (by omega) hband
  have hm2:=deficit_packet_bound n j 2 (by omega) hband
  have hm3:=deficit_packet_bound n j 3 (by omega) hband
  have hm4:=deficit_packet_bound n j 4 (by omega) hband
  have hm5:=deficit_packet_bound n j 5 (by omega) hband
  have h1:rootEdge n (j+1):=by
    exact CascadeOddRay.odd_ray_root_iff n (j+1) hn (by omega) (by omega)
  have h3:rootEdge n (j+3):=by
    exact CascadeOddRay.odd_ray_root_iff n (j+3) hn (by omega) (by omega)
  have h5:rootEdge n (j+5):=by
    exact CascadeOddRay.odd_ray_root_iff n (j+5) hn (by omega) (by omega)
  have h0 (hz:signedZ n j%9≠0):rootEdge n j:=
    nonfork_root_iff n j hn hm0 hz
  have h2 (hz:signedZ n (j+2)%9≠0):rootEdge n (j+2):=
    nonfork_root_iff n (j+2) hn hm2 hz
  have h4 (hz:signedZ n (j+4)%9≠0):rootEdge n (j+4):=
    nonfork_root_iff n (j+4) hn hm4 hz
  have hp:=signed_ray_even_packet_permutation n j hsector hpar
  rcases hp with hp|hp|hp|hp|hp|hp
  · exact Or.inl ⟨h1,h2 (by omega),h3,h4 (by omega),h5⟩
  · exact Or.inl ⟨h1,h2 (by omega),h3,h4 (by omega),h5⟩
  · exact Or.inr (Or.inl ⟨h0 (by omega),h1,h3,h4 (by omega),h5⟩)
  · exact Or.inr (Or.inr ⟨h0 (by omega),h1,h2 (by omega),h3,h5⟩)
  · exact Or.inr (Or.inl ⟨h0 (by omega),h1,h3,h4 (by omega),h5⟩)
  · exact Or.inr (Or.inr ⟨h0 (by omega),h1,h2 (by omega),h3,h5⟩)

#print axioms five_of_six_root_edges
end CascadeFiveForced
