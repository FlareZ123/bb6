import RayTThreeTwoGate
import RayTwoTierTThreeSelector
set_option maxHeartbeats 0
namespace CascadeTThreeDoubleSelector
open CascadeResetInverse CascadeSweep CascadeOddRay CascadeFiveForced
open CascadeTThreeLow CascadeRayTThreeSelector

/-- Lossless authentic blank-root classification: at each high-margin
    ray node, the t=3 odd arm needs both its q mod-three gate and either
    3-adic valuation >=4 at q, or high 3-adic valuation at every exact
    physical t=0 reset predecessor of q. The quantifier retains all
    genuine source predecessors without an arbitrary finite cutoff. -/
theorem exact_odd_root_tthree_two_gate (n j:Nat) (hn:20≤n)
 (hsector:n%6=4 ∨ n%6=5)
 (hm:2048*deficit n j+16384*n+16384≤2^n):
 oddRootAt n j ↔
   ∃(q k t d:Nat), ReachC (2,0) (q,0) ∧
     (d%2=1 ∧
       (6*2^k+1≤2^t*d ∧ 2^t*d≤8*2^k-1) ∧
       2*ray n j+5=3^(t+1)*d ∧
       2*(2^t*d)=8*2^k+q+k+5) ∧
     (4≤t ∨ (t=3 ∧ q%3=2 ∧
       ((2*q+5)%81=0 ∨
        ∀ (d0 h:Nat), 3*d0=2*q+5 →
         2*d0=8*2^(n-4)+h+(n-4)+5 → (2*h+5)%9=0)) ∨
       (t=1 ∧ ((2*q+5)%27=0 ∨
        (2*(2*q-(2*2^n+(n-2)))+5)%27=0))) := by
  constructor
  · intro hr
    obtain ⟨q,k,t,d,hroot,⟨hd,hband,hz,heq⟩,hgate⟩:=
      (exact_odd_root_tthree_residue n j hn hsector hm).mp hr
    refine ⟨q,k,t,d,hroot,⟨hd,hband,hz,heq⟩,?_⟩
    rcases hgate with ht|ht|ht
    · exact Or.inl ht
    · right;left
      obtain ⟨ht,hres⟩:=ht
      refine ⟨ht,hres,?_⟩
      have hthree:t=3:=ht
      subst t
      by_cases h81:(2*q+5)%81=0
      · exact Or.inl h81
      · right
        intro d0 h hd0 he0
        by_cases h9 : (2*h+5)%9=0
        · exact h9
        · have hz81:2*ray n j+5=81*d:=by simpa using hz
          have hband8:6*2^k+1≤8*d ∧ 8*d≤8*2^k-1:=by simpa using hband
          have he16:16*d=8*2^k+q+k+5:=by omega
          exact False.elim ((ray_tthree_two_gate_source_dead n j k d q d0 h hn hm
            hz81 hband8 he16 hd0 he0 h81 h9) hroot)
    · exact Or.inr (Or.inr ht)
  · rintro ⟨q,k,t,d,hroot,⟨hd,hband,hz,heq⟩,hgate⟩
    have hweak:(4≤t ∨ (t=3 ∧ q%3=2) ∨ (t=1 ∧
       ((2*q+5)%27=0 ∨
        (2*(2*q-(2*2^n+(n-2)))+5)%27=0))) := by
      rcases hgate with ht|ht|ht
      · exact Or.inl ht
      · exact Or.inr (Or.inl ⟨ht.1,ht.2.1⟩)
      · exact Or.inr (Or.inr ht)
    exact (exact_odd_root_tthree_residue n j hn hsector hm).mpr
      ⟨q,k,t,d,hroot,⟨hd,hband,hz,heq⟩,hweak⟩

#print axioms exact_odd_root_tthree_two_gate
end CascadeTThreeDoubleSelector
