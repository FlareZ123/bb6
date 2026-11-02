import SecondDeepSector
import Lean.Elab.Tactic.Omega
namespace BB6.Agent15

/-- Every second-family stopping index lies in an exact zero/one-step
inverse sector or the unique parity class with potentially unbounded
2-adic affine inverse depth. The latter satisfies the exact scalar
counter identities for all depths, with no finite cutoff. -/
theorem second_family_depth_partition (j m k : Nat)
    (hk : k+j+3*m+5=2^(2*m+2)*(j+3)) :
   ((j%2=1 ∨ m%2=0 ∨ (j+m)%4=1) ∧
     (affineNormalize (2*j+3) k =
       if h : 4≤k ∧ k%2=0 ∧ (2*j+3+k)%4=1
       then (2*j+3+k-2,(k-2)/2) else (2*j+3,k))) ∨
   (j%2=0 ∧ m%2=1 ∧ (j+m)%4=3 ∧ 1≤oddDepth k ∧
     (let p := affineNormalize (2*j+3) k;
      p.1+2*p.2+4*oddDepth k=2*j+3+2*k ∧
      2^(oddDepth k)*(p.2+2)=k+2)) := by
   by_cases hj : j%2=1
   · exact Or.inl ⟨Or.inl hj,
       second_halt_one_step_outside_deep j m k hk (Or.inl hj)⟩
   · by_cases hm : m%2=0
     · exact Or.inl ⟨Or.inr (Or.inl hm),
         second_halt_one_step_outside_deep j m k hk (Or.inr (Or.inl hm))⟩
     · by_cases hs : (j+m)%4=1
       · exact Or.inl ⟨Or.inr (Or.inr hs),
           second_halt_one_step_outside_deep j m k hk (Or.inr (Or.inr hs))⟩
       · have he : j%2=0 := by omega
         have ho : m%2=1 := by omega
         have h3 : (j+m)%4=3 := by omega
         have hd := second_halt_deep_sector j m k hk he ho h3
         exact Or.inr ⟨he,ho,h3,hd.2.2.1,hd.2.2.2⟩

#print axioms second_family_depth_partition
end BB6.Agent15
