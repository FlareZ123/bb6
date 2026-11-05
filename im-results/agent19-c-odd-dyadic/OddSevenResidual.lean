import OddSevenHigh
import OddSpecialResidualLift
import Lean.Elab.Tactic.Omega

namespace BB6.Agent19Seven

/-- Original Machine C halt iff after the root-excluded
    sum-seven-mod8 source family is removed as well. -/
theorem blank_halts_iff_sumseven_sieve :
    BB6.CReachBridge.RunHalts ↔
      ∃ time a k,
        BB6.Agent8Section.run BB6.Agent46.secNext time (some (5,1))=some (a,k) ∧
        ((a=1 ∧ ∃ m, k+3*m+4=2^(2*m+3) ∧
            m%1024≠424 ∧ m%4096≠4008 ∧ m%32768≠30632 ∧
            m%16≠14 ∧ m%64≠38 ∧ m%16384≠5032) ∨
         (∃ j m, a=2*j+3 ∧ k+j+3*m+5=2^(2*m+2)*(j+3) ∧
           ¬ (2≤m ∧ j%4=3 ∧ (j+3*m+7)%16=0) ∧
           ¬ (2≤m ∧ j%4=1 ∧ (j+3*m+11)%32=0) ∧
           (∀ n, ¬ (n+4≤2*m+2 ∧
             (j+3*m+3)%2^(n+4)=2^(n+2) ∧
             (2*j+3)%8=(if n%2=0 then 7 else 3))) ∧
           ¬ (2≤m ∧ j%8=7 ∧ (j+3*m+15)%64=0) ∧
           ¬ (2≤m ∧ j%8=3 ∧ (j+3*m+47)%64=0) ∧
           ¬ (3≤m ∧ j%8=5 ∧ (j+3*m+27)%128=0) ∧
           ¬ (3≤m ∧ j%8=1 ∧ (j+3*m+91)%128=0) ∧
           ¬ (3≤m ∧ j%16=15 ∧ (j+3*m+51)%256=0))) := by
  rw [BB6.Agent19Special.blank_halts_iff_dyadic_special_lift_sieve]
  constructor
  · rintro ⟨time,a,k,hr,hgate⟩
    rcases hgate with hLow | ⟨j,m,ha,heq,h1,h2,hn,h3,h4,h5,h6⟩
    · exact ⟨time,a,k,hr,Or.inl hLow⟩
    · have h7 : ¬ (3≤m ∧ j%16=15 ∧ (j+3*m+51)%256=0) := by
        rintro ⟨hm,hj,hpair⟩
        subst a
        exact blank_no_high_sumseven j m k hm hj hpair heq ⟨time,hr⟩
      exact ⟨time,a,k,hr,Or.inr ⟨j,m,ha,heq,h1,h2,hn,h3,h4,h5,h6,h7⟩⟩
  · rintro ⟨time,a,k,hr,hgate⟩
    rcases hgate with hLow | ⟨j,m,ha,heq,h1,h2,hn,h3,h4,h5,h6,_⟩
    · exact ⟨time,a,k,hr,Or.inl hLow⟩
    · exact ⟨time,a,k,hr,Or.inr ⟨j,m,ha,heq,h1,h2,hn,h3,h4,h5,h6⟩⟩

#print axioms blank_halts_iff_sumseven_sieve
end BB6.Agent19Seven
