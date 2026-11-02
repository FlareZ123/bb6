import Agent3COrbitIff
import ThirdStageOddDepth
import DyadicResidualFourStage
import Lean.Elab.Tactic.Omega

namespace BB6.Agent6
open BB6.Agent3 BB6.Agent46

/-- A full infinite class of genuine blank-reachable a=1 section outputs is
    forbidden. The exact Agent3 one-four inverse feeder has an odd-odd
    modulo-eight/sixteen pattern already forbidden by Agent38. -/
theorem blank_no_one_index_five_mod_eight (t : Nat) :
    ¬ CReach 1 (4*(8*t+5)) := by
  intro h
  have hp := (blank_one_four_iff_feeder (8*t+5) (by omega)).mp h
  rcases hp with ⟨time,hr⟩
  have hn := BB6Agent38.blank_section_no_odd_special time
    (4*(8*t+5)-1) (2*(8*t+5)-1)
    (by omega) (by omega) (by omega) (by omega)
  exact hn hr

private theorem depth48_implies_k20 (depth k : Nat)
    (hd : depth%64=48)
    (hrel : 2*k+3*depth+8=2^(depth+1)*8) :
    k%32=20 := by
  have hp : 8 ∣ 2^(depth+1) := by
    change 2^3 ∣ 2^(depth+1)
    exact Nat.pow_dvd_pow 2 (by omega)
  obtain ⟨t,ht⟩ := hp
  have hdiv : 64 ∣ 2^(depth+1)*8 := by
    refine ⟨t,?_⟩
    rw [ht]
    omega
  have hmod : (2*k+3*depth+8)%64=0 := by
    rw [hrel]
    exact Nat.mod_eq_zero_of_dvd hdiv
  omega

/-- This entire stopping-depth residue class is impossible on Machine C's
    genuine blank run, for all section times and natural target parameters. -/
theorem dyadic_one_depth_fortyeight_mod64_excluded
    (k depth time : Nat)
    (hk : 4≤k)
    (hlevel : 2*k-3=haltLevel 4 depth)
    (hdepth : depth%64=48)
    (hr : BB6.Agent8Section.run secNext time (some (5,1))=some (1,k)) :
    False := by
  have hc := haltLevel_closed 4 depth
  have hrel : 2*k+3*depth+8=2^(depth+1)*8 := by omega
  have hmod := depth48_implies_k20 depth k hdepth hrel
  have heq : k=4*(8*(k/32)+5) := by omega
  have hh : CReach 1 k := ⟨time,hr⟩
  rw [heq] at hh
  exact blank_no_one_index_five_mod_eight (k/32) hh

/-- Refined full blank-origin halting iff, adding a source-verified fifth
    independent necessary condition to the a=1 dyadic basin, without
    changing the odd-a≥3 residual basin. -/
theorem blank_halts_iff_fifth_stage_residual :
    BB6.CReachBridge.RunHalts ↔
      ∃ time a k : Nat,
        BB6.Agent8Section.run secNext time (some (5,1))=some (a,k) ∧
        ((a=1 ∧ 4≤k ∧
            ∃ depth, 2*k-3=haltLevel 4 depth ∧ depth%8≠2 ∧
              depth%16≠8 ∧ depth%64≠48) ∨
         (3≤a ∧ a%2=1 ∧ a<2*k ∧
            ∃ depth, 2*k-a+3=haltLevel (a-1) depth ∧ depth%2=1 ∧
              a%8≠(3*depth)%8 ∧
              (a%4≠1 ∨ (a+3*depth+4)%16≠0) ∧
              (depth<3 ∨ a%4≠3 ∨ (a+depth)%32≠16) ∧
              (depth<3 ∨ a%8≠7 ∨ (a+3*depth)%16≠4))) := by
  rw [BB6Agent38.blank_halts_iff_four_stage_residual]
  constructor
  · rintro ⟨time,a,k,hr,ht⟩
    refine ⟨time,a,k,hr,?_⟩
    rcases ht with ⟨ha,hk,depth,hlevel,h8,h16⟩ | hodd
    · left
      refine ⟨ha,hk,depth,hlevel,h8,h16,?_⟩
      intro h64
      subst a
      exact dyadic_one_depth_fortyeight_mod64_excluded k depth time hk hlevel h64 hr
    · exact Or.inr hodd
  · rintro ⟨time,a,k,hr,ht⟩
    refine ⟨time,a,k,hr,?_⟩
    rcases ht with ⟨ha,hk,depth,hlevel,h8,h16,_⟩ | hodd
    · exact Or.inl ⟨ha,hk,depth,hlevel,h8,h16⟩
    · exact Or.inr hodd

#print axioms blank_no_one_index_five_mod_eight
#print axioms dyadic_one_depth_fortyeight_mod64_excluded
#print axioms blank_halts_iff_fifth_stage_residual

end BB6.Agent6
