import BB429GateDepth
import BB429TerminalReset
import BB429LowOddMod8
import Lean.Elab.Tactic.Omega
namespace BB429SurvivingTails
set_option maxHeartbeats 30000000
set_option maxRecDepth 100000

/-- A last non-first transition cannot enter the 61 modulo 64 one-step
halting feeder, if its predecessor belongs to the actual blank orbit. -/
theorem no_nonfirst_61_seed (j z x y : Nat)
    (hr : BB429.run j (0,0)=some (x,y))
    (hn : y<2*x+3)
    (hs : BB429.next (x,y)=some (64*z+61,384*z+374)) : False := by
  have hxy : x=160*z+148 ∧ y=192*z+189 := by
    simp only [BB429.next] at hs
    repeat' (split at hs <;> try contradiction)
    all_goals simp_all [Prod.mk.injEq,Option.some.injEq]
    all_goals omega
  have hm := BB429LowOddMod8.rooted_even_parity j x y hr (by omega) (by omega)
  omega

/-- The non-first predecessor of the 893-mod1024 seven-first-step seed
would be an even positive counter with an odd second counter. -/
theorem no_nonfirst_893_seven (j t x y : Nat)
    (hr : BB429.run j (0,0)=some (x,y))
    (hn : y<2*x+3)
    (hs : BB429.next (x,y)=some (8*t+4,4080*t+3542)) : False := by
  have hxy : x=1028*t+886 ∧ y=2040*t+1771 := by
    simp only [BB429.next] at hs
    repeat' (split at hs <;> try contradiction)
    all_goals simp_all [Prod.mk.injEq,Option.some.injEq]
    all_goals omega
  have hm := BB429LowOddMod8.rooted_even_parity j x y hr (by omega) (by omega)
  omega

/-- Derive the exact genuine-last-reset data from any real accelerated halt. -/
private theorem authentic_last_reset (n a b : Nat)
    (hr : BB429.run n (0,0)=some (a,b)) (hg : b+1=2*a) :
    ∃ j, ∃ p : BB429.State, ∃ seed : BB429.State, ∃ k,
       BB429.run j (0,0)=some p ∧ p.2<2*p.1+3 ∧
       BB429.next p=some seed ∧
       BB429Burst.firstRun k seed=some (a,b) := by
  obtain ⟨j,p,seed,k,hj,hn,hs,hf⟩ := BB429LastReset.halting_has_last_nonfirst
    n (a,b) hr ((BB429.next_none_iff_halt_line a b).mpr hg)
  refine ⟨j,p,seed,k,hj,hn,hs,?_⟩
  rw [← BB429FirstRunEq.source_first_run_eq]
  exact hf

/-- Source-compatible k classification plus the actual-root predecessor filter.
Every real 765(mod1024) terminal would follow exactly five first transitions
from an explicit non-first successor family. -/
theorem last_reset_765 (n a b : Nat)
    (hr : BB429.run n (0,0)=some (a,b))
    (hg : b+1=2*a) (hm : a%1024=765) :
    ∃ t j, ∃ p : BB429.State,
      a=1024*t+765 ∧
      BB429.run j (0,0)=some p ∧ p.2<2*p.1+3 ∧
      BB429.next p=some (32*t+21,4032*t+3002) ∧
      BB429Burst.firstRun 5 (32*t+21,4032*t+3002)=some (a,b) := by
  obtain ⟨j,p,seed,k,hj,hn,hs,hf⟩ := authentic_last_reset n a b hr hg
  let t := a/1024
  have ha : a=1024*t+765 := by dsimp [t]; omega
  have hformula := BB429Burst.prefix_formula seed.1 seed.2 k a b hf
  have hpow : (seed.1+3)*2^k=1024*t+768 := by omega
  have hgateway := (BB429Burst.gateway_iff_exponential seed.1 seed.2 k a b hf).mp hg
  have hweven := BB429NonFirstBurst.nonfirst_successor_even p.1 p.2 seed.1 seed.2 hn hs
  have hpar : 0<seed.1 →
       (seed.1%2=1 ∧ k%4=1) ∨ (seed.1%2=0 ∧ k%4=3) := by
    intro hpos
    exact BB429NonFirstBurst.positive_nonfirst_burst_length
       p.1 p.2 seed.1 seed.2 k a b hn hs hpos hf hg
  obtain ⟨_, hk⟩ := GateDepth.nonfirst_765_depths t seed.1 seed.2 k
    hpow hweven hgateway hpar
  rcases hk with h1 | h5
  · subst k
    have he : seed=(64*(8*t+5)+61,384*(8*t+5)+374) := by
      apply Prod.ext <;> dsimp <;> omega
    rw [he] at hs
    exact False.elim (no_nonfirst_61_seed j (8*t+5) p.1 p.2 hj hn hs)
  · subst k
    have he : seed=(32*t+21,4032*t+3002) := by
      apply Prod.ext <;> dsimp <;> omega
    rw [he] at hs hf
    exact ⟨t,j,p,ha,hj,hn,hs,hf⟩

/-- A 893-mod1024 terminal similarly demands exactly five first steps. -/
theorem last_reset_893 (n a b : Nat)
    (hr : BB429.run n (0,0)=some (a,b))
    (hg : b+1=2*a) (hm : a%1024=893) :
    ∃ t j, ∃ p : BB429.State,
      a=1024*t+893 ∧
      BB429.run j (0,0)=some p ∧ p.2<2*p.1+3 ∧
      BB429.next p=some (32*t+25,4032*t+3506) ∧
      BB429Burst.firstRun 5 (32*t+25,4032*t+3506)=some (a,b) := by
  obtain ⟨j,p,seed,k,hj,hn,hs,hf⟩ := authentic_last_reset n a b hr hg
  let t := a/1024
  have ha : a=1024*t+893 := by dsimp [t]; omega
  have hformula := BB429Burst.prefix_formula seed.1 seed.2 k a b hf
  have hpow : (seed.1+3)*2^k=1024*t+896 := by omega
  have hgateway := (BB429Burst.gateway_iff_exponential seed.1 seed.2 k a b hf).mp hg
  have hweven := BB429NonFirstBurst.nonfirst_successor_even p.1 p.2 seed.1 seed.2 hn hs
  have hpar : 0<seed.1 →
       (seed.1%2=1 ∧ k%4=1) ∨ (seed.1%2=0 ∧ k%4=3) := by
    intro hpos
    exact BB429NonFirstBurst.positive_nonfirst_burst_length
       p.1 p.2 seed.1 seed.2 k a b hn hs hpos hf hg
  obtain ⟨_, hk⟩ := GateDepth.nonfirst_893_depths t seed.1 seed.2 k
    hpow hweven hgateway hpar
  rcases hk with h1 | h5 | h7
  · subst k
    have he : seed=(64*(8*t+6)+61,384*(8*t+6)+374) := by
      apply Prod.ext <;> dsimp <;> omega
    rw [he] at hs
    exact False.elim (no_nonfirst_61_seed j (8*t+6) p.1 p.2 hj hn hs)
  · subst k
    have he : seed=(32*t+25,4032*t+3506) := by
      apply Prod.ext <;> dsimp <;> omega
    rw [he] at hs hf
    exact ⟨t,j,p,ha,hj,hn,hs,hf⟩
  · subst k
    have he : seed=(8*t+4,4080*t+3542) := by
      apply Prod.ext <;> dsimp <;> omega
    rw [he] at hs
    exact False.elim (no_nonfirst_893_seven j t p.1 p.2 hj hn hs)

/-- The remaining 637-mod1024 sector has two explicit non-first seed
families: a five-first-step and a seven-first-step alternative. -/
theorem last_reset_637 (n a b : Nat)
    (hr : BB429.run n (0,0)=some (a,b))
    (hg : b+1=2*a) (hm : a%1024=637) :
    ∃ t j, ∃ p : BB429.State,
      a=1024*t+637 ∧
      BB429.run j (0,0)=some p ∧ p.2<2*p.1+3 ∧
      ((BB429.next p=some (32*t+17,4032*t+2498) ∧
        BB429Burst.firstRun 5 (32*t+17,4032*t+2498)=some (a,b)) ∨
       (BB429.next p=some (8*t+2,4080*t+2522) ∧
        BB429Burst.firstRun 7 (8*t+2,4080*t+2522)=some (a,b))) := by
  obtain ⟨j,p,seed,k,hj,hn,hs,hf⟩ := authentic_last_reset n a b hr hg
  let t := a/1024
  have ha : a=1024*t+637 := by dsimp [t]; omega
  have hformula := BB429Burst.prefix_formula seed.1 seed.2 k a b hf
  have hpow : (seed.1+3)*2^k=1024*t+640 := by omega
  have hgateway := (BB429Burst.gateway_iff_exponential seed.1 seed.2 k a b hf).mp hg
  have hweven := BB429NonFirstBurst.nonfirst_successor_even p.1 p.2 seed.1 seed.2 hn hs
  have hpar : 0<seed.1 →
       (seed.1%2=1 ∧ k%4=1) ∨ (seed.1%2=0 ∧ k%4=3) := by
    intro hpos
    exact BB429NonFirstBurst.positive_nonfirst_burst_length
       p.1 p.2 seed.1 seed.2 k a b hn hs hpos hf hg
  obtain ⟨_, hk⟩ := GateDepth.nonfirst_637_depths t seed.1 seed.2 k
    hpow hweven hgateway hpar
  rcases hk with h1 | h5 | h7
  · subst k
    have he : seed=(64*(8*t+4)+61,384*(8*t+4)+374) := by
      apply Prod.ext <;> dsimp <;> omega
    rw [he] at hs
    exact False.elim (no_nonfirst_61_seed j (8*t+4) p.1 p.2 hj hn hs)
  · subst k
    have he : seed=(32*t+17,4032*t+2498) := by
      apply Prod.ext <;> dsimp <;> omega
    rw [he] at hs hf
    exact ⟨t,j,p,ha,hj,hn,Or.inl ⟨hs,hf⟩⟩
  · subst k
    have he : seed=(8*t+2,4080*t+2522) := by
      apply Prod.ext <;> dsimp <;> omega
    rw [he] at hs hf
    exact ⟨t,j,p,ha,hj,hn,Or.inr ⟨hs,hf⟩⟩

#print axioms no_nonfirst_61_seed
#print axioms no_nonfirst_893_seven
#print axioms last_reset_765
#print axioms last_reset_893
#print axioms last_reset_637
end BB429SurvivingTails
