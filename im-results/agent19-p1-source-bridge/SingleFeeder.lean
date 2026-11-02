import FourDepth
import TwoFeeder

namespace BB6.Agent19.SingleFeeder

open BB6.HaltingFunnel (BlankReach T G blank_even_left_invariant blank_even_hub_power)
open BB6.Agent19.P1 (last_predecessor)
open BB6.Agent19.TwoFeeder (odd_positive_predecessor)
open BB6.Agent19.FourDepth (FourShape G_four_preimages)

/-- No power of two vanishes modulo five. -/
theorem pow5 (j:Nat) : (2^j)%5 ≠ 0 := by
  induction j with
  | zero => decide
  | succ j ih =>
    rw [Nat.pow_succ, Nat.mul_mod]
    have hm : (2^j)%5 < 5 := Nat.mod_lt _ (by decide)
    omega

/-- Impossible corridor rank forced by a hypothetical deepest G ancestor. -/
theorem no_power (m j:Nat) : 30*m+10 ≠ 14*2^j := by
  intro heq
  have hp := pow5 j
  have h1 : (14*2^j)%5=0 := by omega
  rw [Nat.mul_mod] at h1
  have hm : (2^j)%5 <5 := Nat.mod_lt _ (by decide)
  omega

theorem G_no_one_K8 (m k:Nat) (hm:0<m) : G k 1 ≠ (32*m+4,3) := by
  intro h
  have hmod : (3+(32*m+4)/2+3)%16=8 := by omega
  obtain ⟨K,hb,hs⟩ := (G_four_preimages (32*m+4) 3 k 1 (by omega) hmod).mp h
  have he:K=8*m := by omega
  subst K
  rcases hs with ⟨hk,hc⟩ | ⟨hc,hk⟩ | ⟨hc,hk⟩ | ⟨hc,hk⟩ <;> omega

/-- Every possible incoming edge must be through the large-G branch. -/
theorem T_to_m_three (m a c:Nat) (hm:0<m)
  (ht:T a c=some (32*m+4,3)) :
  a%2=1 ∧ 4≤c ∧ G (a/2+1) (c-2)=(32*m+4,3) := by
  by_cases h0:c=0
  · subst c; simp [T] at ht
  · by_cases h1:c=1
    · subst c; simp [T] at ht
    · by_cases ha:a%2=0
      · have hbranch : T a c=some (a+3,c-2) := by simp [T,h0,h1,ha]
        obtain ⟨hleft,hright⟩ := Prod.mk.inj (Option.some.inj (hbranch.symm.trans ht))
        omega
      · by_cases h2:c=2
        · subst c; simp [T,h0,h1,ha] at ht
        · by_cases h3:c=3
          · subst c
            have hbranch : T a 3=some (G (a/2) 1) := by simp [T,ha]
            have hh:=Option.some.inj (hbranch.symm.trans ht)
            exact False.elim (G_no_one_K8 m (a/2) hm hh)
          · have hbranch : T a c=some (G (a/2+1) (c-2)) := by
              simp [T,h0,h1,ha,h2,h3]
            have hresult:=Option.some.inj (hbranch.symm.trans ht)
            exact ⟨by omega,by omega,hresult⟩

/-- At all positive multiples m, three of four algebraic P1 G inverse
    branches are forbidden along the genuinely blank-reachable trajectory. -/
theorem only_first_feeder (m:Nat) (hm:0<m)
 (hr:BlankReach (32*m+4) 3) :
 BlankReach (16*m-4) (16*m+9) := by
  obtain ⟨a,c,hr0,ht⟩:=last_predecessor (32*m+4) 3 hr (Or.inr (by decide))
  obtain ⟨haodd,hc4,hG⟩ := T_to_m_three m a c hm ht
  have hmod : (3+(32*m+4)/2+3)%16=8 := by omega
  obtain ⟨K,hb,hs⟩ := (G_four_preimages (32*m+4) 3 (a/2+1) (c-2) (by omega) hmod).mp hG
  have he:K=8*m := by omega
  subst K
  obtain ⟨u,v,hu,heven,haEq,hcEq⟩:= odd_positive_predecessor a c haodd (by omega) hr0
  rcases hs with ⟨hkg,hcg⟩ | ⟨hcG,hkg⟩ | ⟨hcG,hkg⟩ | ⟨hcG,hkg⟩
  · have huEq:u=16*m-4 := by omega
    have hvEq:v=16*m+9 := by omega
    simpa [huEq,hvEq] using hu
  · have huMod:u%4=2 := by omega
    have hi:=blank_even_left_invariant u v hu (by omega) heven
    rcases hi with h | h <;> omega
  · have huMod:u%4=2 := by omega
    have hi:=blank_even_left_invariant u v hu (by omega) heven
    rcases hi with h | h <;> omega
  · have huEq:u=30*m-2 := by omega
    have hvEq:v=2*m+2 := by omega
    obtain ⟨j,hp⟩ := blank_even_hub_power u v hu (by omega) (by omega) heven
    have he:30*m+10=14*2^j := by omega
    exact False.elim (no_power m j he)

/-- The surviving source branch gives an exact two-transition forward path. -/
theorem first_feeder_to_target (m:Nat) (hm:0<m)
    (hr:BlankReach (16*m-4) (16*m+9)) :
    BlankReach (32*m+4) 3 := by
  have h0 : (16*m-4)%2=0 := by omega
  have ht1 : T (16*m-4) (16*m+9) =some (16*m-1,16*m+7) := by
    simp [T,h0]; omega
  have hshape: FourShape (32*m+4) 3 (8*m) (16*m+5) := by
    refine ⟨8*m,by omega, Or.inl ⟨rfl, by omega⟩⟩
  have hmod : (3+(32*m+4)/2+3)%16=8 := by omega
  have hG : G (8*m) (16*m+5) = (32*m+4,3) :=
    (G_four_preimages (32*m+4) 3 (8*m) (16*m+5) (by omega) hmod).mpr hshape
  have ht2 : T (16*m-1) (16*m+7) =some (32*m+4,3) := by
    have hpar:(16*m-1)%2=1 := by omega
    have hk:(16*m-1)/2+1=8*m := by omega
    simpa [T,hpar,hk,hG,show 16*m+7-2=16*m+5 by omega]
  exact BlankReach.next (16*m-1) (16*m+7) (32*m+4) 3
    (BlankReach.next (16*m-4) (16*m+9) (16*m-1) (16*m+7) hr ht1) ht2

/-- An infinite fully classified *single* feeder family. -/
theorem single_feeder_iff (m:Nat) (hm:0<m) :
 BlankReach (32*m+4) 3 ↔ BlankReach (16*m-4) (16*m+9) := by
 constructor
 · exact only_first_feeder m hm
 · exact first_feeder_to_target m hm


theorem high_power_mod32 (n:Nat) (hn:5≤n) : (2^n)%32=0 := by
  have he : n=n-5+5 := by omega
  rw [he,Nat.pow_add]
  simp

theorem pow_bound : ∀ n:Nat, n+1≤2^n := by
  intro n
  induction n with
  | zero => decide
  | succ n ih => rw [Nat.pow_succ]; omega

/-- Every critical target n>=6 congruent 6 modulo 16 is reached iff
    one explicitly indexed two-cell feeder is reached. -/
theorem critical_single_feeder (n:Nat) (hn:6≤n) (hmod:n%16=6) :
    ∃ m:Nat, 0<m ∧
      (BlankReach 2 (14*2^n-2*n-10) ↔
       BlankReach (16*m-4) (16*m+9)) := by
  let b := 14*2^n-2*n-16
  have hp:=high_power_mod32 n (by omega)
  have hb0:=pow_bound n
  have hbBig:36≤b := by dsimp[b];omega
  have hbMod:b%32=4 := by dsimp[b];omega
  let m:=(b-4)/32
  have hm:0<m := by dsimp[m];omega
  have hbVal:b=32*m+4 := by dsimp[m];omega
  refine ⟨m,hm,?_⟩
  have hcriterion:=BB6.Agent19.P1.residual_critical_gateway n (by omega) (by omega)
  have hsingle:=single_feeder_iff m hm
  have hbexpr:14*2^n-2*n-16=32*m+4 := by simpa only [b] using hbVal
  rw [hbexpr] at hcriterion
  exact hcriterion.trans hsingle

#print axioms critical_single_feeder

#print axioms single_feeder_iff
#print axioms only_first_feeder
#print axioms G_no_one_K8
end BB6.Agent19.SingleFeeder
