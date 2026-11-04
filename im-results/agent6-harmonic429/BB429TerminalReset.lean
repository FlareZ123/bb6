import BB429LastReset
import BB429FirstRunEq
import BB429NonFirstBurst
import BB429PowerBarrierBurst
import Lean.Elab.Tactic.Omega

namespace BB429TerminalReset

theorem zero_seed_burst_gate (w k a b : Nat)
    (hw : w%2=0)
    (hr : BB429Burst.firstRun k (0,w)=some (a,b))
    (hg : b+1=2*a) :
    (k=1 ∧ w=8 ∧ a=3) ∨
    (k=3 ∧ w=74 ∧ a=21) ∨
    (5 ≤ k ∧ k%2=1 ∧ a%32=29) := by
  have he := (BB429Burst.gateway_iff_exponential 0 w k a b hr).mp hg
  have hp := (BB429Burst.prefix_formula 0 w k a b hr).1
  have he' : w+3*k+13=4*(3*2^k) := by simpa using he
  have hp' : a+3=3*2^k := by simpa using hp
  have hodd : k%2=1 := by omega
  by_cases hl : k<5
  · have hcase : k=1 ∨ k=3 := by omega
    rcases hcase with h1 | h3
    · subst k
      simp only [show (2:Nat)^1=2 by decide] at he' hp'
      left
      omega
    · subst k
      simp only [show (2:Nat)^3=8 by decide] at he' hp'
      right
      left
      omega
  · refine Or.inr (Or.inr ?_)
    have hlong : 5≤k := by omega
    exact ⟨hlong,hodd,BB429PowerBarrierBurst.first_run_long_mod32 0 w k a b hr hlong⟩

theorem actual_terminal_reset_shape (n a b : Nat)
    (hreach : BB429.run n (0,0)=some (a,b))
    (hhalt : BB429.next (a,b)=none) :
    ∃ j, ∃ p : BB429.State, ∃ seed : BB429.State, ∃ k,
      BB429.run j (0,0)=some p ∧
      p.2<2*p.1+3 ∧
      BB429.next p=some seed ∧
      BB429Burst.firstRun k seed=some (a,b) ∧
      (seed.1=0 ∨
       (k=1 ∧ seed.1%2=1 ∧ a=2*seed.1+3) ∨
       (k=3 ∧ seed.1%2=0 ∧ a=8*seed.1+21) ∨
       (5≤k ∧ a%32=29)) := by
  obtain ⟨j,p,seed,k,hj,hnot,hnon,hk⟩ :=
    BB429LastReset.halting_has_last_nonfirst n (a,b) hreach hhalt
  obtain ⟨x,y⟩ := p
  obtain ⟨u,w⟩ := seed
  have hr : BB429Burst.firstRun k (u,w)=some (a,b) := by
    rw [← BB429FirstRunEq.source_first_run_eq]
    exact hk
  refine ⟨j,(x,y),(u,w),k,hj,hnot,hnon,hr,?_⟩
  by_cases hz : u=0
  · exact Or.inl hz
  · have hpos : 0<u := by omega
    exact Or.inr (BB429NonFirstBurst.positive_nonfirst_burst_shape
      x y u w k a b hnot hnon hpos hr
      ((BB429.next_none_iff_halt_line a b).mp hhalt))

theorem nine_or_seventeen_terminal_one_step (n a b : Nat)
    (hreach : BB429.run n (0,0)=some (a,b))
    (hhalt : BB429.next (a,b)=none)
    (hres : a%32=9 ∨ a%32=17) :
    ∃ j, ∃ p : BB429.State, ∃ seed : BB429.State,
      BB429.run j (0,0)=some p ∧
      p.2<2*p.1+3 ∧
      BB429.next p=some seed ∧
      BB429Burst.firstRun 1 seed=some (a,b) ∧
      seed.1%2=1 := by
  obtain ⟨j,p,seed,k,hj,hnot,hnon,hr,hshape⟩ :=
    actual_terminal_reset_shape n a b hreach hhalt
  rcases hshape with hz | hshape
  · obtain ⟨x,y⟩ := p
    obtain ⟨u,w⟩ := seed
    have hzero : u=0 := hz
    subst u
    have hw := BB429NonFirstBurst.nonfirst_successor_even x y 0 w hnot hnon
    obtain hclass := zero_seed_burst_gate w k a b hw hr
      ((BB429.next_none_iff_halt_line a b).mp hhalt)
    rcases hclass with ⟨hk,hw8,ha3⟩ | ⟨hk,hw74,ha21⟩ | ⟨hk,_,h29⟩
    · omega
    · omega
    · omega
  · rcases hshape with ⟨hk,hu,ha⟩ | ⟨hk,hu,ha⟩ | ⟨hk,h29⟩
    · subst k
      exact ⟨j,p,seed,hj,hnot,hnon,hr,hu⟩
    · have heq : a%32=5 ∨ a%32=21 := by omega
      omega
    · omega

#print axioms zero_seed_burst_gate
#print axioms actual_terminal_reset_shape
#print axioms nine_or_seventeen_terminal_one_step
end BB429TerminalReset
