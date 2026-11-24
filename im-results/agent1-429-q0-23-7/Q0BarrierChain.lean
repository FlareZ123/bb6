import Q0FastBarrier

namespace BB429Q0Macro.RankBarrier
open BB429Q0Macro
set_option maxHeartbeats 8000000

def coeffs : List Nat := [4,7,13,23,41]
def upper (a k : Nat) : Nat := (a*16^k-22-6*k)/24
def lower (a k : Nat) : Nat := (a*16^k+12*k+15)/48

theorem interval_guards (a k u : Nat)
    (hroom : 22+6*k≤a*16^k) (hl : lower a k≤u) (hh : u≤upper a k) :
    24*u+22+6*k≤a*16^k ∧ a*16^k+5+12*k≤48*u+37 := by
  unfold lower upper at *
  omega

private theorem scale_room (k : Nat) (hk : 5≤k) : 256*(k+1)≤16^k := by
  induction k with
  | zero => omega
  | succ k ih =>
    by_cases h : 5≤k
    · have h' := ih h
      rw [Nat.pow_succ]
      omega
    · have h' : k=4 := by omega
      subst k
      decide

private theorem base_cover (u : Nat) (hu : 1000000≤u) (hh : u≤upper 41 5) :
    ∃ a, a∈coeffs ∧ 22+6*5≤a*16^5 ∧ lower a 5≤u ∧ u≤upper a 5 := by
  by_cases h : u≤upper 23 5
  · exact ⟨23,by decide,by decide,by unfold lower; omega,h⟩
  · exact ⟨41,by decide,by decide,by unfold upper at h; unfold lower; omega,hh⟩

private theorem next_cover (k u : Nat) (hk : 5≤k)
    (hl : upper 41 k<u) (hh : u≤upper 41 (k+1)) :
    ∃ a, a∈coeffs ∧ 22+6*(k+1)≤a*16^(k+1) ∧
      lower a (k+1)≤u ∧ u≤upper a (k+1) := by
  have hs := scale_room k hk
  by_cases h4 : u≤upper 4 (k+1)
  · refine ⟨4,by decide,?_,?_,h4⟩
    · rw [Nat.pow_succ]; omega
    · unfold upper at hl; unfold lower; rw [Nat.pow_succ]; omega
  by_cases h7 : u≤upper 7 (k+1)
  · refine ⟨7,by decide,?_,?_,h7⟩
    · rw [Nat.pow_succ]; omega
    · unfold upper at h4; unfold lower; rw [Nat.pow_succ] at *; omega
  by_cases h13 : u≤upper 13 (k+1)
  · refine ⟨13,by decide,?_,?_,h13⟩
    · rw [Nat.pow_succ]; omega
    · unfold upper at h7; unfold lower; rw [Nat.pow_succ] at *; omega
  by_cases h23 : u≤upper 23 (k+1)
  · refine ⟨23,by decide,?_,?_,h23⟩
    · rw [Nat.pow_succ]; omega
    · unfold upper at h13; unfold lower; rw [Nat.pow_succ] at *; omega
  · refine ⟨41,by decide,?_,?_,hh⟩
    · rw [Nat.pow_succ]; omega
    · unfold upper at h23; unfold lower; rw [Nat.pow_succ] at *; omega

/-- The five-coefficient chain has no gaps, at every scale >=5.
    This is pure arithmetic; it assumes no numerical barrier results. -/
theorem chain_cover (k u : Nat) (hk : 5≤k) (hu : 1000000≤u)
    (hh : u≤upper 41 k) :
    ∃ a j, a∈coeffs ∧ 5≤j ∧ j≤k ∧
      24*u+22+6*j≤a*16^j ∧ a*16^j+5+12*j≤48*u+37 := by
  induction k with
  | zero => omega
  | succ k ih =>
    by_cases h : 5≤k
    · by_cases hprev : u≤upper 41 k
      · obtain ⟨a,j,ha,hj,hj',h1,h2⟩ := ih h hprev
        exact ⟨a,j,ha,hj,by omega,h1,h2⟩
      · obtain ⟨a,ha,hroom,hlo,hhi⟩ := next_cover k u h (by omega) hh
        obtain ⟨h1,h2⟩ := interval_guards a (k+1) u hroom hlo hhi
        exact ⟨a,k+1,ha,by omega,by omega,h1,h2⟩
    · have he : k+1=5 := by omega
      rw [he] at hh
      obtain ⟨a,ha,hroom,hlo,hhi⟩ := base_cover u hu hh
      obtain ⟨h1,h2⟩ := interval_guards a 5 u hroom hlo hhi
      exact ⟨a,5,ha,by omega,by omega,h1,h2⟩

theorem q0_chain {Reach : Nat→Nat→Prop} (src : Source Reach)
    {k u n x y : Nat} (hk : 5≤k) (hu : 1000000≤u) (hh : u≤upper 41 k)
    (hcert : ∀ a j, a∈coeffs → 5≤j → j≤k → barrierFast a j=true)
    (hn : n=23+32*u) (hx : x+24*u+19=13*2^n) (hy : y+13=2*x) :
    ¬ Reach x y := by
  obtain ⟨a,j,ha,hj,hj',h1,h2⟩ := chain_cover k u hk hu hh
  exact q0_fast_barrier src (hcert a j ha hj hj') h1 h2 hn hx hy

/-- A uniform five-coefficient barrier proof would close every remaining
    q0 parameter above the existing one-million finite certificate. -/
theorem q0_chain_all {Reach : Nat→Nat→Prop} (src : Source Reach)
    {u n x y : Nat} (hu : 1000000≤u)
    (hcert : ∀ a j, a∈coeffs → 5≤j → barrierFast a j=true)
    (hn : n=23+32*u) (hx : x+24*u+19=13*2^n) (hy : y+13=2*x) :
    ¬ Reach x y := by
  let k := u+5
  have hk : 5≤k := by dsimp [k]; omega
  have hs := scale_room k hk
  have hh : u≤upper 41 k := by unfold upper; dsimp [k] at hs ⊢; omega
  exact q0_chain src hk hu hh (fun a j ha hj _ => hcert a j ha hj) hn hx hy

#print axioms chain_cover
#print axioms q0_chain
#print axioms q0_chain_all
end BB429Q0Macro.RankBarrier
