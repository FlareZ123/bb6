import OddResetSmall

namespace BB429Q0Macro
set_option maxHeartbeats 4000000

/-- The previously studied q0 barriers also cover all paths with
    initial rank p=3*m+C, 0≤C≤14. -/
def barrierCoeffs : List Nat := [4,7,13,23,41]

private theorem pow_room (k : Nat) (hk : 5≤k) : 256*(k+1)≤16^k := by
  induction k with
  | zero => omega
  | succ k ih =>
    by_cases hk' : 5≤k
    · have h := ih hk'
      rw [Nat.pow_succ]
      omega
    · have h : k=4 := by omega
      subst k
      decide

private theorem choose_barrier (k p : Nat) (hk : 5≤k)
    (hlo : 4*16^k+19+12*k≤2*p) (hhi : p+6*k≤41*16^k) :
    ∃ a ∈ barrierCoeffs, p+6*k≤a*16^k ∧ a*16^k+19+12*k≤2*p := by
  have hroom := pow_room k hk
  by_cases h4 : p+6*k≤4*16^k
  · exact ⟨4,by decide,h4,hlo⟩
  by_cases h7 : p+6*k≤7*16^k
  · exact ⟨7,by decide,h7,by omega⟩
  by_cases h13 : p+6*k≤13*16^k
  · exact ⟨13,by decide,h13,by omega⟩
  by_cases h23 : p+6*k≤23*16^k
  · exact ⟨23,by decide,h23,by omega⟩
  exact ⟨41,by decide,hhi,by omega⟩

/-- No gaps between successive barriers, including across radix scales. -/
theorem barrier_cover_rank (K p : Nat) (hK : 5≤K)
    (hlo : 2100000≤p) (hhi : p+6*K≤41*16^K) :
    ∃ k a, 5≤k ∧ k≤K ∧ a∈barrierCoeffs ∧
      p+6*k≤a*16^k ∧ a*16^k+19+12*k≤2*p := by
  induction K with
  | zero => omega
  | succ K ih =>
    by_cases hK' : 5≤K
    · by_cases hprev : p+6*K≤41*16^K
      · obtain ⟨k,a,hk,hkK,ha,h1,h2⟩ := ih hK' hprev
        exact ⟨k,a,hk,by omega,ha,h1,h2⟩
      · have hroom := pow_room K hK'
        have hnew : 4*16^(K+1)+19+12*(K+1)≤2*p := by
          rw [Nat.pow_succ]
          omega
        obtain ⟨a,ha,h1,h2⟩ := choose_barrier (K+1) p hK hnew hhi
        exact ⟨K+1,a,hK,by omega,ha,h1,h2⟩
    · have hK4 : K=4 := by omega
      subst K
      obtain ⟨a,ha,h1,h2⟩ := choose_barrier 5 p (by decide) (by omega) hhi
      exact ⟨5,a,by decide,by decide,ha,h1,h2⟩

/-- A barrier interface with the exact hypotheses of the shared Cross2
    soundness theorem; no assumption of uniform barrier validity. -/
def RankBarrierValid (a k : Nat) : Prop :=
  ∀ m p y, 0<y → 3*y<p → p+6*k≤a*16^k →
    a*16^k+5+12*k≤p+3*m → ¬Path m p y

theorem bounded_rank_path_excluded (K m p y : Nat) (hK : 5≤K)
    (hlo : 2100000≤p) (hhi : p+6*K≤41*16^K)
    (hC : p≤3*m+14) (hy : 0<y) (hc : 3*y<p)
    (hbar : ∀ k a, 5≤k → k≤K → a∈barrierCoeffs → RankBarrierValid a k) :
    ¬ Path m p y := by
  obtain ⟨k,a,hk,hkK,ha,h1,h2⟩ := barrier_cover_rank K p hK hlo hhi
  exact hbar k a hk hkK ha m p y hy hc h1 (by omega)

theorem odd_rayFF_bounded (K t : Nat) (hK : 5≤K)
    (hhi : 53+48*t+6*K≤41*16^K)
    (hbar : ∀ k a, 5≤k → k≤K → a∈barrierCoeffs → RankBarrierValid a k) :
    ¬ Path (13+16*t) (53+48*t) (3+3*t) := by
  by_cases ht : t<43750
  · exact rayFF_small t ht
  · exact bounded_rank_path_excluded K _ _ _ hK (by omega) hhi
      (by omega) (by omega) (by omega) hbar

theorem odd_rayFE_bounded (K t : Nat) (hK : 5≤K)
    (hhi : 36+48*t+6*K≤41*16^K)
    (hbar : ∀ k a, 5≤k → k≤K → a∈barrierCoeffs → RankBarrierValid a k) :
    ¬ Path (8+16*t) (36+48*t) (11+15*t) := by
  by_cases ht : t<43750
  · exact rayFE_small t ht
  · exact bounded_rank_path_excluded K _ _ _ hK (by omega) hhi
      (by omega) (by omega) (by omega) hbar

/-- For either odd-reset ray, p=(3*n+23)/4 or (3*n+27)/4.
    The convenient common bound below is sufficient for both. -/
theorem odd_reset_bounded (src : Source Reach) (K n a b : Nat)
    (hK : 5≤K) (hn : 18≤n) (ho : a%2=1) (hb : b+3=2*a)
    (heq : 4*a+3*n+15=3*2^(n+2))
    (hhi : 3*n+27+24*K≤164*16^K)
    (hbar : ∀ k c, 5≤k → k≤K → c∈barrierCoeffs → RankBarrierValid c k) :
    ¬ Reach a b := by
  intro hr
  rcases odd_reset_forces_path src n a b hn ho hb heq hr with
    ⟨t,ht,hp⟩ | ⟨t,ht,hp⟩
  · exact odd_rayFF_bounded K t hK (by omega) hbar hp
  · exact odd_rayFE_bounded K t hK (by omega) hbar hp

/-- The all-scale barrier conjecture closes the entire long odd-reset
    branch, rather than only the q0 ray for which it was formulated. -/
theorem odd_reset_of_all_barriers (src : Source Reach) (n a b : Nat)
    (hn : 18≤n) (ho : a%2=1) (hb : b+3=2*a)
    (heq : 4*a+3*n+15=3*2^(n+2))
    (hbar : ∀ k c, 5≤k → c∈barrierCoeffs → RankBarrierValid c k) :
    ¬ Reach a b := by
  let K := n+5
  have hK : 5≤K := by dsimp [K]; omega
  have hroom := pow_room K hK
  exact odd_reset_bounded src K n a b hK hn ho hb heq
    (by dsimp [K] at *; omega) (fun k c hk _ hc => hbar k c hk hc)

#print axioms barrier_cover_rank
#print axioms odd_reset_bounded
#print axioms odd_reset_of_all_barriers
end BB429Q0Macro
