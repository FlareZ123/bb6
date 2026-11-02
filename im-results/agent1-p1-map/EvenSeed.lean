import PosEvenForm
namespace BB6.Agent1

/-- A positive-even-right reachable hub has an authentic reset ancestor,
    with an exact conservation equation for its reset counter. -/
theorem even_hub_reset_seed (b d : Nat) (hr : Reach b d)
    (hb : b%2=0) (hdpos : 0<d) (hdeven : d%2=0) :
    ∃ j s : Nat, Reach 2 s ∧ b+12=14*2^j ∧ s+2*j+2=b+d := by
  induction b using Nat.strongRecOn generalizing d with
  | ind b ih =>
    by_cases h2 : b=2
    · refine ⟨0,d,?_,?_,?_⟩
      · simpa [h2] using hr
      · omega
      · omega
    · cases hr with
      | init => omega
      | next a c _ _ hpre ht =>
        obtain ⟨ha, hc, hbval, hdval⟩ :=
          even_target_parent a c b d ht hb hdpos hdeven h2
        obtain ⟨x, y, hrx, hxe, hax, hy⟩ :=
          odd_target_parent a c hpre ha (by omega) (by omega)
        have hxless : x<b := by omega
        have hyeven : y%2=0 := by omega
        obtain ⟨j,s,hs,hpow,hsum⟩ :=
          ih x hxless y hrx hxe (by omega) hyeven
        refine ⟨j+1,s,hs,?_,?_⟩
        · rw [Nat.pow_succ]
          omega
        · omega

#print axioms BB6.Agent1.even_hub_reset_seed
end BB6.Agent1
