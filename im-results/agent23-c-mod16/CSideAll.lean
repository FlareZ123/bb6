import CSide
namespace BB6.Agent23

/-- Uniform side-gateway exclusion for every index divisible by 16, including 0. -/
theorem side_sixteen_unreachable (n : Nat) (hn : n%16=0) :
    ¬ Reach (0,4*n,24*n+23) := by
  intro hr
  by_cases h0 : n=0
  · subst n
    have hh := reached_zero_high 0 19 (by simpa using hr)
    omega
  · have hn16 : 16 ≤ n := by omega
    have he : n=16*((n/16-1)+1) := by omega
    have hk : 4*n=64*(n/16-1)+64 := by omega
    have hc : 24*n+23=384*(n/16-1)+407 := by omega
    have hh : Reach (0,64*(n/16-1)+64,384*(n/16-1)+407) := by
      simpa only [←hk,←hc] using hr
    exact side_positive_sixteen_unreachable (n/16-1) hh

#print axioms side_sixteen_unreachable
end BB6.Agent23
