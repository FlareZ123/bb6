import RankDecision

namespace BB6.P1Rank
open BB6.Agent1

/-- Strict rank progress between any two defined blank-orbit times. -/
private theorem run_later_rank (m n a c b d : Nat)
    (hm : run m=some (a,c))
    (hn : run (m+n+1)=some (b,d)) : a+c < b+d := by
  induction n generalizing b d with
  | zero =>
    have he : m+0+1=m+1 := by omega
    rw [he] at hn
    have ht : T a c=some (b,d) := by
      change (run m).bind (fun p => T p.1 p.2) = some (b,d) at hn
      simpa only [hm, Option.bind_some] using hn
    exact T_sum_growth a c b d ht
  | succ n ih =>
    have he : m+(n+1)+1=(m+n+1)+1 := by omega
    rw [he] at hn
    change (run (m+n+1)).bind (fun p => T p.1 p.2) = some (b,d) at hn
    cases hmid : run (m+n+1) with
    | none =>
      simp only [hmid, Option.bind_none] at hn
      cases hn
    | some p =>
      rcases p with ⟨x,y⟩
      have hlast : T x y=some (b,d) := by
        simpa only [hmid, Option.bind_some] using hn
      have hbefore := ih x y hmid
      have hstep := T_sum_growth x y b d hlast
      omega

/-- Each reachable target appears at most once in the actual blank orbit. -/
theorem blank_time_unique (n m a c:Nat)
    (hn:run n=some (a,c)) (hm:run m=some (a,c)) : n=m := by
  by_cases h:n<m
  · have he : m=n+(m-n-1)+1 := by omega
    have hr := run_later_rank n (m-n-1) a c a c hn (by rw [←he]; exact hm)
    omega
  · by_cases h2:m<n
    · have he : n=m+(n-m-1)+1 := by omega
      have hr := run_later_rank m (n-m-1) a c a c hm (by rw [←he]; exact hn)
      omega
    · omega

/-- Two different blank-reachable configurations cannot share their next
    configuration. True globally for the original P1 accelerated map. -/
theorem reachable_predecessor_unique
    (a c b d z w:Nat) (ha:Reach a c) (hb:Reach b d)
    (hta:T a c=some (z,w)) (htb:T b d=some (z,w)) :
    a=b ∧ c=d := by
  obtain ⟨na,_,hra⟩ := reach_has_run a c ha
  obtain ⟨nb,_,hrb⟩ := reach_has_run b d hb
  have hz1 : run (na+1)=some (z,w) := by simp [run,hra,hta]
  have hz2 : run (nb+1)=some (z,w) := by simp [run,hrb,htb]
  have eqn : na=nb := by
    have he:=blank_time_unique (na+1) (nb+1) z w hz1 hz2
    omega
  rw [eqn] at hra
  have hpair : (a,c)=(b,d) := by
    have hsome : some (a,c)=some (b,d) := by rw [←hra,←hrb]
    exact Option.some.inj hsome
  exact Prod.mk.inj hpair

#print axioms BB6.P1Rank.reachable_predecessor_unique
end BB6.P1Rank
