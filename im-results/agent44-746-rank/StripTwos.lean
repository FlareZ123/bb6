import Std
set_option maxHeartbeats 0
namespace CascadeFastReturn

def stripTwos (q : Nat) : Nat × Nat :=
  if q%2=1 then (0,q)
  else if q=0 then (0,0)
  else
    let p := stripTwos (q/2)
    (p.1+1,p.2)
termination_by q
decreasing_by omega

theorem stripTwos_spec (q : Nat) (hq : 0<q) :
    q = 2^(stripTwos q).1 * (stripTwos q).2 ∧
    (stripTwos q).2 % 2 = 1 := by
  induction q using Nat.strongRecOn with
  | ind q ih =>
    by_cases hodd : q%2=1
    · simp [stripTwos, hodd]
    · have heven : q%2=0 := by omega
      have hq2 : 0<q/2 := by omega
      have hlt : q/2<q := by omega
      obtain ⟨hfac,hpar⟩ := ih (q/2) hlt hq2
      have hqeq : q=2*(q/2) := by omega
      have hstep : stripTwos q = ((stripTwos (q/2)).1+1, (stripTwos (q/2)).2) := by
        rw [stripTwos.eq_1]
        simp [hodd, show q≠0 by omega]
      rw [hstep]
      constructor
      · simp only [Prod.fst, Prod.snd]
        calc
          q = 2*(q/2) := hqeq
          _ = 2*(2^(stripTwos (q/2)).1 * (stripTwos (q/2)).2) := congrArg (2*·) hfac
          _ = 2^((stripTwos (q/2)).1+1) * (stripTwos (q/2)).2 := by
            rw [Nat.pow_succ]
            ac_rfl
      · exact hpar

#print axioms stripTwos_spec
end CascadeFastReturn
