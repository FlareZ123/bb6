import BounceCalc
import Lean.Elab.Tactic.Omega

namespace BB6.Agent46

theorem bounce_even_small (k : Nat) (hk : k%2=0) :
    run 2 (some (0,k,4)) = some (2*k+2,3,0) ∧
    run 2 (some (0,k,5)) = none := by
  have hdiv : k%2+2*(k/2)=k := Nat.mod_add_div k 2
  have hfirst4 : BB6CLine.nextC (0,k,4)=some (2*k+2,2,1) := by
    change (if k%2=0 then some (4*(k/2)+2,2,1)
      else some (4*(k/2)+5,0,4)) = some (2*k+2,2,1)
    simp only [hk,ite_true,Option.some.injEq,Prod.mk.injEq]
    constructor
    · omega
    · trivial
  have hfirst5 : BB6CLine.nextC (0,k,5)=some (2*k+2,2,2) := by
    change (if k%2=0 then some (4*(k/2)+2,2,2)
      else some (4*(k/2)+5,0,5)) = some (2*k+2,2,2)
    simp only [hk,ite_true,Option.some.injEq,Prod.mk.injEq]
    constructor
    · omega
    · trivial
  constructor
  · change run 1 ((some (0,k,4)).bind BB6CLine.nextC)=_
    simp only [Option.bind_some,hfirst4]
    simp [run,BB6CLine.nextC]
  · change run 1 ((some (0,k,5)).bind BB6CLine.nextC)=_
    simp only [Option.bind_some,hfirst5]
    simp [run,BB6CLine.nextC]

theorem bounce_exact (c : Nat) : ∀ k : Nat, 4≤c →
    run (bounce k c).1 (some (0,k,c)) = (bounce k c).2.map embed0 := by
  induction c using Nat.strongRecOn with
  | ind c ih =>
    intro k hc
    rw [bounce.eq_1]
    have hnot : ¬c<4 := by omega
    simp only [hnot,ite_false]
    by_cases ho : k%2=1
    · simp only [ho,ite_true]
      by_cases hs : c≤2*k+6
      · simp only [hs,ite_true]
        exact odd_zero_exit k c ho hc hs
      · simp only [hs,ite_false]
        have hlarge : 2*k+6<c := by omega
        have hsmall : c-(2*k+3)<c := Nat.sub_lt (by omega) (by omega)
        have hcsmall : 4≤c-(2*k+3) := by omega
        have hrec := ih (c-(2*k+3)) hsmall (2*k+3) hcsmall
        have hpre := odd_zero_continue k c ho hlarge
        let out := bounce (2*k+3) (c-(2*k+3))
        change run (2*k+4+out.1) (some (0,k,c))=out.2.map embed0
        rw [run_add,hpre]
        exact hrec
    · simp only [ho,ite_false]
      have he : k%2=0 := by omega
      by_cases hc4 : c=4
      · simp only [hc4,ite_true]
        exact (bounce_even_small k he).1
      · simp only [hc4,ite_false]
        by_cases hc5 : c=5
        · simp only [hc5,ite_true]
          exact (bounce_even_small k he).2
        · simp only [hc5,ite_false]
          by_cases hs : c≤2*k+8
          · simp only [hs,ite_true]
            have hc6 : 6≤c := by omega
            exact even_zero_exit k c he hc6 hs
          · simp only [hs,ite_false]
            have hlarge : 2*k+8<c := by omega
            have hsmall : c-(2*k+5)<c := Nat.sub_lt (by omega) (by omega)
            have hcsmall : 4≤c-(2*k+5) := by omega
            have hrec := ih (c-(2*k+5)) hsmall (2*k+4) hcsmall
            have hpre := even_zero_continue k c he hlarge
            let out := bounce (2*k+4) (c-(2*k+5))
            change run (2*k+3+out.1) (some (0,k,c))=out.2.map embed0
            rw [run_add,hpre]
            exact hrec

#print axioms bounce_even_small
#print axioms bounce_exact
end BB6.Agent46
