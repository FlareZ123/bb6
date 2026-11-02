import EvenTargetForward
import Lean.Elab.Tactic.Omega

namespace BB6.Agent46

/-- Reverse arbitrary even-bounce recursion paths ending in the special c=4 exit. -/
theorem bounce_lift_three (K n : Nat) (hK:K%2=0) :
    (bounce K (invLiftC K n 3)).2=(bounce (invLiftK K n) 4).2 := by
  induction n generalizing K with
  | zero => simp [invLiftC,invLiftK]
  | succ n ih =>
    have hC : 4≤invLiftC (2*K+4) n 3 := by
      have hh:=invLiftC_lower (2*K+4) n 3
      omega
    have hlow : ¬2*K+5+invLiftC (2*K+4) n 3<4 := by omega
    have hodd : K%2≠1 := by omega
    have h4 : 2*K+5+invLiftC (2*K+4) n 3 ≠ 4 := by omega
    have h5 : 2*K+5+invLiftC (2*K+4) n 3 ≠ 5 := by omega
    have hhigh : ¬2*K+5+invLiftC (2*K+4) n 3≤2*K+8 := by omega
    simp only [invLiftC,invLiftK]
    rw [bounce]
    simp only [if_neg hlow,if_neg hodd,if_neg h4,if_neg h5,if_neg hhigh]
    have hsub : 2*K+5+invLiftC (2*K+4) n 3-(2*K+5)=invLiftC (2*K+4) n 3 := by omega
    rw [hsub]
    exact ih (2*K+4) (by omega)

theorem invLiftK_even_three (K n : Nat) (hK:K%2=0) : (invLiftK K n)%2=0 := by
  induction n generalizing K with
  | zero => simpa [invLiftK] using hK
  | succ n ih => simpa only [invLiftK] using ih (2*K+4) (by omega)

theorem bounce_three_sufficient (K c x n : Nat) (hK:K%2=0)
    (hs:x+6=2^n*(2*K+8))
    (hc:c+(2*K+8)+3*n=x+10) :
    (bounce K c).2=some (x,3) := by
  have hpow : 2^(n+1)*(K+4)=x+6 := by
    calc
      2^(n+1)*(K+4)=2^n*2*(K+4) := by rw [Nat.pow_succ]
      _ = 2^n*(2*(K+4)) := by ac_rfl
      _ = 2^n*(2*K+8) := by congr 1 <;> omega
      _ = x+6 := hs.symm
  have hin : invLiftC K n 3=c := by
    have hh := invLiftC_closed K n 3
    rw [hpow] at hh
    omega
  rw [←hin]
  rw [bounce_lift_three K n hK]
  have he := invLiftK_even_three K n hK
  have hb : (bounce (invLiftK K n) 4).2=some (2*(invLiftK K n)+2,3) := by
    have hnotodd : (invLiftK K n)%2≠1 := by omega
    simp [bounce,hnotodd]
  rw [hb]
  have hz := invLiftK_closed K n
  have heq : 2*(invLiftK K n)+2=x := by
    have hh : 2*(invLiftK K n)+8=2^n*(2*K+8) := by
      calc
        2*(invLiftK K n)+8=2*(2^n*(K+4)) := by omega
        _ = 2^n*(2*(K+4)) := by ac_rfl
        _ = 2^n*(2*K+8) := by congr 1 <;> omega
    omega
  simp [heq]

/-- Complete necessity of the arithmetic formula for all even-bounce y=3 exits. -/
theorem bounce_three_necessary (K c x : Nat) (hK:K%2=0)
    (hb:(bounce K c).2=some (x,3)) :
    ∃ n:Nat, x+6=2^n*(2*K+8) ∧ c+(2*K+8)+3*n=x+10 := by
  induction c using Nat.strongRecOn generalizing K x with
  | ind c ih =>
    by_cases hlow:c<4
    · simp [bounce,hlow] at hb
    · have hnotodd : K%2≠1 := by omega
      by_cases h4:c=4
      · have eq : x=2*K+2 := by
          have hh:=hb
          rw [bounce] at hh
          simp only [if_neg hlow,if_neg hnotodd,if_pos h4] at hh
          have heq := Option.some.inj hh
          have hj := Prod.mk.inj heq
          omega
        exact ⟨0,by simp; omega,by omega⟩
      · by_cases h5:c=5
        · simp [bounce,hlow,hnotodd,h4,h5] at hb
        · by_cases hs:c≤2*K+8
          · have hh:=hb
            rw [bounce] at hh
            simp only [if_neg hlow,if_neg hnotodd,if_neg h4,if_neg h5,if_pos hs] at hh
            have heq:=Option.some.inj hh
            have hprod:=Prod.mk.inj heq
            omega
          · have hlt:c-(2*K+5)<c := by omega
            have hstep : (bounce (2*K+4) (c-(2*K+5))).2=some (x,3) := by
              have hh:=hb
              rw [bounce] at hh
              simpa only [if_neg hlow,if_neg hnotodd,if_neg h4,if_neg h5,if_neg hs] using hh
            obtain ⟨n,hpow,hcost⟩ := ih (c-(2*K+5)) hlt (2*K+4) x (by omega) hstep
            refine ⟨n+1,?_,?_⟩
            · rw [Nat.pow_succ]
              calc
                x+6=2^n*(2*(2*K+4)+8) := hpow
                _ = 2^n*(2*(2*K+8)) := by congr 1 <;> omega
                _ = 2^n*2*(2*K+8) := by ac_rfl
            · omega

/-- Complete exact characterization, including arbitrary recursive depths,
    of the special y=3 even-middle bounce output. -/
theorem bounce_three_exact (K c x:Nat) (hK:K%2=0) :
    (bounce K c).2=some (x,3) ↔
    ∃ n:Nat, x+6=2^n*(2*K+8) ∧ c+(2*K+8)+3*n=x+10 := by
  constructor
  · exact bounce_three_necessary K c x hK
  · rintro ⟨n,hs,hc⟩
    exact bounce_three_sufficient K c x n hK hs hc

#print axioms bounce_three_exact
end BB6.Agent46
