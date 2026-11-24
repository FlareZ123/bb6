import CSourceBridge16
import Lean.Elab.Tactic.Omega

set_option maxRecDepth 20000

namespace BB6.Agent13M16

/-- A false M16 quotient lookup contradicts source reachability from the
    published blank start. This uses Agent 43's checked generic source
    bridge, not a reset-only corollary. -/
private theorem cLine_not_seen (a k : Nat)
    (hseen : CCert.seen (CCert.q a) (CCert.q k) (CCert.q 0)=false) :
    ¬ BB6CLine.Reach (a,k,0) := by
  intro hr
  have hcert := CCert.source_reachable_embeds16 hr
  have hs := CCert.reachable_seen hcert
  rw [hseen] at hs
  cases hs

private theorem q_big_eq (x y : Nat) (hx : 8≤x) (hy : 8≤y)
    (hmod : x%16=y%16) : CCert.q x=CCert.q y := by
  apply CCert.q_congr_big
  · exact hx
  · exact hy
  · exact hmod

/-- Five low-family quotient cells absent from the checked 24^3 table. -/
private theorem low_seen_false (k : Nat) (hk : 8≤k)
    (hmod : k%16=9 ∨ k%16=13 ∨ k%16=7 ∨
            k%16=1 ∨ k%16=5) :
    CCert.seen (CCert.q 1) (CCert.q k) (CCert.q 0)=false := by
  rcases hmod with h9 | h13 | h7 | h1 | h5
  · rw [q_big_eq k 9 hk (by decide) h9]
    decide
  · rw [q_big_eq k 13 hk (by decide) h13]
    decide
  · rw [q_big_eq k 23 hk (by decide) h7]
    decide
  · rw [q_big_eq k 17 hk (by decide) h1]
    decide
  · rw [q_big_eq k 21 hk (by decide) h5]
    decide

private theorem low_margin_all (m : Nat) :
    1 ≤ m → 3*m+12 ≤ 2^(2*m+3) := by
  induction m with
  | zero =>
      intro hm
      omega
  | succ m ih =>
      intro hm
      by_cases hz : m=0
      · subst m
        decide
      · have hm' : 1≤m := by omega
        have hprev := ih hm'
        have hexp : 2*(m+1)+3=(2*m+3)+2 := by omega
        rw [hexp, Nat.pow_add]
        rw [show (2:Nat)^2=4 by decide]
        omega

/-- The M16 quotient excludes all five newly removed infinite low
    stopping progressions m=1,5,7,9,13 modulo 16. The target is the
    original three-counter CLine state from the published blank start. -/
theorem low_family_unreachable (m : Nat) (hm : 1≤m)
    (hclass : m%16=1 ∨ m%16=5 ∨ m%16=7 ∨
              m%16=9 ∨ m%16=13) :
    ¬ BB6CLine.Reach (1, 2^(2*m+3)-(3*m+4), 0) := by
  let k := 2^(2*m+3)-(3*m+4)
  have hmargin : 3*m+12≤2^(2*m+3) := low_margin_all m hm
  have hk : 8≤k := by
    dsimp [k]
    omega
  have hstop : k+3*m+4=2^(2*m+3) := by
    dsimp [k]
    exact Nat.sub_add_cancel (by omega)
  have hdiv16 : (2:Nat)^4 ∣ 2^(2*m+3) :=
    Nat.pow_dvd_pow 2 (by omega)
  have hpow16 : 16 ∣ 2^(2*m+3) := by
    simpa using hdiv16
  have hpowmod : 2^(2*m+3)%16=0 :=
    Nat.mod_eq_zero_of_dvd hpow16
  have hmod : k%16=9 ∨ k%16=13 ∨ k%16=7 ∨
              k%16=1 ∨ k%16=5 := by
    rcases hclass with h1 | h5 | h7 | h9 | h13
    · exact Or.inl (by omega)
    · exact Or.inr (Or.inl (by omega))
    · exact Or.inr (Or.inr (Or.inl (by omega)))
    · exact Or.inr (Or.inr (Or.inr (Or.inl (by omega))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (by omega))))
  have hseen := low_seen_false k hk hmod
  change ¬ BB6CLine.Reach (1,k,0)
  exact cLine_not_seen 1 k hseen

private theorem high_power_linear_bound (m : Nat) :
    4*m+4 ≤ 2^(2*m+2) := by
  induction m with
  | zero =>
      decide
  | succ m ih =>
      have hexp : 2*(m+1)+2=(2*m+2)+2 := by omega
      rw [hexp, Nat.pow_add]
      rw [show (2:Nat)^2=4 by decide]
      omega

private theorem high_target_k_ge8 (j m : Nat)
    (hj : 3≤j) (hm : 3≤m) :
    8 ≤ 2^(2*m+2)*(j+3)-(j+3*m+5) := by
  let P := 2^(2*m+2)
  have hP : 4*m+4≤P := by
    simpa [P] using high_power_linear_bound m
  have hpos : 0<P := by
    dsimp [P]
    exact Nat.pow_pos (by decide)
  have hp : 1≤P := by omega
  have hjP : j≤P*j := by
    simpa only [Nat.one_mul] using Nat.mul_le_mul_right j hp
  have hmP : 3*m+13≤3*P := by
    have h := Nat.mul_le_mul_left 3 hP
    omega
  have hmul : P*(j+3)=P*j+3*P := by
    rw [Nat.mul_add, Nat.mul_comm P 3]
  have hmargin : j+3*m+13≤P*(j+3) := by
    rw [hmul]
    omega
  change 8≤P*(j+3)-(j+3*m+5)
  omega

/-- Four high-family quotient cells absent from the checked 24^3 table. -/
private theorem high_seen_false (a k : Nat) (ha : 8≤a) (hk : 8≤k)
    (haMod : a%16=7 ∨ a%16=15)
    (hkMod : k%16=4 ∨ k%16=12) :
    CCert.seen (CCert.q a) (CCert.q k) (CCert.q 0)=false := by
  rcases haMod with ha7 | ha15
  · have hqa : CCert.q a=CCert.q 23 :=
      q_big_eq a 23 ha (by decide) (by omega)
    rcases hkMod with hk4 | hk12
    · have hqk : CCert.q k=CCert.q 20 :=
        q_big_eq k 20 hk (by decide) (by omega)
      rw [hqa,hqk]
      decide
    · have hqk : CCert.q k=CCert.q 12 :=
        q_big_eq k 12 hk (by decide) (by omega)
      rw [hqa,hqk]
      decide
  · have hqa : CCert.q a=CCert.q 15 :=
      q_big_eq a 15 ha (by decide) (by omega)
    rcases hkMod with hk4 | hk12
    · have hqk : CCert.q k=CCert.q 20 :=
        q_big_eq k 20 hk (by decide) (by omega)
      rw [hqa,hqk]
      decide
    · have hqk : CCert.q k=CCert.q 12 :=
        q_big_eq k 12 hk (by decide) (by omega)
      rw [hqa,hqk]
      decide

/-- The M16 quotient excludes the entire two-parameter high stopping
    family m>=3, m=3 (mod 4), j>=3, j=m+3 (mod 8). Its four possible
    quotient images are (15,12,0), (15,20,0), (23,12,0), and (23,20,0),
    none of which is in the certified blank-origin reachable set. -/
theorem high_family_unreachable (j m : Nat)
    (hm : 3≤m) (hm4 : m%4=3) (hj : 3≤j)
    (hjmod : j%8=(m+3)%8) :
    ¬ BB6CLine.Reach
      (2*j+3, 2^(2*m+2)*(j+3)-(j+3*m+5), 0) := by
  let a := 2*j+3
  let P := 2^(2*m+2)
  let k := P*(j+3)-(j+3*m+5)
  have ha : 8≤a := by
    dsimp [a]
    omega
  have hk : 8≤k := by
    simpa [P,k] using high_target_k_ge8 j m hj hm
  have hdiv16 : (2:Nat)^4 ∣ P := by
    dsimp [P]
    exact Nat.pow_dvd_pow 2 (by omega)
  have hpow16 : 16 ∣ P := by
    simpa using hdiv16
  rcases hpow16 with ⟨q,hq⟩
  have hprod16 : 16 ∣ P*(j+3) := by
    refine ⟨q*(j+3), ?_⟩
    rw [hq, Nat.mul_assoc]
  have hstop : k+j+3*m+5=P*(j+3) := by
    dsimp [k]
    omega
  have hstopmod16 : (k+j+3*m+5)%16=0 := by
    rw [hstop]
    exact Nat.mod_eq_zero_of_dvd hprod16
  have hdiv8 : (2:Nat)^3 ∣ P := by
    dsimp [P]
    exact Nat.pow_dvd_pow 2 (by omega)
  have hpow8 : 8 ∣ P := by
    simpa using hdiv8
  rcases hpow8 with ⟨r,hr⟩
  have hprod8 : 8 ∣ P*(j+3) := by
    refine ⟨r*(j+3), ?_⟩
    rw [hr, Nat.mul_assoc]
  have hstopmod8 : (k+j+3*m+5)%8=0 := by
    rw [hstop]
    exact Nat.mod_eq_zero_of_dvd hprod8
  have hm8 : m%8=3 ∨ m%8=7 := by omega
  have hj8 : j%8=2 ∨ j%8=6 := by
    rcases hm8 with hm3 | hm7
    · have hj6 : j%8=6 := by omega
      exact Or.inr hj6
    · have hj2 : j%8=2 := by omega
      exact Or.inl hj2
  have hsumMod8 : (j+3*m+5)%8=4 := by
    rcases hm8 with hm3 | hm7
    · have hj6 : j%8=6 := by omega
      omega
    · have hj2 : j%8=2 := by omega
      omega
  have hk8 : k%8=4 := by omega
  have haMod : a%16=7 ∨ a%16=15 := by
    rcases hj8 with hj2 | hj6
    · left
      dsimp [a]
      omega
    · right
      dsimp [a]
      omega
  have hkMod : k%16=4 ∨ k%16=12 := by omega
  have hseen := high_seen_false a k ha hk haMod hkMod
  change ¬ BB6CLine.Reach (a,k,0)
  exact cLine_not_seen a k hseen

#print axioms low_family_unreachable
#print axioms high_family_unreachable

end BB6.Agent13M16
