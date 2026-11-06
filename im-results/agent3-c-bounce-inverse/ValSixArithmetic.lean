import Lean
import Lean.Elab.Tactic.Omega

set_option maxRecDepth 8192

namespace BB6.Agent3ValSix

/-- On the valuation-six output, original odd-source bounce depth is 1 or 3. -/
theorem depth_one_or_three (x y a k n : Nat)
    (hx : x % 16 = 13) (hy : y % 16 = 2) (ha : a % 2 = 1)
    (hlt : a < 2*k) (hmod : (x+y+1)%256=64)
    (hsum : x+y+1=2^n*(2*(a-1)+8))
    (hcost : (2*k-a+3)+(2*(a-1)+8)+3*n=x+2*y+2) :
    (n=1 ∧ 4*a+12=x+y+1 ∧ 2*k+a+10=x+2*y) ∨
    (n=3 ∧ 16*a+48=x+y+1 ∧ 2*k+a+16=x+2*y) := by
  have hnodd : n%2=1 := by omega
  have hnlt : n<5 := by
    by_cases hn : n < 5
    · exact hn
    have hpow : 32 ∣ 2^n := by
      change 2^5 ∣ 2^n
      exact Nat.pow_dvd_pow 2 (by omega)
    obtain ⟨r,hr⟩ := hpow
    obtain ⟨q,hq⟩ : ∃ q, a-1=2*q := ⟨(a-1)/2, by omega⟩
    have hfactor : 2*(a-1)+8=4*(q+2) := by omega
    have hdiv : 128 ∣ x+y+1 := by
      refine ⟨r*(q+2), ?_⟩
      calc
        x+y+1=2^n*(2*(a-1)+8) := hsum
        _=(32*r)*(4*(q+2)) := by rw [hr,hfactor]
        _=(32*4)*(r*(q+2)) := by ac_rfl
        _=128*(r*(q+2)) := by rfl
    have hz := Nat.mod_eq_zero_of_dvd hdiv
    omega
  have hc : n=1 ∨ n=3 := by omega
  rcases hc with h1 | h3
  · left
    subst n
    simp only [Nat.pow_one] at hsum
    constructor
    · rfl
    · constructor <;> omega
  · right
    subst n
    simp at hsum
    constructor
    · rfl
    · constructor <;> omega

/-- The exceptional a=1 source is absent above the small power-of-two base. -/
theorem no_one_source_power (x y n : Nat)
    (hmod : (x+y+1)%256=64) (hbig : 320≤x+y+1)
    (hsum : x+y+1=2^n*16) : False := by
  by_cases h : n < 3
  · have hn : n=0 ∨ n=1 ∨ n=2 := by omega
    rcases hn with h0 | h1 | h2
    · subst n; simp at hsum; omega
    · subst n; simp at hsum; omega
    · subst n; simp at hsum; omega
  · have hpow : 8 ∣ 2^n := by
      change 2^3 ∣ 2^n
      exact Nat.pow_dvd_pow 2 (by omega)
    obtain ⟨r,hr⟩ := hpow
    have hdiv : 128 ∣ x+y+1 := by
      refine ⟨r, ?_⟩
      calc
        x+y+1 = 2^n*16 := hsum
        _=(8*r)*16 := by rw [hr]
        _=128*r := by ac_rfl
    have hz := Nat.mod_eq_zero_of_dvd hdiv
    omega

theorem first_bounce_forbidden (x y a k : Nat)
    (hx : x%16=13) (hy : y%16=2)
    (hmod : (x+y+1)%256=64)
    (h1 : 4*a+12=x+y+1 ∧ 2*k+a+10=x+2*y) :
    k%2=1 ∧ (a+k)%4=2 ∧ 5≤k := by
  omega

theorem third_bounce_forbidden (x y a k : Nat)
    (hx : x%16=13) (hy : y%16=2)
    (hmod : (x+y+1)%256=64) (hbig : 320≤x+y+1)
    (h3 : 16*a+48=x+y+1 ∧ 2*k+a+16=x+2*y) :
    4≤k ∧ k%2=0 ∧ (a+k)%4=1 ∧
    5≤(k-2)/2 ∧ ((k-2)/2)%2=1 ∧
    ((a+k-2)+((k-2)/2))%4=2 := by
  omega

theorem direct_forbidden (x y : Nat)
    (hx : x%16=13) (hy : y%16=2) (hsize : 34≤y)
    (hmod : (x+y+1)%256=64) :
    let a := x+y-2
    let k := (y-2)/2
    4≤k ∧ k%2=0 ∧ (a+k)%4=1 ∧
    5≤(k-2)/2 ∧ ((k-2)/2)%2=1 ∧
    ((a+k-2)+((k-2)/2))%4=2 := by
  dsimp
  omega

#print axioms depth_one_or_three
#print axioms no_one_source_power
#print axioms first_bounce_forbidden
#print axioms third_bounce_forbidden
#print axioms direct_forbidden
end BB6.Agent3ValSix
