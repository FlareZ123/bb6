import OddOddConeSource
import Lean.Elab.Tactic.Omega

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace BB6.Agent2COddOddVal3

/-- At even-source bounce depth >=2 the target sum is divisible by sixteen. -/
private theorem depth_lt_two (a n s : Nat)
    (ha : a % 2 = 0) (ha2 : 2 ≤ a)
    (hs : s % 16 = 8)
    (h : s = 2^n * (2*(a-1)+6)) : n < 2 := by
  by_cases hn : n < 2
  · exact hn
  have hn2 : 2 ≤ n := by omega
  let r := n - 2
  have hr : n = r+2 := by dsimp [r]; omega
  have hb4 : (2*(a-1)+6) % 4 = 0 := by omega
  have hdvd : 4 ∣ (2*(a-1)+6) := Nat.dvd_of_mod_eq_zero hb4
  cases hdvd with
  | intro q hq =>
    have hpower : 2^(r+2) = 4*2^r := by simp [Nat.pow_add]; omega
    have hmul : 2^(r+2) * (2*(a-1)+6) = 16*(2^r*q) := by
      rw [hq, hpower]
      simp only [Nat.mul_assoc, Nat.mul_left_comm, Nat.mul_comm]
    rw [hr, hmul] at h
    omega

private theorem no_zero_parent (s n : Nat)
    (hs : s%16=8) (hbound : 24≤s) (heq : s=2^n*8) : False := by
  by_cases h0 : n=0
  · subst n
    simp at heq
    omega
  have hn : 1≤n := by omega
  let r := n-1
  have hr : n = r+1 := by dsimp [r]; omega
  have he : 2^(r+1)*8 = 16*2^r := by
    rw [Nat.pow_add]
    simp only [show 2^1=2 by decide]
    omega
  rw [hr, he] at heq
  omega

private theorem even_parent_forbidden (a k x y n : Nat)
    (ha : a % 2 = 0) (ha2 : 2 ≤ a) (hhigh : a < 2*k)
    (hx : x % 8 = 1) (hy : y % 8 = 7)
    (hs : (x+y) % 16 = 8)
    (hS : x+y = 2^n * (2*(a-1)+6))
    (hC : (2*k-a+3)+(2*(a-1)+6)+3*n = x+2*y) :
    5≤k ∧ k%2=1 ∧ (a+k)%4=1 := by
  have hn := depth_lt_two a n (x+y) ha ha2 hs hS
  have hn1 : n ≠ 1 := by
    intro h1
    subst n
    simp at hS hC
    omega
  have h0 : n=0 := by omega
  subst n
  simp at hS hC
  omega

private theorem no_odd_power (s a n : Nat)
    (hs : s % 2=0)
    (h : s+1=2^n*(2*(a-1)+8)) : False := by
  have hh : 2*(a-1)+8=2*(a-1+4) := by omega
  rw [hh] at h
  have hmul : 2^n*(2*(a-1+4))=2*(2^n*(a-1+4)) := by
    simp only [Nat.mul_assoc, Nat.mul_left_comm, Nat.mul_comm]
  rw [hmul] at h
  omega

private theorem no_one_power (s n : Nat)
    (hs : s%2=0)
    (h : s+1=2^n*16) : False := by
  have hmul : 2^n*16=2*(2^n*8) := by omega
  rw [hmul] at h
  omega

/-- Every possible original-machine predecessor of this 8/16 odd-odd
    cone has odd right counter and forbidden coordinate sum 1 mod 4. -/
theorem all_parent_forbidden (a k x y : Nat)
    (hx : x%8=1) (hy : y%8=7)
    (hs : (x+y)%16=8) (hy8 : 8≤y)
    (h : BB6.Agent46.sectionPreimageCriterion a k x y) :
    5≤k ∧ k%2=1 ∧ (a+k)%4=1 := by
  unfold BB6.Agent46.sectionPreimageCriterion at h
  by_cases ha0 : a=0
  · simp only [if_pos ha0] at h
    by_cases hk0 : k=0
    · simp [hk0] at h
    by_cases hk1 : k=1
    · simp only [if_neg hk0,if_pos hk1] at h
      omega
    simp only [if_neg hk0,if_neg hk1] at h
    rcases h with ⟨n,hs0,_⟩
    exact False.elim (no_zero_parent (x+y) n hs (by omega) hs0)
  by_cases ha1 : a=1
  · simp only [if_neg ha0,if_pos ha1] at h
    by_cases hk0 : k=0
    · simp [hk0] at h
    by_cases hk1 : k=1
    · simp [hk0,hk1] at h
    by_cases hk2 : k=2
    · simp only [if_neg hk0,if_neg hk1,if_pos hk2] at h
      omega
    by_cases hk3 : k=3
    · simp only [if_neg hk0,if_neg hk1,if_neg hk2,if_pos hk3] at h
      omega
    simp only [if_neg hk0,if_neg hk1,if_neg hk2,if_neg hk3] at h
    rcases h with ⟨n,hs1,_⟩
    have hmod : (x+y)%2=0 := by omega
    exact False.elim (no_one_power (x+y) n hmod hs1)
  have ha2 : 2≤a := by omega
  simp only [if_neg ha0,if_neg ha1] at h
  by_cases hk0 : k=0
  · simp [hk0] at h
  simp only [if_neg hk0] at h
  by_cases hreg : 2*k≤a
  · simp only [if_pos hreg] at h
    rcases h with ⟨_,hy0⟩
    omega
  simp only [if_neg hreg] at h
  by_cases hae : a%2=0
  · simp only [if_pos hae] at h
    rcases h with ⟨n,hS,hC⟩
    exact even_parent_forbidden a k x y n hae ha2 (by omega) hx hy hs hS hC
  simp only [if_neg hae] at h
  rcases h with ⟨n,hS,_⟩
  have hmod : (x+y)%2=0 := by omega
  exact False.elim (no_odd_power (x+y) a n hmod hS)

/-- Exact source-level all-time exclusion of the 8/16 odd-odd
    cone, of asymptotic ambient density 1/128. -/
theorem blank_unreachable (x y : Nat)
    (hx : x%8=1) (hy : y%8=7)
    (hy8 : 8≤y) (hs : (x+y)%16=8) (time : Nat) :
    BB6.Agent8Section.run BB6.Agent46.secNext time (some (5,1)) ≠ some (x,y) := by
  intro h
  cases time with
  | zero =>
      simp [BB6.Agent8Section.run] at h
      omega
  | succ n =>
      cases hp : BB6.Agent8Section.run BB6.Agent46.secNext n (some (5,1)) with
      | none => simp [BB6.Agent8Section.run,hp] at h
      | some p =>
          rcases p with ⟨a,k⟩
          have he : BB6.Agent46.secNext (a,k)=some (x,y) := by
            simpa [BB6.Agent8Section.run,hp] using h
          have hcrit :=
            (BB6.Agent46.complete_section_inverse a k x y (by omega)).mp he
          obtain ⟨hk5,hkodd,hksum⟩ :=
            all_parent_forbidden a k x y hx hy hs hy8 hcrit
          cases n with
          | zero =>
              simp [BB6.Agent8Section.run] at hp
              omega
          | succ nn =>
              have hi := BB6.Agent3.blank_section_odd_image nn a k hp hk5 hkodd
              omega

private theorem power_lower (m : Nat) : 4*m+4 ≤ 2^(2*m+2) := by
  induction m with
  | zero => decide
  | succ m ih =>
    rw [show 2*(m+1)+2=2*m+2+2 by omega, Nat.pow_add]
    change 4*(m+1)+4 ≤ 2^(2*m+2)*4
    omega

/-- High halting targets with m=3 (mod 4), j=3m+10 (mod 16)
    lie in this uniform source-forbidden 8/16 cone. -/
theorem high_stop_coordinates (j m k : Nat)
    (hm3 : 3≤m) (hm4 : m%4=3)
    (hj16 : j%16 = (3*m+10)%16)
    (hstop : k+j+3*m+5=2^(2*m+2)*(j+3)) :
    (2*j+3)%8=1 ∧ k%8=7 ∧ (2*j+3+k)%16=8 ∧ 8≤k := by
  have hp4 : (2:Nat)^4 ∣ 2^(2*m+2) := Nat.pow_dvd_pow 2 (by omega)
  have hp16 : 16 ∣ 2^(2*m+2) := by
    simpa only [show (2:Nat)^4=16 by decide] using hp4
  have hdiv : 16 ∣ (k+j+3*m+5) := by
    rw [hstop]
    exact Nat.dvd_trans hp16 (Nat.dvd_mul_right _ _)
  have hzero : (k+j+3*m+5)%16=0 := Nat.mod_eq_zero_of_dvd hdiv
  have hlower := power_lower m
  have hj0 := Nat.mul_le_mul_right j (by omega : 1≤2^(2*m+2))
  have hj : j ≤ 2^(2*m+2)*j := by simpa using hj0
  have hm : 3*m+13 ≤ 2^(2*m+2)*3 := by
    have h := Nat.mul_le_mul_right 3 hlower
    omega
  rw [Nat.mul_add] at hstop
  constructor
  · omega
  constructor
  · omega
  constructor
  · omega
  · omega

/-- Authentic Machine C blank-halting obstruction: an infinite
    1/64-density high-stop parameter family is excluded at all times. -/
theorem high_stop_blank_unreachable (j m k : Nat)
    (hm3 : 3≤m) (hm4 : m%4=3)
    (hj16 : j%16=(3*m+10)%16)
    (hstop : k+j+3*m+5=2^(2*m+2)*(j+3)) :
    ∀ time, BB6.Agent8Section.run BB6.Agent46.secNext time (some (5,1)) ≠
      some (2*j+3,k) := by
  intro time
  obtain ⟨hx,hy,hs,hy8⟩ :=
    high_stop_coordinates j m k hm3 hm4 hj16 hstop
  exact blank_unreachable (2*j+3) k hx hy hy8 hs time

#print axioms all_parent_forbidden
#print axioms blank_unreachable
#print axioms high_stop_coordinates
#print axioms high_stop_blank_unreachable

end BB6.Agent2COddOddVal3
