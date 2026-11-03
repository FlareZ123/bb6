import Init

namespace SpaceNeedlePrime

-- Closed-form preimage families of the published one-counter map.
def oddQ : Nat → Nat
  | 0 => 45
  | t+1 => 1024 * oddQ t + 1581
def evenQ : Nat → Nat
  | 0 => 214
  | t+1 => 262144 * evenQ t + 413910

def oddExponent (t : Nat) := 9 + 10*t
def evenExponent (t : Nat) := 12 + 18*t

theorem odd_power_identity (t : Nat) :
    2 ^ oddExponent t = 17 + 11 * oddQ t := by
  induction t with
  | zero => decide
  | succ t ih =>
    have he : oddExponent (t+1) = oddExponent t + 10 := by
      simp only [oddExponent]
      omega
    rw [he, Nat.pow_add, ih]
    change (17 + 11 * oddQ t) * 1024 = 17 + 11 * (1024 * oddQ t + 1581)
    omega

theorem even_power_identity (t : Nat) :
    2 ^ evenExponent t = 30 + 19 * evenQ t := by
  induction t with
  | zero => decide
  | succ t ih =>
    have he : evenExponent (t+1) = evenExponent t + 18 := by
      simp only [evenExponent]
      omega
    rw [he, Nat.pow_add, ih]
    change (30 + 19 * evenQ t) * 262144 = 30 + 19 * (262144 * evenQ t + 413910)
    omega

def oddSource (q : Nat) := 8*q+10
def evenSource (q : Nat) := 16*q+22

theorem odd_source_decomposition (q : Nat) :
    oddSource q + 2 = 2^2 * (2*q+3) := by
  simp [oddSource]; omega

theorem even_source_decomposition (q : Nat) :
    evenSource q + 2 = 2^3 * (2*q+3) := by
  simp [evenSource]; omega

theorem odd_successor_counter (t : Nat) :
    oddSource (oddQ t) + 2 + 3*(oddQ t+1) + 2 = 2 ^ oddExponent t := by
  rw [odd_power_identity]
  simp [oddSource]
  omega

theorem even_successor_counter (t : Nat) :
    evenSource (evenQ t) + 3 + 3*(evenQ t+1) + 2 = 2 ^ evenExponent t := by
  rw [even_power_identity]
  simp [evenSource]
  omega

theorem odd_crt (m a : Nat) (hm5 : m%5 ≠ 0) (ha2 : a%2=1) :
    ∃ t : Nat, (a+m*t)%10=9 := by
  have hm_lt : m%5<5 := Nat.mod_lt _ (by decide)
  have ha_lt : a%10<10 := Nat.mod_lt _ (by decide)
  have hm : m%5=1 ∨ m%5=2 ∨ m%5=3 ∨ m%5=4 := by omega
  have ha : a%10=1 ∨ a%10=3 ∨ a%10=5 ∨ a%10=7 ∨ a%10=9 := by omega
  rcases hm with hm | hm | hm | hm
  all_goals rcases ha with ha | ha | ha | ha | ha
  all_goals first
    | exact ⟨0, by omega⟩
    | exact ⟨2, by omega⟩
    | exact ⟨4, by omega⟩
    | exact ⟨6, by omega⟩
    | exact ⟨8, by omega⟩

theorem even_crt (m a : Nat) (hm3 : m%3 ≠ 0) (ha2 : a%2=0) :
    ∃ t : Nat, (a+m*t)%18=12 := by
  have hm_lt : m%9<9 := Nat.mod_lt _ (by decide)
  have ha_lt : a%18<18 := Nat.mod_lt _ (by decide)
  have hm : m%9=1 ∨ m%9=2 ∨ m%9=4 ∨ m%9=5 ∨ m%9=7 ∨ m%9=8 := by omega
  have ha : a%18=0 ∨ a%18=2 ∨ a%18=4 ∨ a%18=6 ∨ a%18=8 ∨ a%18=10 ∨ a%18=12 ∨ a%18=14 ∨ a%18=16 := by omega
  rcases hm with hm | hm | hm | hm | hm | hm
  all_goals rcases ha with ha | ha | ha | ha | ha | ha | ha | ha | ha | ha
  all_goals first
    | exact ⟨0, by omega⟩
    | exact ⟨2, by omega⟩
    | exact ⟨4, by omega⟩
    | exact ⟨6, by omega⟩
    | exact ⟨8, by omega⟩
    | exact ⟨10, by omega⟩
    | exact ⟨12, by omega⟩
    | exact ⟨14, by omega⟩
    | exact ⟨16, by omega⟩

theorem extend_progression (m a lower p r t : Nat)
    (hm : 0 < m) (hp : 0 < p)
    (ht : (a + m*t)%p = r) :
    ∃ k : Nat, lower ≤ k ∧ k%m=a%m ∧ k%p=r := by
  let k := a + m*(t+p*(lower+1))
  have heq : k = (a+m*t) + p*(m*(lower+1)) := by
    simp only [k, Nat.mul_add, Nat.mul_left_comm]
    omega
  have hlow : lower+1 ≤ m*(lower+1) :=
    Nat.le_mul_of_pos_left (lower+1) hm
  have hlow2 : m*(lower+1) ≤ p*(m*(lower+1)) :=
    Nat.le_mul_of_pos_left (m*(lower+1)) hp
  have hk : lower ≤ k := by omega
  have hkm : k%m=a%m := by
    dsimp [k]
    rw [Nat.mul_comm m (t+p*(lower+1))]
    exact Nat.add_mul_mod_self_right a (t+p*(lower+1)) m
  have hkp : k%p=r := by
    rw [heq, Nat.add_mul_mod_self_left]
    exact ht
  exact ⟨k,hk,hkm,hkp⟩

def admissibleExponent (k : Nat) : Prop :=
  ∃ v q : Nat, 2^v * (2*q+3) + v + 3*(q+1) = 2^k

theorem odd_admissible (t : Nat) : admissibleExponent (oddExponent t) := by
  unfold admissibleExponent
  refine ⟨2, oddQ t, ?_⟩
  rw [odd_power_identity]
  change 4*(2*oddQ t+3)+2+3*(oddQ t+1) = 17+11*oddQ t
  omega

theorem even_admissible (t : Nat) : admissibleExponent (evenExponent t) := by
  unfold admissibleExponent
  refine ⟨3, evenQ t, ?_⟩
  rw [even_power_identity]
  change 8*(2*evenQ t+3)+3+3*(evenQ t+1) = 30+19*evenQ t
  omega

theorem every_coprime15_progression_has_unbounded_predecessors
    (m a bound : Nat) (hm : 0 < m)
    (hm3 : m%3 ≠ 0) (hm5 : m%5 ≠ 0) :
    ∃ k, bound ≤ k ∧ k%m=a%m ∧ admissibleExponent k := by
  by_cases ha : a%2=1
  · obtain ⟨t, ht⟩ := odd_crt m a hm5 ha
    obtain ⟨k, hbound, hmodm, hmod10⟩ :=
      extend_progression m a bound 10 9 t hm (by decide) ht
    refine ⟨k, hbound, hmodm, ?_⟩
    have hk : oddExponent (k/10) = k := by
      have h := Nat.mod_add_div k 10
      unfold oddExponent
      omega
    simpa only [hk] using odd_admissible (k/10)
  · have he : a%2=0 := by
      have hlt := Nat.mod_lt a (by decide : 0<2)
      omega
    obtain ⟨t, ht⟩ := even_crt m a hm3 he
    obtain ⟨k, hbound, hmodm, hmod18⟩ :=
      extend_progression m a bound 18 12 t hm (by decide) ht
    refine ⟨k, hbound, hmodm, ?_⟩
    have hk : evenExponent (k/18) = k := by
      have h := Nat.mod_add_div k 18
      unfold evenExponent
      omega
    simpa only [hk] using even_admissible (k/18)

#print axioms every_coprime15_progression_has_unbounded_predecessors
#print axioms odd_admissible
#print axioms even_admissible

end SpaceNeedlePrime
