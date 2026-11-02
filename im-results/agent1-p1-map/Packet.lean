import GParity

namespace BB6.P1Reduction

/-- The high-counter branch of the published G recursion. -/
theorem G_upper (k c : Nat) (hc : 2*k+2 ≤ c) :
    G k c = (4*k+4, c-(2*k+2)) := by
  unfold G
  have h1 : ¬ c < 2*k := by omega
  have h2 : ¬ c ≤ 2*k+1 := by omega
  simp [h1, h2]

theorem T_even_big_first (a c : Nat) (ha : a%2=0) (hc : a+10 ≤ c) :
    T a c = some (a+3,c-2) := by
  have h0 : c ≠ 0 := by omega
  have h1 : c ≠ 1 := by omega
  simp [T,h0,h1,ha]

theorem T_even_big_second (a c : Nat) (ha : a%2=0) (hc : a+10 ≤ c) :
    T (a+3) (c-2) = some (2*a+12,c-a-10) := by
  have hn0 : c-2 ≠ 0 := by omega
  have hn1 : c-2 ≠ 1 := by omega
  have hn2 : c-2 ≠ 2 := by omega
  have hn3 : c-2 ≠ 3 := by omega
  have haodd : (a+3)%2 ≠ 0 := by omega
  have hG : G ((a+3)/2+1) ((c-2)-2) = (2*a+12,c-a-10) := by
    have hbound : 2*((a+3)/2+1)+2 ≤ (c-2)-2 := by omega
    rw [G_upper _ _ hbound]
    congr 1 <;> omega
  simp [T,hn0,hn1,hn2,hn3,haodd,hG]

/-- Finite termination along a sequence of accelerated P1 hubs. -/
inductive HaltsFrom : Nat × Nat → Prop where
  | halt (a c : Nat) (h : T a c = none) : HaltsFrom (a,c)
  | step (a c a' c' : Nat) (h : T a c = some (a',c'))
      (tail : HaltsFrom (a',c')) : HaltsFrom (a,c)

/-- Every even-a hub with right counter 4 halts in two accelerated transitions. -/
theorem even_four_halts (a : Nat) (ha : a%2=0) : HaltsFrom (a,4) := by
  have hs : T a 4 = some (a+3,2) := by simp [T,ha]
  have hh : T (a+3) 2 = none := by
    apply (T_none_iff _ _).2
    omega
  exact HaltsFrom.step a 4 (a+3) 2 hs (HaltsFrom.halt (a+3) 2 hh)

/-- Recursively generated "dangerous" even-counter starts. -/
def critical (a : Nat) : Nat → Nat
  | 0 => 4
  | n+1 => a+10 + critical (2*a+12) n

/-- Infinite parametric halting family of synthetic hub configurations.
    This theorem does not say the blank-tape orbit enters the family. -/
theorem critical_halts (a n : Nat) (ha : a%2=0) :
    HaltsFrom (a,critical a n) := by
  induction n generalizing a with
  | zero =>
    exact even_four_halts a ha
  | succ n ih =>
    have hh := ih (2*a+12) (by omega)
    let c := critical a (n+1)
    have hc : a+10 ≤ c := by dsimp [c,critical]; omega
    have h1 := T_even_big_first a c ha hc
    have h2 := T_even_big_second a c ha hc
    have hc' : c-a-10 = critical (2*a+12) n := by
      dsimp [c,critical]
      omega
    rw [hc'] at h2
    exact HaltsFrom.step a c (a+3) (c-2) h1
      (HaltsFrom.step (a+3) (c-2) (2*a+12)
       (critical (2*a+12) n) h2 hh)

/-- Explicit exponential growth of the dangerous-counter family, with subtraction
    avoided in the proposition so the statement holds purely in naturals. -/
theorem critical_closed_form (a n : Nat) :
    critical a n + 2*n = (a+12)*(2^n-1)+4 := by
  induction n generalizing a with
  | zero =>
    simp [critical]
  | succ n ih =>
    have hp : 1 ≤ 2^n := by
      have hpos : 0 < 2^n := Nat.pow_pos (by omega)
      omega
    have heq : 2^(n+1)-1 = 2*(2^n-1)+1 := by
      rw [Nat.pow_succ]
      omega
    have hh := ih (2*a+12)
    change critical (2*a+12) n + 2*n =
      ((2*a+12)+12)*(2^n-1)+4 at hh
    have hh_norm : critical (2*a+12) n + 2*n =
      (2*a+24)*(2^n-1)+4 := by
      simpa only [show 2*a+12+12 = 2*a+24 by omega] using hh
    simp only [critical]
    rw [heq]
    have hpre : a + 10 + critical (2*a+12) n + 2*(n+1) =
        a+12 + (2*a+24)*(2^n-1)+4 := by
      omega
    rw [hpre]
    simp only [Nat.mul_add, Nat.add_mul, Nat.mul_assoc, Nat.mul_comm]
    omega

/-- Specializing to a = 2 recovers the sparse observed halting values. -/
theorem critical_two_closed_form (n : Nat) :
    critical 2 n + 2*n + 10 = 14*2^n := by
  have h := critical_closed_form 2 n
  have hp : 1 ≤ 2^n := by
    have hh : 0 < 2^n := Nat.pow_pos (by omega)
    omega
  change critical 2 n + 2*n = 14*(2^n-1)+4 at h
  omega



/-- Even input strictly below the direct-exit threshold returns an odd
    second counter after the nested G recursion. -/
theorem G_small_even_returns_odd (k c : Nat)
    (hc : c%2=0) (hsmall : c < 2*k+2) :
    (G k c).2 % 2 = 1 := by
  by_cases hlow : c < 2*k
  · rw [G]
    simp only [hlow, dite_true]
    apply G_preserves_odd_second
    omega
  · have hmid : c ≤ 2*k+1 := by omega
    rw [G]
    simp only [hlow, dite_false, hmid, ite_true]
    omega

/-- The medium-counter even phase always exits to an odd second counter
    after two accelerated transitions. -/
theorem T_even_small_exits_odd (a c : Nat)
    (ha : a%2=0) (hceven : c%2=0)
    (hcmin : 6 ≤ c) (hcmax : c < a+10) :
    ∃ b d, T a c = some (a+3,c-2) ∧
      T (a+3) (c-2) = some (b,d) ∧ d%2=1 := by
  have hn0 : c≠0 := by omega
  have hn1 : c≠1 := by omega
  have h1 : T a c = some (a+3,c-2) := by simp [T,hn0,hn1,ha]
  have hn0' : c-2≠0 := by omega
  have hn1' : c-2≠1 := by omega
  have hn2' : c-2≠2 := by omega
  have hn3' : c-2≠3 := by omega
  have ha' : (a+3)%2≠0 := by omega
  let g := G ((a+3)/2+1) ((c-2)-2)
  have hodd : g.2 %2=1 := by
    apply G_small_even_returns_odd
    · omega
    · omega
  have h2 : T (a+3) (c-2) = some g := by
    simp [T,hn0',hn1',hn2',hn3',ha',g]
  exact ⟨g.1,g.2,h1,h2,hodd⟩


/-- From an odd right counter the map makes a non-halting transition
    to a zero or odd right counter. -/
theorem T_odd_second_avoids_positive_even (a c : Nat) (hc : c%2=1) :
    ∃ a' c', T a c = some (a',c') ∧ (c'=0 ∨ c'%2=1) := by
  have hn0 : c≠0 := by omega
  by_cases hc1 : c=1
  · refine ⟨a+2,0,?_,Or.inl rfl⟩
    simp [T,hn0,hc1]
  · have hc3 : c≥3 := by omega
    by_cases ha : a%2=0
    · refine ⟨a+3,c-2,?_,Or.inr (by omega)⟩
      simp [T,hn0,hc1,ha]
    · by_cases hc' : c=3
      · let g := G (a/2) 1
        have hodd : g.2%2=1 := by
          exact G_preserves_odd_second (a/2) 1 (by decide)
        refine ⟨g.1,g.2,?_,Or.inr hodd⟩
        simp [T,hn0,hc1,ha,hc',g]
      · let g := G (a/2+1) (c-2)
        have hodd : g.2%2=1 := by
          apply G_preserves_odd_second
          omega
        have hc2 : c≠2 := by omega
        refine ⟨g.1,g.2,?_,Or.inr hodd⟩
        simp [T,hn0,hc1,ha,hc2,hc',g]


/-- For any pair of naturals, G raises the sum above its weighted input. -/
theorem G_mass_lower (k c : Nat) :
    2*k+c+2 ≤ (G k c).1+(G k c).2 := by
  induction k using Nat.strongRecOn generalizing c with
  | ind k ih =>
    by_cases h1 : c < 2*k
    · have hr : k - (c/2+1) < k := by omega
      have hrec := ih _ hr (2*c+3)
      rw [G]
      simp only [h1, dite_true]
      omega
    · by_cases h2 : c ≤ 2*k+1
      · rw [G]
        simp [h1,h2]
        omega
      · rw [G]
        simp [h1,h2]
        omega

/-- The special c=1 branch has two additional units of mass. -/
theorem G_mass_one (k : Nat) :
    2*k+5 ≤ (G k 1).1+(G k 1).2 := by
  by_cases hk:k=0
  · subst k
    simp [G]
  · have hlow : 1 < 2*k := by omega
    have hr := G_mass_lower (k-1) 5
    rw [G]
    simp only [hlow, dite_true, Nat.reduceDiv, Nat.reduceMul, Nat.reduceAdd]
    omega

/-- Strict rank growth along every nonhalting accelerated action. -/
theorem T_mass_increases (a c a' c' : Nat)
    (h : T a c = some (a',c')) :
    a+c < a'+c' := by
  unfold T at h
  by_cases hc0 : c=0
  · simp [hc0] at h
    omega
  · by_cases hc1 : c=1
    · simp [hc0,hc1] at h
      omega
    · by_cases ha : a%2=0
      · simp [hc0,hc1,ha] at h
        omega
      · by_cases hc2 : c=2
        · simp [hc0,hc1,ha,hc2] at h
        · by_cases hc3 : c=3
          · simp [hc0,hc1,ha,hc2,hc3] at h
            have hm := G_mass_one (a/2)
            have heq : (G (a/2) 1).1 = a' ∧ (G (a/2) 1).2 = c' := by
              exact Prod.mk.inj h
            rw [heq.1,heq.2] at hm
            omega
          · simp [hc0,hc1,ha,hc2,hc3] at h
            have hm := G_mass_lower (a/2+1) (c-2)
            have heq : (G (a/2+1) (c-2)).1 = a' ∧
              (G (a/2+1) (c-2)).2 = c' := by
              exact Prod.mk.inj h
            rw [heq.1,heq.2] at hm
            omega

#print axioms BB6.P1Reduction.T_mass_increases

/-- Iteration of the certified accelerated map. `some` means the machine
    has not taken a halting transition within the specified horizon. -/
def iterT : Nat → Nat × Nat → Option (Nat × Nat)
  | 0, x => some x
  | n+1, x => (T x.1 x.2).bind (iterT n)

/-- All critical inputs reach the dangerous gate after 2n safe transitions. -/
theorem critical_gate (a n : Nat) (ha : a%2=0) :
    ∃ b, b%2=0 ∧ iterT (2*n) (a,critical a n) = some (b,4) := by
  induction n generalizing a with
  | zero =>
    exact ⟨a,ha,by simp [iterT,critical]⟩
  | succ n ih =>
    obtain ⟨b,hbeven,hrun⟩ := ih (2*a+12) (by omega)
    let c := critical a (n+1)
    have hc : a+10 ≤ c := by dsimp [c,critical]; omega
    have h1 := T_even_big_first a c ha hc
    have h2 := T_even_big_second a c ha hc
    have hc' : c-a-10 = critical (2*a+12) n := by
      dsimp [c,critical]; omega
    rw [hc'] at h2
    refine ⟨b,hbeven,?_⟩
    have hnum : 2*(n+1) = (2*n)+2 := by omega
    rw [hnum]
    have hnum' : (2*n)+2 = (2*n+1)+1 := by omega
    rw [hnum']
    change (T a c).bind (fun x => (T x.1 x.2).bind (iterT (2*n))) = some (b,4)
    simp only [h1, Option.bind_some, h2]
    exact hrun

/-- Prefix/suffix fusion for iteration. -/
theorem iterT_add (m n : Nat) (s : Nat × Nat) :
    iterT (m+n) s = (iterT m s).bind (iterT n) := by
  induction m generalizing s with
  | zero => simp [iterT]
  | succ m ih =>
    rw [Nat.succ_add]
    simp only [iterT]
    cases h : T s.1 s.2 with
    | none => simp [h]
    | some t => simp [h, ih]

/-- The first halting transition follows the 2n safe steps and one more
    safe transition through (odd,2); the (2n+2)-step iterate is none. -/
theorem critical_halts_at (a n : Nat) (ha : a%2=0) :
    iterT (2*n+2) (a,critical a n) = none := by
  obtain ⟨b,hbeven,hrun⟩ := critical_gate a n ha
  have hstep : T b 4 = some (b+3,2) := by simp [T,hbeven]
  have hstop : T (b+3) 2 = none := by
    apply (T_none_iff _ _).2
    omega
  have htwo : iterT 2 (b,4) = none := by
    simp [iterT,hstep,hstop]
  rw [show 2*n+2 = (2*n)+2 by omega, iterT_add, hrun]
  exact htwo

#print axioms BB6.P1Reduction.critical_closed_form
#print axioms BB6.P1Reduction.critical_gate
#print axioms BB6.P1Reduction.critical_halts_at

#print axioms BB6.P1Reduction.T_even_big_second
#print axioms BB6.P1Reduction.critical_halts

end BB6.P1Reduction
