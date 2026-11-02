import EvenFamily
namespace BB6.HaltingFunnel

def Gate (n : Nat) : Nat := 14*2^n-2*n-10

theorem power_ge_index (n : Nat) : n+1 ≤ 2^n := by
  have hh := Nat.lt_pow_self (n:=n) (a:=2) (by decide)
  omega

theorem Gate_sandwich (n : Nat) (hn : 1≤n) :
    14*2^(n-1) < Gate n+8 ∧ Gate n+8 < 14*2^n := by
  have hlow : n ≤ 2^(n-1) := by
    have hh := Nat.lt_pow_self (n:=n-1) (a:=2) (by decide)
    omega
  have hp : 2^n = 2*2^(n-1) := by
    calc
      2^n = 2^((n-1)+1) := congrArg (fun t:Nat => 2^t) (by omega)
      _ = 2^(n-1)*2 := by rw [Nat.pow_succ]
      _ = 2*2^(n-1) := by omega
  have hbig : 2*n+10 ≤ 14*2^n := by
    rw [hp]
    omega
  have hcalc : Gate n+8+2*n+2 = 14*2^n := by
    dsimp [Gate]
    omega
  constructor
  · rw [hp] at hcalc
    omega
  · omega

/-- The alternative positive-even feeder to every n>=1 critical gateway is
    forbidden by the exact E_j family classification and power sandwich. -/
theorem blank_no_gate_even_feeder (n : Nat) (hn : 1≤n) :
    ¬BlankReach (Gate n-4) 2 := by
  obtain ⟨hlo,hhi⟩ := Gate_sandwich n hn
  have hpower := power_ge_index n
  have hbound : 4 ≤ Gate n := by
    have hb : 2*n+10 ≤ 14*2^n := by omega
    dsimp [Gate]
    omega
  have hmod : (Gate n-4)%2=0 := by
    dsimp [Gate]
    omega
  intro hr
  obtain ⟨j,hj⟩ := blank_even_hub_power (Gate n-4) 2 hr (by decide) (by decide) hmod
  have hsub : Gate n-4+12 = Gate n+8 := by omega
  rw [hsub] at hj
  by_cases hjn : j<n
  · have hp : 2^j ≤ 2^(n-1) :=
      Nat.pow_le_pow_right (by decide : 0 < (2:Nat)) (by omega)
    omega
  · have hp : 2^n ≤ 2^j :=
      Nat.pow_le_pow_right (by decide : 0 < (2:Nat)) (by omega)
    omega

/-- An odd-index critical target necessarily has a forbidden ancestor,
    provided its alternative even-sector predecessor has been excluded. -/
theorem blank_gate_multiple_four (k : Nat)
    (hno : ¬BlankReach (4*k+12) 2) :
    ¬BlankReach 2 (4*k+16) := by
  intro hr
  cases hr with
  | next a c _ _ hr1 ht =>
      obtain ⟨ha,hc⟩ := T_to_two_positive a c (4*k+16) (by omega) ht
      have ha' : a=4*k+15 := by omega
      subst a
      subst c
      cases hr1 with
      | next a c _ _ hr2 ht2 =>
          rcases T_odd_left_predecessor a c (4*k+15) 0 ht2 (by omega) with hcase | hcase
          · obtain ⟨hc1,hleft,hright⟩:=hcase
            have ha':a=4*k+13 := by omega
            subst a
            subst c
            cases hr2 with
            | next x y _ _ hr3 ht3 =>
                rcases T_odd_left_predecessor x y (4*k+13) 1 ht3 (by omega) with h | h
                · omega
                · obtain ⟨heven,hge,hleft,hright⟩:=h
                  have hx:x=4*k+10 := by omega
                  have hy:y=3 := by omega
                  subst x
                  subst y
                  have hinv := blank_even_left_invariant (4*k+10) 3 hr3 (by omega) (by omega)
                  rcases hinv with h | h <;> omega
          · obtain ⟨heven,hge,hleft,hright⟩:=hcase
            have ha' : a=4*k+12 := by omega
            have hc' : c=2 := by omega
            subst a
            subst c
            exact hno hr2

/-- Every odd-index critical gateway H(n) is unreachable from the actual
    blank-entry hub (2,1), for all n odd. -/
theorem blank_no_odd_critical (n : Nat) (hn : n%2=1) :
    ¬BlankReach 2 (Gate n) := by
  have h1 : 1≤n := by omega
  have hpow := power_ge_index n
  have hp4 : 4 ∣ 14*2^n := by
    by_cases hn1 : n=1
    · subst n
      decide
    · have hge:2≤n:=by omega
      have hpoweq : 2^n = 4*2^(n-2) := by
        calc
          2^n = 2^((n-2)+2) := congrArg (fun t:Nat => 2^t) (by omega)
          _ = 2^(n-2)*2^2 := by rw [Nat.pow_add]
          _ = 4*2^(n-2) := by simp only [Nat.reducePow]; omega
      refine ⟨14*2^(n-2), ?_⟩
      omega
  have hge : 16≤Gate n := by
    dsimp [Gate]
    omega
  have hmod : Gate n%4=0 := by
    dsimp [Gate]
    omega
  let k := (Gate n-16)/4
  have he : Gate n=4*k+16 := by dsimp [k]; omega
  rw [he]
  apply blank_gate_multiple_four k
  have hp : 4*k+12=Gate n-4 := by omega
  rw [hp]
  exact blank_no_gate_even_feeder n h1

#print axioms BB6.HaltingFunnel.blank_even_hub_power
#print axioms BB6.HaltingFunnel.blank_no_gate_even_feeder
#print axioms BB6.HaltingFunnel.blank_no_odd_critical
end BB6.HaltingFunnel
