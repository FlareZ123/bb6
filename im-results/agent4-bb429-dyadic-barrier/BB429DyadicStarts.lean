import BB429Rank
import BB429Burst
import Lean.Elab.Tactic.Omega

/-!
A dyadic indistinguishability obstruction for finite-modulus reachability
invariants of the source-equivalent #429 accelerated map. The constructed
starts are synthetic, not genuine blank-orbit states.
-/
namespace BB429DyadicStarts

/-- A rapidly growing family of prefix lengths. -/
def depth : Nat → Nat
  | 0 => 17
  | k+1 => 4*depth k+13

/-- The precise first-branch synthetic halting demand at left counter zero. -/
def demand (k : Nat) : Nat :=
  12*2^(depth k) - (3*depth k+13)

private theorem depth_ge (k : Nat) : k ≤ depth k := by
  induction k with
  | zero => decide
  | succ k ih =>
      simp only [depth]
      omega

private theorem depth_positive (k : Nat) : 0 < depth k := by
  have h := depth_ge k
  cases k with
  | zero => decide
  | succ k => omega

/-- The large dyadic factor forced into the linear correction term. -/
private theorem depth_cost (k : Nat) :
    3*depth k+13 = 64*4^k := by
  induction k with
  | zero => decide
  | succ k ih =>
      change 3*(4*depth k+13)+13 = 64*4^(k+1)
      calc
        3*(4*depth k+13)+13 = 4*(3*depth k+13) := by omega
        _ = 4*(64*4^k) := by rw [ih]
        _ = 64*4^(k+1) := by rw [Nat.pow_succ]; omega

private theorem power_four_square (k : Nat) :
    4^k = 2^k*2^k := by
  calc
    4^k = (2*2)^k := by rfl
    _ = 2^k*2^k := by rw [Nat.mul_pow]

/-- A first-branch seed exists as an ordinary natural number. -/
private theorem exponential_bound (m : Nat) :
    3*(m+1)+13 ≤ 12*2^(m+1) := by
  induction m with
  | zero => decide
  | succ m ih =>
      have hpos : 0 < 2^(m+1) := Nat.pow_pos (by decide)
      rw [Nat.pow_succ]
      omega

private theorem demand_identity (k : Nat) :
    demand k + 3*depth k+13 = 12*2^(depth k) := by
  unfold demand
  have hp := depth_positive k
  cases h : depth k with
  | zero => omega
  | succ m =>
      have hb := exponential_bound m
      omega

/-- For each k, the synthetic first-branch halting seed has both coordinates
    congruent to the genuine blank seed modulo 2^k. -/
theorem demand_dyadic_divisibility (k : Nat) :
    2^k ∣ demand k := by
  have hh : depth k = k+(depth k-k) := by have h:=depth_ge k; omega
  have hp : 2^(depth k) = 2^k*2^(depth k-k) := by
    calc
      2^(depth k) = 2^(k+(depth k-k)) := by rw [←hh]
      _ = 2^k*2^(depth k-k) := by rw [Nat.pow_add]
  have hfirst : 2^k ∣ 12*2^(depth k) := by
    refine ⟨12*2^(depth k-k), ?_⟩
    calc
      12*2^(depth k) = 12*(2^k*2^(depth k-k)) := by rw [hp]
      _ = 2^k*(12*2^(depth k-k)) := by ac_rfl
  have hsecond : 2^k ∣ 3*depth k+13 := by
    refine ⟨64*2^k, ?_⟩
    rw [depth_cost, power_four_square]
    simp only [Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm]
  exact Nat.dvd_sub hfirst hsecond

/-- Every valid first-branch prefix of the mathematical source map is a
    genuine prefix of the original 12-case accelerated map. -/
theorem first_prefix_is_source (s t : Nat × Nat) (n : Nat)
    (h : BB429Burst.firstRun n s = some t) :
    BB429.run n s = some t := by
  induction n generalizing t with
  | zero => simpa [BB429Burst.firstRun, BB429.run] using h
  | succ n ih =>
      simp only [BB429Burst.firstRun] at h
      cases hp : BB429Burst.firstRun n s with
      | none => simp [hp] at h
      | some p =>
          simp only [hp, Option.bind_some] at h
          have hs : BB429.next p = some t := by
            rcases p with ⟨u,w⟩
            by_cases hg : 2*u+3 ≤ w
            · simpa [BB429Burst.firstStep, BB429.next, hg] using h
            · simp [BB429Burst.firstStep, hg] at h
          have hr : BB429.run n s = some p := ih p hp
          simpa [BB429.run, hr] using hs

/-- A whole infinite family of *synthetic* starts, indistinguishable from the
    true blank seed to any fixed 2-power modulus, nevertheless halts. -/
theorem synthetic_halt (k : Nat) :
    ∃ n a b, BB429.run n (0,demand k) = some (a,b) ∧
      BB429.next (a,b) = none := by
  have he : 2*0+demand k+3*depth k+13 =
      4*((0+3)*2^(depth k)) := by
    have hh:=demand_identity k
    omega
  obtain ⟨n,a,b,hr,hgate⟩ :=
    (BB429Burst.burst_gateway_iff 0 (demand k)).mpr ⟨depth k,he⟩
  exact ⟨n,a,b,first_prefix_is_source _ _ _ hr,
    (BB429.next_none_iff_halt_line a b).mpr hgate⟩

/-- No 2^k-residue-closed property containing blank can simultaneously be
    invariant under every nonhalting source transition and exclude all
    halting configurations. We state this without choosing a finite graph. -/
theorem no_dyadic_halt_separating_invariant
    (k : Nat) (P : Nat × Nat → Prop)
    (hmod : ∀ x y, x.1%2^k=y.1%2^k → x.2%2^k=y.2%2^k → P x → P y)
    (hinit : P (0,0))
    (hstep : ∀ x y, P x → BB429.next x = some y → P y)
    (hhalt : ∀ x, P x → BB429.next x ≠ none) : False := by
  obtain ⟨n,a,b,hr,hn⟩ := synthetic_halt k
  have hseed : P (0,demand k) := by
    apply hmod (0,0) (0,demand k)
    · simp
    · exact Nat.mod_eq_zero_of_dvd (demand_dyadic_divisibility k) |>.symm
    · exact hinit
  have hrun : ∀ (m : Nat) (s t : Nat × Nat), P s →
      BB429.run m s = some t → P t := by
    intro m
    induction m with
    | zero =>
        intro s t hs ht
        simp [BB429.run] at ht
        simpa [ht] using hs
    | succ m ih =>
        intro s t hs ht
        simp only [BB429.run] at ht
        cases hp : BB429.run m s with
        | none => simp [hp] at ht
        | some p =>
            simp only [hp, Option.bind_some] at ht
            exact hstep p t (ih s p hs hp) ht
  exact hhalt (a,b) (hrun n (0,demand k) (a,b) hseed hr) hn

#print axioms depth_cost
#print axioms demand_dyadic_divisibility
#print axioms first_prefix_is_source
#print axioms synthetic_halt
#print axioms no_dyadic_halt_separating_invariant
end BB429DyadicStarts
