import BB429Rank
import Lean.Elab.Tactic.Omega
namespace BB429SyntheticOdd
set_option maxHeartbeats 10000000
set_option maxRecDepth 30000

/-- Backward demand guaranteeing that n forward first-branch transitions
    lead to w+3=2u, for a starting first counter u>=2. -/
def oddStart : Nat → Nat → Nat
  | u, 0 => 2*u-3
  | u, n+1 => oddStart (2*u+3) n + (2*u+3)

private theorem run_succ_left (n : Nat) (s : BB429.State) :
    BB429.run (n+1) s = (BB429.next s).bind (BB429.run n) := by
  induction n generalizing s with
  | zero =>
      simp [BB429.run]
  | succ n ih =>
      change (BB429.run (n+1) s).bind BB429.next =
        (BB429.next s).bind (BB429.run (n+1))
      rw [ih]
      cases h : BB429.next s with
      | none => simp [h]
      | some t => simp [h, BB429.run]

private theorem odd_first (u n : Nat) :
    BB429.next (u,oddStart u (n+1)) =
    some (2*u+3, oddStart (2*u+3) n) := by
  have h : 2*u+3 ≤ oddStart u (n+1) := by simp [oddStart]
  simp [BB429.next, h, oddStart]
  omega

private theorem from_positive (n u : Nat) (hu : 2≤u) :
    ∃ a b, BB429.run n (u,oddStart u n)=some (a,b) ∧ b+3=2*a := by
  induction n generalizing u with
  | zero =>
      refine ⟨u,2*u-3,?_,?_⟩
      · simp [BB429.run, oddStart]
      · omega
  | succ n ih =>
      obtain ⟨a,b,hr,hg⟩ := ih (2*u+3) (by omega)
      refine ⟨a,b,?_,hg⟩
      rw [run_succ_left, odd_first]
      simpa only [Option.bind_some] using hr

theorem blank_synthetic_odd (n : Nat) :
    ∃ a b, BB429.run (n+1) (0,oddStart 0 (n+1))=some (a,b) ∧
      b+3=2*a := by
  obtain ⟨a,b,hr,hg⟩ := from_positive n 3 (by omega)
  refine ⟨a,b,?_,hg⟩
  rw [run_succ_left, odd_first]
  simpa only [Option.bind_some] using hr

/-- Explicit arithmetic of the guaranteed odd-reset entrance seed. -/
theorem oddStart_explicit (u n : Nat) :
    oddStart u (n+1) + 2*u + 3*(n+1) + 15 =
      4*(u+3)*2^(n+1) := by
  induction n generalizing u with
  | zero =>
      simp [oddStart]
      omega
  | succ n ih =>
      calc
        oddStart u ((n+1)+1)+2*u+3*((n+1)+1)+15 =
          oddStart (2*u+3) (n+1)+2*(2*u+3)+3*(n+1)+15 := by
            simp only [oddStart]
            omega
        _ = 4*((2*u+3)+3)*2^(n+1) := ih (2*u+3)
        _ = 4*(u+3)*2^((n+1)+1) := by
          have h : 2*u+3+3=2*(u+3) := by omega
          rw [h]
          simp only [Nat.pow_succ]
          ac_rfl

def depth : Nat → Nat
  | 0 => 11
  | k+1 => 2*depth k+5

private theorem depth_ge (k : Nat) : k+1≤depth k := by
  induction k with
  | zero => decide
  | succ k ih =>
      simp only [depth]
      omega

private theorem depth_explicit (k : Nat) :
    3*depth k+15=48*2^k := by
  induction k with
  | zero => decide
  | succ k ih =>
      simp only [depth, Nat.pow_succ]
      omega

/-- For every modulus 2^k, a synthetic (0,W) input congruent to blank
    reaches the odd near-terminal reset line in finite source time. -/
theorem synthetic_all_dyadic (k : Nat) :
    ∃ W n a b, 2^k ∣ W ∧
      BB429.run n (0,W)=some (a,b) ∧ b+3=2*a := by
  have hd : 1≤depth k := by have hh:=depth_ge k; omega
  obtain ⟨m,hm⟩ : ∃ m,depth k=m+1 := by
    cases h : depth k with
    | zero => omega
    | succ m => exact ⟨m,rfl⟩
  have he : oddStart 0 (depth k)+3*depth k+15=12*2^(depth k) := by
    rw [hm]
    have h := oddStart_explicit 0 m
    omega
  have hp : 2^k ∣ 12*2^(depth k) := by
    rcases Nat.pow_dvd_pow 2 (by have hh:=depth_ge k; omega : k≤depth k) with ⟨t,ht⟩
    refine ⟨12*t,?_⟩
    simp only [ht]
    ac_rfl
  have hq : 2^k ∣ 3*depth k+15 := by
    refine ⟨48,?_⟩
    have hh := depth_explicit k
    omega
  have hw : 2^k ∣ oddStart 0 (depth k) := by
    have hs : oddStart 0 (depth k) = 12*2^(depth k)-(3*depth k+15) := by omega
    rw [hs]
    exact Nat.dvd_sub hp hq
  obtain ⟨a,b,hr,hg⟩ := blank_synthetic_odd m
  refine ⟨oddStart 0 (depth k),depth k,a,b,hw,?_,hg⟩
  simpa only [hm] using hr

/-- The odd near-terminal feeder is an actual successful source transition
    to zero first counter and second counter 2 mod4. -/
theorem near_reset_next (a b : Nat) (hg : b+3=2*a) :
    BB429.next (a,b)=some (0,4*a+2) := by
  have hbig : ¬b ≥ 2*a+3 := by omega
  have h2 : b ≠ 2*a+2 := by omega
  have h1 : b ≠ 2*a+1 := by omega
  have h0 : b ≠ 2*a := by omega
  have hp : b%2 ≠ 0 := by omega
  have hd : a-b/2=2 := by omega
  simp [BB429.next,hbig,h2,h1,h0,hp,hd]
  omega

/-- Every dyadic congruence class of the *blank initial state* contains
    an artificial section start whose full source trace enters an odd
    exceptional zero-reset transition. No true blank-root reachability is
    claimed for the artificial start. -/
theorem every_dyadic_blank_class_has_odd_reset (k : Nat) :
    ∃ W n a b z,
      2^k ∣ W ∧ BB429.run n (0,W)=some (a,b) ∧
      BB429.next (a,b)=some (0,z) ∧ z%4=2 := by
  obtain ⟨W,n,a,b,hmod,hr,hg⟩ := synthetic_all_dyadic k
  refine ⟨W,n,a,b,4*a+2,hmod,hr,near_reset_next a b hg,?_⟩
  omega

/-- No finite dyadic quotient can simultaneously contain the original blank
    seed, respect the complete forward source dynamics, and prohibit the
    odd exceptional reset. This is a METHOD LIMITATION, not a machine proof. -/
theorem no_dyadic_odd_reset_free_invariant
    (k : Nat) (P : Nat × Nat → Prop)
    (hmod : ∀ x y, x.1 % 2^k = y.1 % 2^k →
      x.2 % 2^k = y.2 % 2^k → P x → P y)
    (hinit : P (0,0))
    (hstep : ∀ x y, P x → BB429.next x = some y → P y)
    (hforbid : ∀ a b z, P (a,b) →
      BB429.next (a,b)=some (0,z) → z%4≠2) : False := by
  obtain ⟨W,n,a,b,z,hd,hr,hn,hz⟩ :=
    every_dyadic_blank_class_has_odd_reset k
  have hseed : P (0,W) := by
    apply hmod (0,0) (0,W)
    · simp
    · exact (Nat.mod_eq_zero_of_dvd hd).symm
    · exact hinit
  have hrun : ∀ (m : Nat) (s t : BB429.State), P s →
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
            simp only [hp,Option.bind_some] at ht
            exact hstep p t (ih s p hs hp) ht
  exact hforbid a b z (hrun n (0,W) (a,b) hseed hr) hn hz

#print axioms synthetic_all_dyadic
#print axioms blank_synthetic_odd
#print axioms near_reset_next
#print axioms every_dyadic_blank_class_has_odd_reset
#print axioms no_dyadic_odd_reset_free_invariant
end BB429SyntheticOdd
