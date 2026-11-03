import Std
import Lean.Elab.Tactic.Omega

namespace BB6.Agent1Direct

inductive Direct : Nat → Nat → Nat → Nat → Nat → Prop where
| zero (a k : Nat) : Direct 0 a k a k
| succ {n a k b c : Nat} (h : Direct n a k b c)
  (ha : 2 ≤ b) (hk : 0 < c) (hg : 2*c ≤ b) :
  Direct (n+1) a k (b-2*c) (2*c+2)

/-- n successful source edges with minimum weighted-mass gain four. -/
inductive MinimalRun (f : Nat × Nat → Option (Nat × Nat)) :
    Nat → Nat → Nat → Nat → Nat → Prop where
| zero (a k : Nat) : MinimalRun f 0 a k a k
| succ {n a k b c x y : Nat} (h : MinimalRun f n a k b c)
  (hs : f (b,c) = some (x,y))
  (mass : x+2*y=b+2*c+4) :
  MinimalRun f (n+1) a k x y

theorem direct_counter {n a k x y : Nat} (h : Direct n a k x y) :
    y+2 = 2^n*(k+2) := by
  induction h with
  | zero a k => simp
  | @succ n a k b c h ha hk hg ih =>
      have he : (2*c+2)+2 = 2*(c+2) := by omega
      rw [he, ih, Nat.pow_succ]
      simp [Nat.mul_comm, Nat.mul_left_comm]

theorem direct_mass {n a k x y : Nat} (h : Direct n a k x y) :
    x+2*y = a+2*k+4*n := by
  induction h with
  | zero a k => omega
  | @succ n a k b c h ha hk hg ih => omega

theorem direct_dyadic_bound {n a k x y : Nat} (h : Direct n a k x y) :
    2^(n+1)*(k+2) ≤ a+2*k+4*n+4 := by
  have hc := direct_counter h
  have hm := direct_mass h
  have he : 2^(n+1)*(k+2) = 2*(2^n*(k+2)) := by
    rw [Nat.pow_succ]
    ac_rfl
  rw [he, ←hc]
  omega

private theorem pow_two_linear (n : Nat) (hn : 4 ≤ n) :
    2^n ≥ 2*n+1 := by
  induction n with
  | zero => omega
  | succ n ih =>
      by_cases h4 : 4 ≤ n
      · have hp := ih h4
        rw [Nat.pow_succ]
        omega
      · have hn3 : n=3 := by omega
        subst n
        decide

/-- A direct chain cannot last initial weighted mass plus four steps. -/
theorem direct_bounded (a k x y : Nat)
    (h : Direct (a+2*k+4) a k x y) : False := by
  have hd := direct_dyadic_bound h
  have hp := pow_two_linear (a+2*k+4) (by omega)
  have hprod := Nat.mul_le_mul_left (2^(a+2*k+4+1)) (show 2≤k+2 by omega)
  have hcalc : 2^(a+2*k+4+1)*(k+2) ≥ 4*(2*(a+2*k+4)+1) := by
    have p := Nat.mul_le_mul_left 4 hp
    rw [Nat.pow_succ] at hprod ⊢
    omega
  omega

theorem direct_left_closed {n a k x y : Nat} (h : Direct n a k x y) :
    x+2^(n+1)*(k+2)=a+2*k+4*n+4 := by
  have hc := direct_counter h
  have hm := direct_mass h
  have he : 2^(n+1)*(k+2) = 2*(2^n*(k+2)) := by
    rw [Nat.pow_succ]
    ac_rfl
  rw [he, ←hc]
  omega

/-- Closed-form jump after n direct updates, with Nat subtraction. -/
def directState (a k n : Nat) : Nat × Nat :=
  (a+2*k+4*n+4 - 2^(n+1)*(k+2), 2^n*(k+2)-2)

theorem direct_state_exact {n a k x y : Nat}
    (h : Direct n a k x y) : directState a k n = (x,y) := by
  have hl := direct_left_closed h
  have hr := direct_counter h
  have hx : a+2*k+4*n+4-2^(n+1)*(k+2)=x := by omega
  have hy : 2^n*(k+2)-2=y := by omega
  simp [directState, hx, hy]

#print axioms direct_state_exact

theorem direct_unique {n a k x y x' y' : Nat}
    (h : Direct n a k x y) (h' : Direct n a k x' y') :
    x=x' ∧ y=y' := by
  have h1 := direct_counter h
  have h2 := direct_counter h'
  have w1 := direct_mass h
  have w2 := direct_mass h'
  omega

/-- Exact test for the nth consecutive direct update from (a,k). -/
def Allowed (a k n : Nat) : Prop :=
  4 * 2^n * (k+2) ≤ a+2*k+4*n+8

theorem direct_last_allowed {n a k x y : Nat}
    (h : Direct (n+1) a k x y) : Allowed a k n := by
  cases h with
  | succ hb ha hk hg =>
      have hc := direct_counter hb
      have hm := direct_mass hb
      dsimp [Allowed]
      have he : 4 * 2^n * (k+2) = 4 * (2^n*(k+2)) := by ac_rfl
      rw [he, ←hc]
      omega

theorem direct_right_pos {n a k x y : Nat}
    (h : Direct n a k x y) (hk : 0<k) : 0<y := by
  induction h with
  | zero a k => exact hk
  | @succ n a k b c h ha hp hg ih => omega

private theorem allowed_back_step (a k n : Nat)
    (h : Allowed a k (n+1)) : Allowed a k n := by
  unfold Allowed at *
  have hpow : 1 ≤ 2^n := Nat.one_le_pow n 2 (by decide)
  have hc : 2 ≤ k+2 := by omega
  have hlow : 2 ≤ 2^n*(k+2) := by
    have he := Nat.mul_le_mul hpow hc
    simpa using he
  have he : 4 * 2^(n+1) * (k+2) = 8 * (2^n*(k+2)) := by
    calc
      4 * 2^(n+1) * (k+2) = (4*2)*(2^n*(k+2)) := by
        rw [Nat.pow_succ]
        ac_rfl
      _ = 8*(2^n*(k+2)) := by rfl
  rw [he] at h
  have he2 : 4*2^n*(k+2) = 4*(2^n*(k+2)) := by ac_rfl
  rw [he2]
  omega

private theorem allowed_back_all (a k n : Nat)
    (h : Allowed a k n) :
    ∀ i, i ≤ n → Allowed a k i := by
  induction n with
  | zero =>
      intro i hi
      have hh : i=0 := by omega
      simpa [hh] using h
  | succ n ih =>
      intro i hi
      by_cases he : i=n+1
      · simpa [he] using h
      · have hb := allowed_back_step a k n h
        exact ih hb i (by omega)

theorem direct_construct (r a k : Nat) (hk : 0<k)
    (ha : ∀ i, i<r → Allowed a k i) :
    ∃ x y, Direct r a k x y := by
  induction r with
  | zero => exact ⟨a,k,Direct.zero a k⟩
  | succ r ih =>
      obtain ⟨b,c,hb⟩ := ih (by intro i hi; exact ha i (by omega))
      have hc := direct_counter hb
      have hm := direct_mass hb
      have hd := ha r (by omega)
      have hpos := direct_right_pos hb hk
      have hguard : 2*c≤b := by
        unfold Allowed at hd
        have he : 4 * 2^r * (k+2) = 4 * (2^r*(k+2)) := by ac_rfl
        rw [he, ←hc] at hd
        omega
      exact ⟨b-2*c,2*c+2,Direct.succ hb (by omega) hpos hguard⟩

/-- Dyadic growth is superlinear from exponent two onward. -/
private theorem pow_two_ge_step (n : Nat) (hn : 2≤n) :
    n+2≤2^n := by
  induction n with
  | zero => omega
  | succ n ih =>
      by_cases h2 : 2≤n
      · have hp := ih h2
        rw [Nat.pow_succ]
        omega
      · have h1 : n=1 := by omega
        subst n
        decide

/-- All nontrivial direct epochs have an exponential length barrier. -/
theorem allowed_log_bound (a k r : Nat) (hk : 0<k)
    (hr : 2≤r) (h : Allowed a k r) :
    8*2^r ≤ a+2*k := by
  have hp := pow_two_ge_step r hr
  have hpow : 4*r+8 ≤4*2^r := by omega
  have hprod := Nat.mul_le_mul_left (4*2^r) (show 3≤k+2 by omega)
  have hthree : 12*2^r ≤4*2^r*(k+2) := by
    have he : 12*2^r = (4*2^r)*3 := by omega
    rw [he]
    exact hprod
  unfold Allowed at h
  omega

/-- A run of n≥3 direct returns needs mass at least 8·2^(n−1). -/
theorem direct_log_bound {n a k x y : Nat} (hk : 0<k)
    (hn : 3≤n) (h : Direct n a k x y) :
    8*2^(n-1) ≤ a+2*k := by
  have hn0 : 2≤n-1 := by omega
  have hn1 : n-1+1=n := by omega
  have hh : Direct (n-1+1) a k x y := by simpa [hn1] using h
  exact allowed_log_bound a k (n-1) hk hn0 (direct_last_allowed hh)

#print axioms allowed_log_bound
#print axioms direct_log_bound

/-- Necessary and sufficient single inequality for r+1 direct returns. -/
theorem direct_iff_last_guard (a k r : Nat) (hk : 0<k) :
    (∃x y, Direct (r+1) a k x y) ↔ Allowed a k r := by
  constructor
  · rintro ⟨x,y,h⟩
    exact direct_last_allowed h
  · intro hl
    exact direct_construct (r+1) a k hk
      (by intro i hi; exact allowed_back_all a k r hl i (by omega))

#print axioms direct_left_closed
#print axioms direct_unique
#print axioms direct_iff_last_guard
#print axioms direct_bounded
end BB6.Agent1Direct
