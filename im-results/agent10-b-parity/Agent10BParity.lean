import Lean.Elab.Tactic.Omega

namespace BB6.Agent10B

/-- Shifted Machine B scalar map, with x=z+8. -/
def T (x : Nat) : Nat := (3*x+7*(x%2))/2

def orbit : Nat → Nat → Nat
  | 0,x => x
  | n+1,x => orbit n (T x)

def SamePrefix (x y n : Nat) : Prop :=
  ∀ j : Nat, j < n → (orbit j x)%2=(orbit j y)%2

theorem two_T (x : Nat) : 2*T x = 3*x+7*(x%2) := by
  simp only [T]
  omega

theorem T_pos (x : Nat) (h:0<x) : x<T x := by
  have h2 := two_T x
  omega

theorem T_mono_parity (x y : Nat) (hle:x≤y)
  (hb:x%2=y%2) : T x ≤ T y := by
  have hx:=two_T x
  have hy:=two_T y
  omega

theorem T_difference (x y : Nat) (hle:x≤y)
  (hb:x%2=y%2) : 2*(T y-T x)=3*(y-x) := by
  have hx:=two_T x
  have hy:=two_T y
  have hm:=T_mono_parity x y hle hb
  omega

theorem prefix_div_pow_two (n : Nat) :
  ∀ x y : Nat, x≤y → SamePrefix x y n → 2^n ∣ y-x := by
  induction n with
  | zero =>
    intro x y hle hp
    simp
  | succ n ih =>
    intro x y hle hp
    have hb : x%2=y%2 := hp 0 (by omega)
    have hm : T x ≤ T y := T_mono_parity x y hle hb
    have htail : SamePrefix (T x) (T y) n := by
      intro j hj
      exact hp (j+1) (by omega)
    obtain ⟨q,hq⟩ := ih (T x) (T y) hm htail
    have heq : 3*(y-x)=2*(T y-T x) :=
      (T_difference x y hle hb).symm
    rw [hq] at heq
    have hdiv : 2^(n+1) ∣ 3*(y-x) := by
      refine ⟨q, ?_⟩
      calc
        3*(y-x)=2*(2^n*q) := heq
        _=2^(n+1)*q := by simp [Nat.pow_succ]; ac_rfl
    have hc : (2^(n+1)).Coprime 3 :=
      (show (2:Nat).Coprime 3 by decide).pow_left (n+1)
    exact hc.dvd_of_dvd_mul_left hdiv

theorem two_pow_gt (n : Nat) : n < 2^n := by
  induction n with
  | zero => decide
  | succ n ih =>
    rw [Nat.pow_succ]
    omega

theorem all_bits_equal_implies_equal (x y : Nat)
    (hb : ∀ n : Nat, (orbit n x)%2=(orbit n y)%2) : x=y := by
  rcases Nat.le_total x y with hle | hle
  · have hd := prefix_div_pow_two (y+1) x y hle
      (fun j hj => hb j)
    have hbnd : y-x < 2^(y+1) := by
      have ht:=two_pow_gt (y+1)
      omega
    have hz:=Nat.eq_zero_of_dvd_of_lt hd hbnd
    omega
  · have hd := prefix_div_pow_two (x+1) y x hle
      (fun j hj => (hb j).symm)
    have hbnd : x-y < 2^(x+1) := by
      have ht:=two_pow_gt (x+1)
      omega
    have hz:=Nat.eq_zero_of_dvd_of_lt hd hbnd
    omega

theorem orbit_add (m n x : Nat) :
    orbit (m+n) x = orbit n (orbit m x) := by
  induction m generalizing x with
  | zero => simp [orbit]
  | succ m ih =>
    have heq : (m+1)+n=(m+n)+1 := by omega
    rw [heq,orbit,ih]
    rfl

theorem orbit_ge (n x : Nat) : x ≤ orbit n x := by
  induction n generalizing x with
  | zero => exact Nat.le_refl _
  | succ n ih =>
    change x ≤ orbit n (T x)
    have h : x ≤ T x := by
      by_cases hx : x=0
      · subst x
        decide
      · have hx' : 0<x := by omega
        have hgt:=T_pos x hx'
        omega
    exact Nat.le_trans h (ih (T x))

theorem orbit_lt (n x : Nat) (hn : 0<n) (hx:0<x) : x < orbit n x := by
  rcases n with _ | n
  · omega
  · change x < orbit n (T x)
    have hstrict:=T_pos x hx
    have hle:=orbit_ge n (T x)
    omega

theorem parity_orbit_aperiodic (x n p : Nat) (hx : 0<x) (hp : 0<p) :
    ¬ (∀ k : Nat,
      (orbit (n+k) x)%2 = (orbit (n+k+p) x)%2) := by
  intro hperiod
  have hbits : ∀ k : Nat,
    (orbit k (orbit n x))%2=(orbit k (orbit (n+p) x))%2 := by
    intro k
    rw [←orbit_add n k x,←orbit_add (n+p) k x]
    have hper:=hperiod k
    have heq : n+p+k=n+k+p := by omega
    rwa [heq]
  have heq := all_bits_equal_implies_equal (orbit n x) (orbit (n+p) x) hbits
  have hl : orbit n x < orbit (n+p) x := by
    rw [orbit_add n p x]
    apply orbit_lt p (orbit n x) hp
    have hh:=orbit_ge n x
    omega
  omega

/-- Exact copy of Agent 18's standalone scalar map. -/
def G (z : Nat) : Nat := 3*(z/2)+4+5*(z%2)

def iterG : Nat → Nat → Nat
  | 0,z => z
  | n+1,z => iterG n (G z)

theorem shifted_G (z : Nat) : T (z+8)=G z+8 := by
  have h:=two_T (z+8)
  simp only [G]
  omega

theorem orbit_shifted (n z : Nat) :
    orbit n (z+8)=iterG n z+8 := by
  induction n generalizing z with
  | zero => rfl
  | succ n ih =>
    change orbit n (T (z+8))=iterG n (G z)+8
    rw [shifted_G]
    exact ih (G z)

/-- The actual Agent 18 B scalar parity word is never eventually periodic. -/
theorem B_scalar_bits_aperiodic (n p : Nat) (hp : 0<p) :
    ¬ (∀ k : Nat,
      (iterG (n+k) 0)%2=(iterG (n+k+p) 0)%2) := by
  intro h
  apply parity_orbit_aperiodic 8 n p (by omega) hp
  intro k
  have h1 := orbit_shifted (n+k) 0
  have h2 := orbit_shifted (n+k+p) 0
  have hh:=h k
  simp only [Nat.zero_add] at h1 h2
  omega

#print axioms shifted_G
#print axioms B_scalar_bits_aperiodic
#print axioms orbit_add
#print axioms parity_orbit_aperiodic
#print axioms prefix_div_pow_two
#print axioms all_bits_equal_implies_equal
end BB6.Agent10B
