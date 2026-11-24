import Lean
namespace CascadePeriodic

/-- An infinite integral sequence cannot absorb repeated division by an
    even multiplier with an odd numerator, unless it is identically zero. -/
theorem even_odd_geometric_zero (P R : Int) (hp : P % 2 = 0)
    (hr : R % 2 = 1) (x : Nat → Int)
    (hx : ∀ j, P * x (j+1) = R * x j) : ∀ j, x j = 0 := by
  have allDiv (m : Nat) : ∀ (y : Nat → Int),
      (∀ j, P * y (j+1) = R * y j) → ∀ j, (2:Int)^m ∣ y j := by
    induction m with
    | zero => simp
    | succ m ih =>
      intro y hy j
      have heven (i : Nat) : y i % 2 = 0 := by
        have hmod := congrArg (fun z : Int => z % 2) (hy i)
        change (P * y (i+1)) % 2 = (R * y i) % 2 at hmod
        rw [Int.mul_emod P, Int.mul_emod R, hp, hr] at hmod
        simpa using hmod.symm
      let z : Nat → Int := fun i => y i / 2
      have hyz (i : Nat) : y i = 2 * z i := by
        dsimp [z]
        have := heven i
        omega
      have hz (i : Nat) : P * z (i+1) = R * z i := by
        have hh := hy i
        rw [hyz (i+1), hyz i] at hh
        have hh' : 2 * (P * z (i+1)) = 2 * (R * z i) := by
          calc
            2 * (P * z (i+1)) = P * (2 * z (i+1)) := by ac_rfl
            _ = R * (2 * z i) := hh
            _ = 2 * (R * z i) := by ac_rfl
        omega
      obtain ⟨q,hq⟩ := ih z hz j
      refine ⟨q,?_⟩
      rw [hyz j, hq, Int.pow_succ]
      ac_rfl
  intro j
  by_cases hne : x j = 0
  · exact hne
  have habs : 0 < (x j).natAbs := Int.natAbs_pos.mpr hne
  have hd := allDiv (x j).natAbs x hx j
  have hnat := Int.natAbs_dvd_natAbs.mpr hd
  have hpow : ((2:Int)^(x j).natAbs).natAbs = 2^(x j).natAbs := by
    rw [Int.natAbs_pow]
    rfl
  rw [hpow] at hnat
  have := Nat.le_of_dvd habs hnat
  have := Nat.lt_two_pow_self (n := (x j).natAbs)
  omega

def denominator (P R G : Int) : Int := (P*G-R)*(P-R)^2

def numerator (P R G S C E D z k : Int) : Int :=
  S*(P-R)^2*z + C*(P*G-R)*(P-R)*k +
    (E*(P-R)-P*C*D)*(P*G-R)

theorem affine_rigidity (P R G S C E D : Int) (hp : P % 2 = 0)
    (hr : R % 2 = 1) (x z k : Nat → Int)
    (hz : ∀ j, z (j+1) = G*z j) (hk : ∀ j, k (j+1) = k j+D)
    (hx : ∀ j, P*x (j+1) = R*x j+S*z j+C*k j+E) :
    ∀ j, denominator P R G * x j = numerator P R G S C E D (z j) (k j) := by
  let y : Nat → Int := fun j => denominator P R G * x j -
    numerator P R G S C E D (z j) (k j)
  have hy (j : Nat) : P*y (j+1) = R*y j := by
    dsimp [y]
    rw [hz j, hk j]
    have hs : P * numerator P R G S C E D (G*z j) (k j+D) =
        R * numerator P R G S C E D (z j) (k j) +
        denominator P R G * (S*z j+C*k j+E) := by
      unfold numerator denominator
      grind
    have hf : P*(denominator P R G*x (j+1)) =
        denominator P R G*(R*x j+S*z j+C*k j+E) := by
      rw [← Int.mul_assoc, Int.mul_comm P (denominator P R G), Int.mul_assoc, hx j]
    rw [Int.mul_sub, hf, hs]
    grind
  have hzero := even_odd_geometric_zero P R hp hr y hy
  intro j
  have hj := hzero j
  dsimp [y] at hj
  omega

theorem affine_second_difference (P R G S C E D : Int) (hp : P % 2 = 0)
    (hr : R % 2 = 1) (x z k : Nat → Int)
    (hz : ∀ j, z (j+1) = G*z j) (hk : ∀ j, k (j+1) = k j+D)
    (hx : ∀ j, P*x (j+1) = R*x j+S*z j+C*k j+E) :
    ∀ j, denominator P R G ∣ S*(P-R)^2*z j*(G-1)^2 := by
  intro j
  have h := affine_rigidity P R G S C E D hp hr x z k hz hk hx
  have h0 := h j
  have h1 := h (j+1)
  have h2 := h (j+2)
  rw [show j+2=j+1+1 by omega, hz (j+1), hz j, hk (j+1), hk j] at h2
  rw [hz j,hk j] at h1
  refine ⟨x (j+1+1)-2*x (j+1)+x j,?_⟩
  calc
    S*(P-R)^2*z j*(G-1)^2 =
        numerator P R G S C E D (G*(G*z j)) (k j+D+D) -
          2*numerator P R G S C E D (G*z j) (k j+D) +
          numerator P R G S C E D (z j) (k j) := by
      unfold numerator
      clear h0 h1 h2 h hx hz hk
      grind
    _ = denominator P R G*x (j+1+1) -
          2*(denominator P R G*x (j+1)) + denominator P R G*x j := by
      rw [←h2,←h1,←h0]
    _ = denominator P R G*(x (j+1+1)-2*x (j+1)+x j) := by
      clear h0 h1 h2 h hx hz hk
      grind

theorem affine_exponential_divisibility (P R G S C E D : Int)
    (hp : P % 2 = 0) (hr : R % 2 = 1) (x z k : Nat → Int)
    (hz : ∀ j, z (j+1) = G*z j) (hk : ∀ j, k (j+1) = k j+D)
    (hx : ∀ j, P*x (j+1) = R*x j+S*z j+C*k j+E) :
    ∀ j, P*G-R ∣ S*z j*(G-1)^2 := by
  intro j
  obtain ⟨q,hq⟩ := affine_second_difference P R G S C E D hp hr x z k hz hk hx j
  have hne : P-R ≠ 0 := by omega
  have hp2 : (P-R)^2 ≠ 0 := Int.pow_ne_zero hne
  refine ⟨q,?_⟩
  unfold denominator at hq
  have hc : (P-R)^2*(S*z j*(G-1)^2) = (P-R)^2*((P*G-R)*q) := by
    calc
      (P-R)^2*(S*z j*(G-1)^2) = S*(P-R)^2*z j*(G-1)^2 := by ac_rfl
      _ = (P*G-R)*(P-R)^2*q := hq
      _ = (P-R)^2*((P*G-R)*q) := by ac_rfl
  exact (Int.mul_eq_mul_left_iff hp2).mp hc

#print axioms even_odd_geometric_zero
#print axioms affine_rigidity
#print axioms affine_second_difference
#print axioms affine_exponential_divisibility
end CascadePeriodic
