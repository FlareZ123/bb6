import Std

namespace SheepHubs

/-- Every odd linear coefficient is invertible on the additive residues modulo a
power of two. Constructively lifted one binary digit at a time. -/
theorem odd_affine_root (k A C : Nat) (hc : C % 2 = 1) :
    ∃ t : Nat, 2^k ∣ A + C*t := by
  induction k with
  | zero =>
      exact ⟨0, by simp⟩
  | succ k ih =>
      obtain ⟨t, ht⟩ := ih
      obtain ⟨j,hj⟩ := ht
      have hpower : (2:Nat)^(k+1)=2*2^k := by
        rw [Nat.pow_succ]
        omega
      by_cases he : j%2=0
      · obtain ⟨v,hv⟩ : 2 ∣ j := (Nat.dvd_iff_mod_eq_zero).mpr he
        refine ⟨t, ⟨v, ?_⟩⟩
        rw [hpower]
        calc
          A+C*t = 2^k*j := hj
          _ = 2^k*(2*v) := by rw [hv]
          _ = (2*2^k)*v := by ac_rfl
      · have hodd : j%2=1 := by omega
        have heven : (j+C)%2=0 := by omega
        obtain ⟨v,hv⟩ : 2 ∣ j+C := (Nat.dvd_iff_mod_eq_zero).mpr heven
        refine ⟨t+2^k,⟨v,?_⟩⟩
        rw [hpower]
        calc
          A+C*(t+2^k)=A+C*t+C*2^k := by simp only [Nat.mul_add]; omega
          _ = 2^k*j+C*2^k := by rw [hj]
          _ = 2^k*(j+C) := by rw [Nat.mul_add]; ac_rfl
          _ = 2^k*(2*v) := by rw [hv]
          _ = (2*2^k)*v := by ac_rfl

/-- Choose the modular root at any prescribed nonnegative lower bound. -/
theorem odd_affine_root_unbounded (k A C N : Nat) (hc : C % 2 = 1) :
    ∃ t : Nat, N ≤ t ∧ 2^k ∣ A + C*t := by
  obtain ⟨t,ht⟩ := odd_affine_root k A C hc
  refine ⟨t+2^k*N, ?_, ?_⟩
  · have hp : 1 ≤ (2:Nat)^k := by
      have hpos : 0 < (2:Nat)^k := Nat.pow_pos (by decide)
      omega
    have hb := Nat.mul_le_mul_right N hp
    omega
  have heq : A+C*(t+2^k*N)=(A+C*t)+2^k*(C*N) := by
    rw [Nat.mul_add]
    ac_rfl
  rw [heq]
  exact Nat.dvd_add ht (Nat.dvd_mul_right _ _)

#print axioms odd_affine_root
end SheepHubs

namespace SheepHubs

/-- Every generic source with a sufficiently long odd block has an entire
2-adic congruence class of synthetic source lifts that return to 0 modulo
2^(a+L+1).  The Lean statement retains the exact legal generic transition
Diophantine equation rather than using an unverified symbolic E definition. -/
theorem generic_hub_lift (a L n u W N : Nat)
    (hu : 5 ≤ u) (huodd : u%2=1) (hnodd : n%2=1)
    (heq : 2*(1+2^L*W)+1 = (2^(a+1)+1)*u+2*a) :
    ∃ t : Nat,
      N ≤ t ∧
      let V := u+2^(L+1)*n*t
      let Q := W+(2^(a+1)+1)*n*t
      5≤V ∧ V%2=1 ∧ Q%2=1 ∧
      2*(1+2^L*Q)+1=(2^(a+1)+1)*V+2*a ∧
      2^(a+L+1) ∣ 1+3^L*Q ∧
      2^a*V=2^a*u+2^(a+L+1)*n*t := by
  have h3 : 3^L %2=1 := by
    rw [Nat.pow_mod]
    simp
  have h2 : (2:Nat)^(a+1)%2=0 := by
    rw [Nat.pow_succ]
    omega
  have hM : (2^(a+1)+1)%2=1 := by
    rw [Nat.add_mod]
    simp [h2]
  have hc : (3^L*(2^(a+1)+1)*n)%2=1 := by
    simp [Nat.mul_mod,h3,hM,hnodd]
  obtain ⟨t,htN,ht⟩ := odd_affine_root_unbounded (a+L+1)
    (1+3^L*W) (3^L*(2^(a+1)+1)*n) N hc
  let V := u+2^(L+1)*n*t
  let Q := W+(2^(a+1)+1)*n*t
  have hpow : (2:Nat)^(L+1)=2*2^L := by rw [Nat.pow_succ]; omega
  have hvodd : V%2=1 := by
    have heven : 2^(L+1)*n*t%2=0 := by
      rw [hpow]
      simp [Nat.mul_mod]
    dsimp [V]
    rw [Nat.add_mod,huodd,heven]
  have hdiv : 2^(a+L+1) ∣ 1+3^L*Q := by
    have hsame : 1+3^L*Q = (1+3^L*W)+(3^L*(2^(a+1)+1)*n)*t := by
      dsimp [Q]
      calc
        1+3^L*(W+(2^(a+1)+1)*n*t)
            = 1+(3^L*W+3^L*((2^(a+1)+1)*n*t)) := by rw [Nat.mul_add]
        _ = (1+3^L*W)+(3^L*(2^(a+1)+1)*n)*t := by ac_rfl
    rwa [hsame]
  have htwo : 2 ∣ 2^(a+L+1) := by
    have he : a+L+1= (a+L)+1 := by omega
    rw [he,Nat.pow_succ]
    exact ⟨2^(a+L), by ac_rfl⟩
  have heven : (1+3^L*Q)%2=0 := Nat.mod_eq_zero_of_dvd (Nat.dvd_trans htwo hdiv)
  have hqodd : Q%2=1 := by
    rw [Nat.add_mod, Nat.mul_mod,h3] at heven
    omega
  have hformula : 2*(1+2^L*Q)+1=(2^(a+1)+1)*V+2*a := by
    dsimp [V,Q]
    have hterm : 2*(2^L*((2^(a+1)+1)*n*t)) =
          (2^(a+1)+1)*(2^(L+1)*n*t) := by
      rw [hpow]
      ac_rfl
    calc
      2*(1+2^L*(W+(2^(a+1)+1)*n*t))+1
          = (2*(1+2^L*W)+1)+2*(2^L*((2^(a+1)+1)*n*t)) := by
              simp only [Nat.mul_add]
              ac_rfl
      _ = (2^(a+1)+1)*u+2*a+(2^(a+1)+1)*(2^(L+1)*n*t) := by
              rw [hterm,heq]
      _ = (2^(a+1)+1)*(u+2^(L+1)*n*t)+2*a := by
              rw [Nat.mul_add]
              omega
  have hsource : 2^a*V=2^a*u+2^(a+L+1)*n*t := by
    dsimp [V]
    have hexp : 2^(a+L+1) = 2^a*2^(L+1) := by
      rw [show a+L+1=a+(L+1) by omega, Nat.pow_add]
    rw [hexp]
    simp only [Nat.mul_add]
    ac_rfl
  refine ⟨t, htN, ?_, hvodd, hqodd, hformula, hdiv, hsource⟩
  omega

#print axioms generic_hub_lift
end SheepHubs
