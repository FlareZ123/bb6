import Lean.Elab.Tactic.Omega
namespace ThreeAdic

private theorem mod_small (m x : Nat) (hm : 0<m) (hx : x<3*m) :
    (x<m ∧ x%m=x) ∨
    (m≤x ∧ x<2*m ∧ x%m=x-m) ∨
    (2*m≤x ∧ x%m=x-2*m) := by
  by_cases h0 : x<m
  · exact Or.inl ⟨h0, Nat.mod_eq_of_lt h0⟩
  · by_cases h1 : x<2*m
    · right; left
      refine ⟨by omega, h1, ?_⟩
      rw [Nat.mod_eq_sub_mod (by omega : x≥m)]
      exact Nat.mod_eq_of_lt (by omega : x-m<m)
    · right; right
      constructor
      · omega
      · rw [Nat.mod_eq_sub_mod (by omega : x≥m)]
        rw [Nat.mod_eq_sub_mod (by omega : x-m≥m)]
        rw [Nat.mod_eq_of_lt (by omega : x-m-m<m)]
        omega

private theorem mod_shift2 (m x : Nat) (hm : 0<m) (hx : x<3*m) :
    (x<m ∧ (x+2*m)%(3*m)=x+2*m) ∨
    (m≤x ∧ (x+2*m)%(3*m)=x-m) := by
  by_cases h0 : x<m
  · left
    exact ⟨h0, Nat.mod_eq_of_lt (by omega)⟩
  · right
    constructor
    · omega
    · rw [Nat.mod_eq_sub_mod (by omega : x+2*m≥3*m)]
      rw [Nat.mod_eq_of_lt (by omega : x+2*m-3*m<3*m)]
      omega

private theorem mod_shift4 (m x : Nat) (hm : 0<m) (hx : x<3*m) :
    (x<2*m ∧ (x+4*m)%(3*m)=x+m) ∨
    (2*m≤x ∧ (x+4*m)%(3*m)=x-2*m) := by
  by_cases h0 : x<2*m
  · left
    constructor
    · exact h0
    · rw [Nat.mod_eq_sub_mod (by omega : x+4*m≥3*m)]
      rw [Nat.mod_eq_of_lt (by omega : x+4*m-3*m<3*m)]
      omega
  · right
    constructor
    · omega
    · rw [Nat.mod_eq_sub_mod (by omega : x+4*m≥3*m)]
      rw [Nat.mod_eq_sub_mod (by omega : x+4*m-3*m≥3*m)]
      rw [Nat.mod_eq_of_lt (by omega : x+4*m-3*m-3*m<3*m)]
      omega

theorem triple_bounded (m x y : Nat) (hm : 0 < m)
    (hx : x < 3*m) (hy : y < 3*m) (h : x % m = y % m) :
    x=y ∨ (x+2*m)%(3*m)=y ∨ (x+4*m)%(3*m)=y := by
  rcases mod_small m x hm hx with xx | xx | xx <;>
  rcases mod_small m y hm hy with yy | yy | yy <;>
  rcases mod_shift2 m x hm hx with x2 | x2 <;>
  rcases mod_shift4 m x hm hx with x4 | x4 <;>
  omega

theorem mod_add_six (m x : Nat) :
  (x+6*m)%(3*m)=x%(3*m) := by
  have heq : 6*m = (3*m)*2 := by omega
  rw [heq, Nat.add_mod]
  simp

theorem shift_to_plus (m x y : Nat)
   (h : (x+2*m)%(3*m)=y%(3*m)) :
   x%(3*m)=(y+4*m)%(3*m) := by
  have h' := congrArg (fun t => (t+4*m)%(3*m)) h
  rw [Nat.mod_add_mod, Nat.mod_add_mod] at h'
  rw [show x+2*m+4*m=x+6*m by omega, mod_add_six] at h'
  exact h'

theorem one_step_lift (F : Nat → Nat) (n0 r m : Nat) (hm:0<m)
    (hshift : ∀ n, (F (n+2*m)+2*m)%(3*m)=F n%(3*m))
    (hbase : ∃ n, n0≤n ∧ n≤n0+2*(m-1) ∧ F n%m=r%m) :
    ∃ n, n0≤n ∧ n≤n0+2*(3*m-1) ∧ F n%(3*m)=r%(3*m) := by
  obtain ⟨n,hn0,hnbound,heq⟩ := hbase
  have hx : F n % (3*m) % m = F n %m := Nat.mod_mul_left_mod (F n) 3 m
  have hy : r % (3*m) % m = r%m := Nat.mod_mul_left_mod r 3 m
  have hmod : (F n%(3*m))%m=(r%(3*m))%m := by omega
  have hxlt : F n%(3*m)<3*m := Nat.mod_lt _ (by omega)
  have hylt : r%(3*m)<3*m := Nat.mod_lt _ (by omega)
  have cases := triple_bounded m (F n%(3*m)) (r%(3*m)) hm hxlt hylt hmod
  have hp : F (n+2*m)%(3*m)=(F n+4*m)%(3*m) :=
    shift_to_plus m (F (n+2*m)) (F n) (hshift n)
  have hp2raw : F (n+4*m)%(3*m)=(F (n+2*m)+4*m)%(3*m) := by
    have t := hshift (n+2*m)
    have h := shift_to_plus m (F (n+2*m+2*m)) (F (n+2*m)) t
    simpa [show n+2*m+2*m=n+4*m by omega] using h
  have hp2 : F (n+4*m)%(3*m)=(F n+2*m)%(3*m) := by
    calc
      _ = (F (n+2*m)+4*m)%(3*m) := hp2raw
      _ = (F (n+2*m)%(3*m)+4*m)%(3*m) := (Nat.mod_add_mod _ _ _).symm
      _ = ((F n+4*m)%(3*m)+4*m)%(3*m) := by rw [hp]
      _ = (F n+4*m+4*m)%(3*m) := Nat.mod_add_mod _ _ _
      _ = (F n+2*m+6*m)%(3*m) := by congr 1; omega
      _ = (F n+2*m)%(3*m) := mod_add_six m (F n+2*m)
  rcases cases with h0 | h2 | h4
  · refine ⟨n,hn0,by omega,?_⟩
    simpa [Nat.mod_mod] using h0
  · refine ⟨n+4*m,by omega,by omega,?_⟩
    rw [hp2]
    simpa only [Nat.mod_add_mod,Nat.mod_mod] using h2
  · refine ⟨n+2*m,by omega,by omega,?_⟩
    rw [hp]
    simpa only [Nat.mod_add_mod,Nat.mod_mod] using h4

theorem all_residues (F : Nat → Nat) (n0 : Nat)
    (hshift : ∀ e n, (F (n+2*3^e)+2*3^e)%(3^(e+1))=F n%(3^(e+1))) :
    ∀ e r, ∃ n, n0≤n ∧ n≤n0+2*(3^e-1) ∧ F n%(3^e)=r%(3^e) := by
  intro e
  induction e with
  | zero =>
      intro r
      refine ⟨n0,by omega,by simp,?_⟩
      omega
  | succ e ih =>
      intro r
      have hm : 0<3^e := Nat.pow_pos (by omega)
      have hs : ∀ n, (F (n+2*3^e)+2*3^e)%(3*(3^e))=F n%(3*(3^e)) := by
        intro n
        simpa only [Nat.pow_succ', Nat.pow_add_one, Nat.mul_comm] using hshift e n
      have ht := one_step_lift F n0 r (3^e) hm hs (ih r)
      simpa only [Nat.pow_succ', Nat.pow_add_one, Nat.mul_comm] using ht

theorem cube_lift (m x : Nat) (hm:0<m) (h3:3 ∣ m)
    (hmod:x%m=1) : x^3%(3*m)=1 := by
  obtain ⟨s,hs⟩ := h3
  have hspos : 0<s := by rw [hs] at hm; omega
  have hx : x=1+m*(x/m) := by
    calc
      x = x%m + m*(x/m) := (Nat.mod_add_div x m).symm
      _ = 1+m*(x/m) := by rw [hmod]
  have hpoly (s q : Nat) : (1+3*s*q)^3=
      1+(3*(3*s))*(q+3*s*q*q+3*s*s*q*q*q) := by
    grind +ring
  rw [hx,hs]
  rw [hpoly]
  rw [Nat.add_mod]
  simp [Nat.mul_mod]
  exact Nat.mod_eq_of_lt (by omega)

theorem power_period : ∀ e : Nat, (2^(2*3^e))%(3^(e+1))=1 := by
  intro e
  induction e with
  | zero => decide
  | succ e ih =>
      let m := 3^(e+1)
      have hm : 0<m := Nat.pow_pos (by omega)
      have h3 : 3 ∣ m := by
        refine ⟨3^e,?_⟩
        simp only [m, Nat.pow_add_one]
        omega
      have ht := cube_lift m (2^(2*3^e)) hm h3 ih
      have hpow : (2^(2*3^e))^3=2^(2*3^(e+1)) := by
        calc
          _ = 2^((2*3^e)*3) := (Nat.pow_mul 2 (2*3^e) 3).symm
          _ = 2^(2*3^(e+1)) := by
             congr 1
             simp only [Nat.pow_succ']
             omega
      rw [hpow] at ht
      simpa only [m, Nat.pow_succ', Nat.pow_add_one,Nat.mul_comm] using ht

theorem shift_two_power (e t : Nat) :
    (2^(t+2*3^e))%(3^(e+1))=2^t%(3^(e+1)) := by
  rw [Nat.pow_add, Nat.mul_mod, power_period e]
  simp [Nat.mod_mod]

#print axioms shift_two_power
#print axioms power_period
#print axioms all_residues

end ThreeAdic
