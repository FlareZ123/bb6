import Std

namespace BB6.Agent39Sheep

/-- Exactly the valuation-zero generic Sheep section transition, in backwards orientation. -/
def Parent0 (x y : Nat) : Prop :=
  5 ≤ x ∧ x % 2 = 1 ∧ 3*x = 2*y+1

inductive Chain0 : Nat → Nat → Nat → Prop where
  | nil (x : Nat) : Chain0 0 x x
  | cons {n x y z : Nat} (edge : Parent0 x y)
      (tail : Chain0 n y z) : Chain0 (n+1) x z

private theorem parent_offset {x y : Nat} (h : Parent0 x y) :
    3*(x-1)=2*(y-1) := by
  rcases h with ⟨hx,_,eq⟩
  omega

theorem chain_offset {h x y : Nat} (c : Chain0 h x y) :
    3^h * (x-1) = 2^h * (y-1) := by
  induction c with
  | nil x => simp
  | @cons n x y z edge tail ih =>
      have he := parent_offset edge
      calc
        3^(n+1) * (x-1) = 3^n * (3*(x-1)) := by simp [Nat.pow_succ, Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm]
        _ = 3^n * (2*(y-1)) := by rw [he]
        _ = 2*(2^n*(z-1)) := by rw [←ih]; ac_rfl
        _ = 2^(n+1)*(z-1) := by simp [Nat.pow_succ, Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm]

private theorem parent_from_power (n m : Nat) (hm : 4 ≤ 2^(n+1)*m) :
    Parent0 (1 + 2^(n+1)*m) (1+2^n*(3*m)) := by
  unfold Parent0
  have hp : 2^(n+1) = 2*2^n := by simp [Nat.pow_succ, Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm]
  constructor
  · omega
  constructor
  · rw [hp]
    simp only [Nat.mul_assoc]
    omega
  · rw [hp]
    simp [Nat.mul_add, Nat.add_mul, Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm]
    omega

theorem chain_from_power (h m : Nat) (hm : 4 ≤ 2^h*m) :
    Chain0 h (1+2^h*m) (1+3^h*m) := by
  induction h generalizing m with
  | zero => simpa using Chain0.nil (1+m)
  | succ n ih =>
      have hnew : 4 ≤ 2^n*(3*m) := by
        have hp : 2^(n+1)=2*2^n := by simp [Nat.pow_succ, Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm]
        rw [hp] at hm
        simp only [Nat.mul_assoc] at hm
        have hm2 : 2*(2^n*m) ≤ 3*(2^n*m) := by omega
        have hp2 : 2^n*(3*m) = 3*(2^n*m) := by ac_rfl
        rw [hp2]
        omega
      have step := parent_from_power n m hm
      have tail := ih (3*m) hnew
      simpa only [Nat.pow_succ, Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm] using (Chain0.cons step tail)

theorem chain_divisible {h x y : Nat} (c : Chain0 h x y) :
    3^h ∣ y-1 := by
  have hc := chain_offset c
  have hd : 3^h ∣ 2^h * (y-1) := ⟨x-1,hc.symm⟩
  have hcop : Nat.Coprime (3^h) (2^h) := by
    exact (by decide : Nat.Coprime 3 2).pow h h
  exact hcop.dvd_of_dvd_mul_left hd

theorem chain_factor {h x y : Nat} (c : Chain0 h x y) (hy : 1 ≤ y) :
    ∃ m : Nat, y=1+3^h*m ∧ x=1+2^h*m := by
  obtain ⟨m,hm⟩ := chain_divisible c
  have hy1 : y = 1 + (y-1) := by omega
  have hx : 1 ≤ x := by
    cases c with
    | nil _ => omega
    | cons edge _ => exact Nat.le_trans (by omega : 1≤5) edge.1
  have hf := chain_offset c
  have hn3 : 0 < 3^h := Nat.pow_pos (by omega)
  rw [hm] at hf
  have heq : x-1=2^h*m := by
    apply Nat.mul_left_cancel hn3
    simpa only [Nat.mul_assoc, Nat.mul_left_comm, Nat.mul_comm] using hf
  refine ⟨m, ?_, ?_⟩
  · omega
  · omega

theorem chain_exists_iff (h y : Nat) (hy : 5 ≤ y) :
    (∃ x, Chain0 h x y) ↔
    ∃ m, y=1+3^h*m ∧ 4 ≤ 2^h*m := by
  constructor
  · rintro ⟨x,hx⟩
    obtain ⟨m,heq,hx_eq⟩ := chain_factor hx (by omega)
    refine ⟨m,heq,?_⟩
    cases hx with
    | nil x => omega
    | cons edge tail =>
        have hge := edge.1
        omega
  · rintro ⟨m,heq,hm⟩
    refine ⟨1+2^h*m, ?_⟩
    rw [heq]
    exact chain_from_power h m hm

theorem source_large_of_divisible (h m : Nat)
    (hy : 5 ≤ 1+3^h*m) : 4 ≤ 2^h*m := by
  cases h with
  | zero =>
      simp only [Nat.pow_zero, Nat.one_mul] at hy ⊢
      omega
  | succ k =>
      cases k with
      | zero =>
          simp only [Nat.pow_succ, Nat.pow_zero, Nat.one_mul] at hy ⊢
          omega
      | succ k =>
          have hmp : 0 < m := by
            by_cases hz : m=0
            · simp [hz] at hy
            · omega
          have hp : 0 < 2^k := Nat.pow_pos (by decide)
          have hh : 4 ≤ 4*(2^k*m) := by
            have hpos : 0 < 2^k*m := Nat.mul_pos hp hmp
            omega
          have hpow : 2^(k+1+1)=4*2^k := by
            simp only [Nat.pow_succ]
            calc
              (2^k*2)*2 = (2*2)*2^k := by ac_rfl
              _ = 4*2^k := by rfl
          rw [hpow]
          simpa only [Nat.mul_assoc] using hh

/-- For every target at least five, the prescribed length of all-zero-valuation
    inverse corridor exists exactly at the 3-adic divisibility levels. -/
theorem chain_target_iff_divisible (h y : Nat) (hy : 5 ≤ y) :
    (∃ x, Chain0 h x y) ↔ 3^h ∣ y-1 := by
  constructor
  · rintro ⟨x,hx⟩
    exact chain_divisible hx
  · rintro ⟨m,hm⟩
    have he : y=1+3^h*m := by omega
    exact (chain_exists_iff h y hy).mpr ⟨m,he,source_large_of_divisible h m (by omega)⟩

private theorem chain_source_ge {h x y : Nat} (c : Chain0 h x y)
    (hh : 0<h) : 5 ≤ x := by
  cases c with
  | nil _ => omega
  | cons edge tail => exact edge.1

theorem chain_unique_source {h x x' y : Nat}
    (c : Chain0 h x y) (c' : Chain0 h x' y) : x=x' := by
  by_cases hh : h=0
  · subst h
    cases c
    cases c'
    rfl
  · have hx : 1 ≤ x := by
      have hge := chain_source_ge c (by omega)
      omega
    have hx' : 1 ≤ x' := by
      have hge := chain_source_ge c' (by omega)
      omega
    have hc := chain_offset c
    have hc' := chain_offset c'
    have h3 : 0 < 3^h := Nat.pow_pos (by decide)
    have he : x-1=x'-1 := Nat.mul_left_cancel h3 (hc.trans hc'.symm)
    omega

#print axioms BB6.Agent39Sheep.chain_target_iff_divisible
#print axioms BB6.Agent39Sheep.chain_unique_source
#print axioms BB6.Agent39Sheep.chain_exists_iff
end BB6.Agent39Sheep
