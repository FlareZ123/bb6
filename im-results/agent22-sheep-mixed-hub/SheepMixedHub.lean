module
public import Std

@[expose] public section
namespace BB6.SheepMixedHub

inductive GenericStep : Nat → Nat → Prop where
  | ofOdd (a u : Nat) (hOdd : u % 2 = 1) (hu : 5 ≤ u) :
      GenericStep (2^a*u) (2^a*u+a+(u-1)/2)

private theorem pow_even (p : Nat) (hp : 1 ≤ p) : (2^p)%2=0 := by
  cases p with
  | zero => omega
  | succ p => rw [Nat.pow_succ]; simp

private theorem pow_three_odd (k : Nat) : (3^k)%2=1 := by
  induction k with
  | zero => decide
  | succ k ih => rw [Nat.pow_succ, Nat.mul_mod, ih]

/-- For any modulus 2^p*q (p>0, q positive odd), the synthetic Sheep
section graph has a genuine generic even-to-even edge from residue 0
to each even target residue. Source states need not be blank-reachable. -/
theorem zero_hub_any_odd (p q s : Nat) (hp : 1 ≤ p)
    (hq : 0 < q) (hqodd : q%2=1)
    (hs : s < 2^p * q) (he : s%2=0) :
    ∃ x y : Nat, x % (2^p*q) = 0 ∧
      y % (2^p*q) = s ∧ x%2=0 ∧ y%2=0 ∧ GenericStep x y := by
  let m := 2^p*q
  let u := 5*q
  let c := (u-1)/2
  let L := p+c+1
  let b := s + m*L - (p+c)
  let a := p+b
  let x := 2^a*u
  let y := x+a+c
  have hm : 0<m := by
    dsimp [m]
    exact Nat.mul_pos (Nat.pow_pos (by decide)) hq
  have hL : L ≤ m*L := by
    have h := Nat.mul_le_mul_right L (show 1≤m by omega)
    simpa [Nat.mul_comm] using h
  have hpc : p+c ≤ m*L := by
    have hdef : L=p+c+1 := rfl
    omega
  have hb : p+c+b=s+m*L := by dsimp only [b]; omega
  have hodd : u%2=1 := by
    dsimp [u]
    simp [Nat.mul_mod, hqodd]
  have hu : 5≤u := by
    dsimp [u]
    omega
  have hx : x=m*(2^b*5) := by
    dsimp [x,a,m,u]
    rw [Nat.pow_add]
    ac_rfl
  have hy : y=x+s+m*L := by dsimp [y,a]; omega
  have hmeven : m%2=0 := by
    dsimp [m]
    simp [Nat.mul_mod, pow_even p hp]
  have hxeven : x%2=0 := by rw [hx]; simp [Nat.mul_mod, hmeven]
  have hyeven : y%2=0 := by
    have hml : (m*L)%2=0 := by simp [Nat.mul_mod, hmeven]
    rw [hy]
    omega
  have hxmod : x%m=0 := by rw [hx]; simp
  have hymod : y%m=s := by
    rw [hy,hx]
    have hh : m*(2^b*5)+s+m*L = s+m*(2^b*5+L) := by
      simp only [Nat.mul_add]; omega
    rw [hh]
    exact (Nat.add_mul_mod_self_left s m (2^b*5+L)).trans (Nat.mod_eq_of_lt (show s<m by simpa [m] using hs))
  have hsStep : GenericStep x y := by
    simpa [x,y,a,c] using GenericStep.ofOdd a u hodd hu
  exact ⟨x,y,by simpa [m] using hxmod,by simpa [m] using hymod,
    hxeven,hyeven,hsStep⟩

/-- Mixed 2-adic/3-adic specialization. -/
theorem zero_hub_mixed (p k s : Nat) (hp : 1 ≤ p)
    (hs : s < 2^p * 3^k) (he : s%2=0) :
    ∃ x y : Nat, x % (2^p*3^k) = 0 ∧
      y % (2^p*3^k) = s ∧ x%2=0 ∧ y%2=0 ∧ GenericStep x y := by
  have hq : 0<3^k := Nat.pow_pos (by decide)
  have hqodd : (3^k)%2=1 := pow_three_odd k
  exact zero_hub_any_odd p (3^k) s hp hq hqodd hs he

/-- A residue predicate containing zero and globally closed under all legal
even-to-even generic edges must contain every even residue. -/
theorem zero_forces_even_residues (p q : Nat)
    (hp : 1 ≤ p) (hq : 0<q) (hqodd : q%2=1)
    (A : Nat → Prop) (hz : A 0)
    (hclosed : ∀ x y, x%2=0 → y%2=0 → GenericStep x y →
      A (x%(2^p*q)) → A (y%(2^p*q))) :
    ∀ s, s<2^p*q → s%2=0 → A s := by
  intro s hs he
  obtain ⟨x,y,hx,hy,hxe,hye,hedge⟩ :=
    zero_hub_any_odd p q s hp hq hqodd hs he
  exact hy ▸ hclosed x y hxe hye hedge (hx ▸ hz)

#print axioms zero_hub_any_odd
#print axioms zero_hub_mixed
#print axioms zero_forces_even_residues
end BB6.SheepMixedHub
