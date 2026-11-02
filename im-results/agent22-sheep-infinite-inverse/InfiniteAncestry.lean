import SheepPowerBridge
namespace BB6.Agent22.InfiniteAncestry

private theorem cube_shift (z : Nat) :
    (z+1)^3 = 1 + z * ((z+1)*(z+1)+(z+1)+1) := by
  simp only [Nat.pow_succ, Nat.pow_zero, Nat.mul_one,
             Nat.add_mul, Nat.mul_add, Nat.one_mul]
  simp only [Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm]
  omega

private theorem div_three_factor (y : Nat) :
    ((3*y+1)*(3*y+1)+(3*y+1)+1) = 3*(1+3*y+y*(3*y)) := by
  simp only [Nat.add_mul, Nat.mul_add, Nat.one_mul, Nat.mul_one]
  simp only [Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm]
  omega

private theorem cube_three (y : Nat) :
    (1+3*y)^3 = 1+9*y*(1+3*y+y*(3*y)) := by
  have hs:=cube_shift (3*y)
  have hfactor:=div_three_factor y
  have hc : 3*y+1=1+3*y := by omega
  rw [hc] at hs
  rw [hc] at hfactor
  rw [hfactor] at hs
  have hh : 9*y*(1+3*y+y*(3*y)) =
      (3*y)*(3*(1+3*y+y*(3*y))) := by
    have hn : 9=3*3 := rfl
    rw [hn]
    ac_rfl
  rwa [hh]

private theorem cube_lift (k q : Nat) :
    (1+3^(k+1)*q)^3 =
    1+3^(k+2)*(q*(1+3*(3^k*q)+(3^k*q)*(3*(3^k*q)))) := by
  have h1 : 3^(k+1) = 3*3^k := by rw [Nat.pow_succ]; omega
  have h2 : 3^(k+2) = 9*3^k := by
    have h : k+2=k+1+1 := by omega
    rw [h,Nat.pow_succ,Nat.pow_succ]
    omega
  rw [h1,h2]
  have he : 1+(3*3^k)*q = 1+3*(3^k*q) := by ac_rfl
  rw [he]
  rw [cube_three (3^k*q)]
  congr 1
  ac_rfl

/-- Exact quotient witnessing the 3-adic exponent-lifting identity. -/
def Q : Nat → Nat
  | 0 => 1
  | k+1 =>
    Q k * (1 + 3*(3^k*Q k) + (3^k*Q k)*(3*(3^k*Q k)))

/-- 2^(2·3^k) is one modulo 3^(k+1), with explicit integral quotient. -/
theorem power_three_lifting (k : Nat) :
    2^(2*3^k) = 1 + 3^(k+1)*Q k := by
  induction k with
  | zero => decide
  | succ k ih =>
    have hp : 2*(3^(k+1)) = (2*3^k)*3 := by
      rw [Nat.pow_succ]
      omega
    calc
      2^(2*3^(k+1)) = (2^(2*3^k))^3 := by
        rw [hp,Nat.pow_mul]
      _ = (1+3^(k+1)*Q k)^3 := by rw [ih]
      _ = 1+3^(k+2)*(Q k*(1+3*(3^k*Q k)+(3^k*Q k)*(3*(3^k*Q k)))) :=
        cube_lift k (Q k)
      _ = 1+3^((k+1)+1)*Q (k+1) := by rfl

theorem Q_pos (k : Nat) : 0 < Q k := by
  induction k with
  | zero => decide
  | succ k ih =>
    simp only [Q]
    apply Nat.mul_pos ih
    omega

theorem Q_step_ge_four (k : Nat) : 4 ≤ Q (k+1) := by
  change 4 ≤ Q k * (1+3*(3^k*Q k)+(3^k*Q k)*(3*(3^k*Q k)))
  have hp : 0<3^k := Nat.pow_pos (by decide)
  have hq : 0<Q k := Q_pos k
  have hy : 0<3^k*Q k := Nat.mul_pos hp hq
  have h4 : 4 ≤ 1+3*(3^k*Q k) := by omega
  have hg : Q k * 4 ≤ Q k*(1+3*(3^k*Q k)+(3^k*Q k)*(3*(3^k*Q k))) := by
    exact Nat.mul_le_mul_left _ (by omega)
  omega

/-- A closed-form generic inverse chain towards a power of two. -/
def ancestor (n i : Nat) : Nat :=
  1 + 2^i * 3^((n+2)-i) * Q (n+1)

theorem ancestor_zero (n : Nat) :
    ancestor n 0 = 2^(2*3^(n+1)) := by
  have hp := power_three_lifting (n+1)
  unfold ancestor
  have he : n+2-0=n+1+1 := by omega
  rw [he]
  simp only [Nat.pow_zero, Nat.one_mul]
  exact hp.symm

private theorem ancestor_step_relation (n i : Nat) (hi : i+1 ≤ n+2) :
    2*(ancestor n i) + 1 = 3*(ancestor n (i+1)) := by
  have he : (n+2)-i = ((n+2)-(i+1))+1 := by omega
  have hp3 : 3^((n+2)-i) = 3^((n+2)-(i+1))*3 := by
    rw [he,Nat.pow_succ]
  have hp2 : 2^(i+1) = 2^i*2 := by rw [Nat.pow_succ]
  unfold ancestor
  rw [hp3,hp2]
  simp only [Nat.mul_add, Nat.add_mul]
  have hmul :
      2*((2^i*(3^((n+2)-(i+1))*3))*Q (n+1)) =
        3*((2^i*2*3^((n+2)-(i+1)))*Q (n+1)) := by ac_rfl
  omega

private theorem ancestor_generic (n i : Nat) :
    5 ≤ ancestor n (i+1) ∧ (ancestor n (i+1))%2=1 := by
  let v := 2^i * 3^((n+2)-(i+1)) * Q (n+1)
  have hx : ancestor n (i+1)=1+2*v := by
    unfold ancestor v
    rw [Nat.pow_succ]
    ac_rfl
  have hq : 4 ≤ Q (n+1) := Q_step_ge_four n
  have hpos : 0<2^i * 3^((n+2)-(i+1)) :=
    Nat.mul_pos (Nat.pow_pos (by decide)) (Nat.pow_pos (by decide))
  have hbig : Q (n+1) ≤ v := by
    exact Nat.le_mul_of_pos_left _ hpos
  rw [hx]
  constructor <;> omega

/-- The recursive predecessors are all actual generic a=0 Sheep return
edges, with no exceptional u=3 edges. -/
theorem ancestor_predecessor (n i : Nat) (hi : i+1 ≤ n+2) :
    SheepBridge.SectionNext (ancestor n (i+1)) (ancestor n i) := by
  obtain ⟨hge,hodd⟩ := ancestor_generic n i
  have heq := ancestor_step_relation n i hi
  have htarget : ancestor n (i+1)+(ancestor n (i+1)-1)/2 =
      ancestor n i := by omega
  have hnext := SheepBridge.SectionNext.general 0 (ancestor n (i+1)) hge hodd
  simpa [htarget] using hnext

/-- A chain of exactly d forward section steps. -/
inductive SectionChain : Nat → Nat → Nat → Prop where
  | refl (t : Nat) : SectionChain 0 t t
  | cons {n t u v : Nat} :
      SheepBridge.SectionNext t u → SectionChain n u v → SectionChain (n+1) t v

/-- Explicit depth-indexed chain from a generic odd ancestor to a power. -/
theorem finite_ancestry (n i : Nat) (hi : i≤n+1) :
    SectionChain i (ancestor n i) (ancestor n 0) := by
  induction i with
  | zero => exact SectionChain.refl _
  | succ i ih =>
    exact SectionChain.cons (ancestor_predecessor n i (by omega)) (ih (by omega))

/-- For every prescribed depth, a power of two has a valid all-generic
backward Sheep predecessor chain of at least that length. -/
theorem power_has_arbitrarily_long_predecessor_chain (n : Nat) :
    ∃ j t : Nat, SectionChain n t (2^j) := by
  refine ⟨2*3^(n+1), ancestor n n, ?_⟩
  rw [←ancestor_zero n]
  exact finite_ancestry n n (by omega)

#print axioms BB6.Agent22.InfiniteAncestry.power_has_arbitrarily_long_predecessor_chain

end BB6.Agent22.InfiniteAncestry
