import Lean.Elab.Tactic.Omega

namespace BB6.Agent30Cross

theorem nat_add_mod_cancel (a b c m : Nat) :
    ((a+c)%m = (b+c)%m) ↔ (a%m=b%m) := by
  constructor
  · intro h
    have h' := congrArg (fun z:Nat => (z:Int)) h
    simp only [Int.natCast_emod, Int.natCast_add] at h'
    have q := (Int.emod_add_cancel_right (c:Int)).mp h'
    exact Int.natCast_inj.mp (by simpa only [Int.natCast_emod] using q)
  · intro h
    have h' := congrArg (fun z:Nat => (z:Int)) h
    simp only [Int.natCast_emod] at h'
    have q := (Int.emod_add_cancel_right (c:Int)).mpr h'
    exact Int.natCast_inj.mp (by simpa only [Int.natCast_emod, Int.natCast_add] using q)

def G (z : Nat) : Nat := 3*(z/2)+4+5*(z%2)

theorem G_mod3 (z : Nat) : G z % 3 = 1 - z%2 := by
  unfold G
  omega

theorem G_div3 (z : Nat) : G z / 3 = z/2+1+2*(z%2) := by
  unfold G
  omega

theorem nat_mod_digits (x y a b : Nat) :
    (x%(a*b)=y%(a*b)) ↔ (x%a=y%a ∧ (x/a)%b=(y/a)%b) := by
  constructor
  · intro h
    constructor
    · have he := congrArg (fun z : Nat => z % a) h
      simpa only [Nat.mod_mul_right_mod] using he
    · have he := congrArg (fun z : Nat => z / a) h
      simpa only [Nat.mod_mul_right_div_self] using he
  · rintro ⟨hmod, hdiv⟩
    rw [Nat.mod_mul, Nat.mod_mul, hmod, hdiv]

theorem G_cong_step (x y m : Nat) :
    (G x % (3*m) = G y % (3*m)) ↔
    (x % (2*m) = y % (2*m)) := by
  rw [nat_mod_digits, nat_mod_digits]
  simp only [G_mod3, G_div3]
  constructor
  · rintro ⟨hmod, hdiv⟩
    have hx : x%2<2 := Nat.mod_lt _ (by omega)
    have hy : y%2<2 := Nat.mod_lt _ (by omega)
    have hp : x%2=y%2 := by omega
    refine ⟨hp, ?_⟩
    have hshift : ((x/2)+(1+2*(y%2)))%m = ((y/2)+(1+2*(y%2)))%m := by
      simpa only [hp, Nat.add_assoc] using hdiv
    exact (nat_add_mod_cancel (x/2) (y/2) (1+2*(y%2)) m).mp hshift
  · rintro ⟨hp, hdiv⟩
    constructor
    · omega
    · have hshift := (nat_add_mod_cancel (x/2) (y/2) (1+2*(y%2)) m).mpr hdiv
      simpa only [hp, Nat.add_assoc] using hshift

def iterG : Nat → Nat → Nat
  | 0,z => z
  | n+1,z => G (iterG n z)

theorem iterG_cong (n x y m : Nat) :
    (iterG n x % (3^n*m) = iterG n y % (3^n*m)) ↔
    (x % (2^n*m) = y % (2^n*m)) := by
  induction n generalizing m with
  | zero => simp [iterG]
  | succ n ih =>
    have hm :
        (iterG n x % (2*(3^n*m)) = iterG n y % (2*(3^n*m))) ↔
        (x % (2^n*(2*m)) = y % (2^n*(2*m))) := by
      simpa only [Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm] using (ih (2*m))
    have h := (G_cong_step (iterG n x) (iterG n y) (3^n*m)).trans hm
    simpa only [iterG, Nat.pow_succ, Nat.mul_assoc, Nat.mul_left_comm, Nat.mul_comm] using h

#print axioms iterG_cong

theorem iterG_commutes (n z : Nat) : iterG n (G z) = G (iterG n z) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    change G (iterG n (G z)) = G (G (iterG n z))
    rw [ih]

end BB6.Agent30Cross
