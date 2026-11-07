import Lean.Elab.Tactic.Omega

namespace BB6Modular

private theorem two_mod_cases (m x y : Nat) (_hm : 0<m)
    (hx : x<2*m) (hy : y<2*m) (h : x%m=y%m) :
    x=y ∨ (x+m)%(2*m)=y := by
  by_cases hl : x<m
  · have hmx : x%m=x := Nat.mod_eq_of_lt hl
    by_cases hr : y<m
    · have hmy : y%m=y := Nat.mod_eq_of_lt hr
      left; omega
    · have hmy : y%m=y-m := by
        rw [Nat.mod_eq_sub_mod (by omega : m≤y)]
        exact Nat.mod_eq_of_lt (by omega)
      right
      rw [Nat.mod_eq_of_lt (by omega : x+m<2*m)]
      omega
  · have hmx : x%m=x-m := by
      rw [Nat.mod_eq_sub_mod (by omega : m≤x)]
      exact Nat.mod_eq_of_lt (by omega)
    by_cases hr : y<m
    · have hmy : y%m=y := Nat.mod_eq_of_lt hr
      right
      rw [Nat.mod_eq_sub_mod (by omega : 2*m≤x+m)]
      rw [Nat.mod_eq_of_lt (by omega : x+m-2*m<2*m)]
      omega
    · have hmy : y%m=y-m := by
        rw [Nat.mod_eq_sub_mod (by omega : m≤y)]
        exact Nat.mod_eq_of_lt (by omega)
      left; omega

private theorem odd_shift (m d t : Nat) (_hm : 0<m) (hd : d%2=1) :
    (d*(t+m))%(2*m) = (d*t+m)%(2*m) := by
  have hodd : d=2*(d/2)+1 := by omega
  have he : d*m = m + (2*m)*(d/2) := by
    calc
      d*m = (2*(d/2)+1)*m := congrArg (· * m) hodd
      _ = m + (2*m)*(d/2) := by grind +ring
  rw [Nat.mul_add, he]
  calc
    (d*t+(m+(2*m)*(d/2)))%(2*m) =
        (d*t+m+(2*m)*(d/2))%(2*m) := by simp [Nat.add_assoc]
    _ = (d*t+m)%(2*m) := by simp

/-- Elementary constructive surjectivity of multiplication by an odd
    natural number modulo any power of two. No Euler/Fermat prerequisites. -/
theorem odd_mul_surjective (d E r : Nat) (hd : d%2=1) :
    ∃ t, (d*t) % (2^E) = r % (2^E) := by
  induction E with
  | zero => exact ⟨0, by simp [Nat.mod_one]⟩
  | succ E ih =>
      obtain ⟨t,ht⟩ := ih
      let m := 2^E
      have hm : 0<m := Nat.pow_pos (by decide)
      have hM : 2*m = 2^(E+1) := by
        dsimp [m]
        simp [Nat.pow_succ, Nat.mul_comm]
      have hx : (d*t)%(2*m)<2*m := Nat.mod_lt _ (by omega)
      have hy : r%(2*m)<2*m := Nat.mod_lt _ (by omega)
      have hmod : ((d*t)%(2*m))%m=(r%(2*m))%m := by
        have h1 : ((d*t)%(2*m))%m=(d*t)%m := by
          rw [Nat.mod_mul_left_mod]
        have h2 : (r%(2*m))%m=r%m := by
          rw [Nat.mod_mul_left_mod]
        simpa only [h1,h2,m] using ht
      rcases two_mod_cases m ((d*t)%(2*m)) (r%(2*m)) hm hx hy hmod with heq | heq
      · exact ⟨t, by simpa only [hM] using heq⟩
      · refine ⟨t+m, ?_⟩
        have hs := odd_shift m d t hm hd
        have hres : (d*(t+m))%(2*m) = r%(2*m) := by
          rw [hs]
          calc
            (d*t+m)%(2*m) = ((d*t)%(2*m)+m)%(2*m) :=
              (Nat.mod_add_mod _ _ _).symm
            _ = r%(2*m) := heq
        simpa only [hM] using hres


/-- Whenever two residues have the same parity, repeated shifts by twice
    any odd factor traverse their exact residue classes mod 2^E. -/
theorem odd_double_shift (E x y d : Nat) (hE : 1≤E)
    (hd : d%2=1) (hpar : x%2=y%2) :
    ∃ t, (y+2*d*t)%2^E=x%2^E := by
  let m := 2^(E-1)
  let M := 2^E
  have hm : 0<m := Nat.pow_pos (by decide)
  have hM : M=2*m := by
    have hExp : E=(E-1)+1 := by omega
    change 2^E=2*2^(E-1)
    calc
      2^E = 2^((E-1)+1) := congrArg (fun z:Nat => 2^z) hExp
      _ = 2*2^(E-1) := by rw [Nat.pow_succ]; omega
  let x0 := x%M
  let y0 := y%M
  have hx : x0<M :=
    Nat.mod_lt _ (by dsimp[M]; exact Nat.pow_pos (by decide))
  have hy : y0<M :=
    Nat.mod_lt _ (by dsimp[M]; exact Nat.pow_pos (by decide))
  have hpar0 : x0%2=y0%2 := by
    have hxpar : x0%2=x%2 := by
      have he := Nat.mod_mul_left_mod x m 2
      simpa [x0,hM,Nat.mul_comm] using he
    have hypar : y0%2=y%2 := by
      have he := Nat.mod_mul_left_mod y m 2
      simpa [y0,hM,Nat.mul_comm] using he
    omega
  let v := (x0+2*m-y0)/2
  have hv : y0+2*v=x0+2*m := by dsimp [v]; omega
  obtain ⟨t,ht⟩ := odd_mul_surjective d (E-1) v hd
  have ht' : (d*t)%m=v%m := ht
  have hshift : (2*(d*t))%M=(2*v)%M := by
    rw [hM]
    calc
      (2*(d*t))%(2*m)=2*((d*t)%m) :=
        Nat.mul_mod_mul_left 2 (d*t) m
      _ = 2*(v%m) := by rw [ht']
      _ = (2*v)%(2*m) :=
        (Nat.mul_mod_mul_left 2 v m).symm
  refine ⟨t,?_⟩
  have hymod : (y+2*d*t)%M=(y0+2*(d*t))%M := by
    have heq : y+2*d*t=y+2*(d*t) := by simp only [Nat.mul_assoc]
    rw [heq]
    exact (Nat.mod_add_mod y M (2*(d*t))).symm
  have hright : (y0+2*v)%M=x0 := by
    rw [hv,hM]
    have hmx : x0<2*m := by omega
    simp [Nat.mod_eq_of_lt hmx]
  calc
    (y+2*d*t)%M = (y0+2*(d*t))%M := hymod
    _ = (y0+2*v)%M := by
      calc
        _ = (y0%M+(2*(d*t))%M)%M := Nat.add_mod _ _ _
        _ = (y0%M+(2*v)%M)%M := by rw [hshift]
        _ = (y0+2*v)%M := (Nat.add_mod _ _ _).symm
    _ = x0 := hright
    _ = x%M := rfl

#print axioms odd_double_shift

#print axioms odd_mul_surjective
end BB6Modular
