import SheepEven

namespace SheepWeightedResidual

/-- Integer-cleared generic even-return equations imply the exact weighted residual identity. -/
theorem generic_residual_identity
    (a h b u v up : Nat)
    (hu : 1 ≤ u)
    (hstep : 2^(h+1) * v + 3 = (2^(a+1)+1) * u + 2*a)
    (hout : 2^b * up = 1 + 3^h * v) :
    2^(b+h+1) * up + 2^(h+1) * (2^b - 1) =
      2^(b+h+1) + 3^h * (2^(a+1)+1) * (u-1) +
        2 * 3^h * (2^a+a-1) := by
  let A := 2^(a+1) + 1
  let B := 2^a + a - 1
  let C := 3^h
  let D := 2^(h+1)
  let E := 2^b
  have hpow : 2^(b+h+1) = D * E := by
    calc
      2^(b+h+1) = 2^(b+(h+1)) := by congr 1 <;> omega
      _ = 2^b * 2^(h+1) := by rw [Nat.pow_add]
      _ = D * E := by dsimp [D, E]; ac_rfl
  have hEpos : 0 < E := by dsimp [E]; exact Nat.pow_pos (by decide)
  have hsum : E * up + (E - 1) = E + C * v := by
    calc
      E * up + (E - 1) = (1 + C*v) + (E-1) := by rw [hout]
      _ = E + C*v := by omega
  have hleft : D * (E * up) + D * (E - 1) = D * E + C * (D * v) := by
    calc
      D * (E * up) + D * (E - 1) = D * (E * up + (E - 1)) := by rw [Nat.mul_add]
      _ = D * (E + C * v) := by rw [hsum]
      _ = D * E + D * (C * v) := by rw [Nat.mul_add]
      _ = D * E + C * (D * v) := by ac_rfl
  have hstepC : C * (D * v) + 3 * C = C * (A * u) + C * (2*a) := by
    calc
      C * (D * v) + 3 * C = C * (D * v + 3) := by rw [Nat.mul_add]; ac_rfl
      _ = C * (A*u + 2*a) := by dsimp [A, D] at hstep ⊢; rw [hstep]
      _ = C * (A*u) + C*(2*a) := by rw [Nat.mul_add]
  have hu' : u = (u-1) + 1 := by omega
  have hA : A + 2*a = 2*B + 3 := by
    dsimp [A, B]
    have hp : 2^(a+1) = 2^a * 2 := by rw [Nat.pow_succ]
    have hp0 : 1 ≤ 2^a := Nat.one_le_pow a 2 (by decide)
    rw [hp]
    omega
  have hrewrite : C * (A*u) = C * (A*(u-1)) + C*A := by
    rw [hu']
    simp [Nat.mul_add]
  have hconst : C*A + C*(2*a) = 2*C*B + 3*C := by
    calc
      C*A + C*(2*a) = C*(A+2*a) := by exact (Nat.mul_add C A (2*a)).symm
      _ = C*(2*B+3) := by rw [hA]
      _ = C*(2*B) + C*3 := by rw [Nat.mul_add]
      _ = 2*C*B + 3*C := by ac_rfl
  have htarget : C * (D*v) = C * (A*(u-1)) + 2*C*B := by
    have hlin := hstepC
    rw [hrewrite] at hlin
    have hlin' : C * (D*v) + 3*C = (C*(A*(u-1)) + 2*C*B) + 3*C := by
      calc
        C * (D*v) + 3*C = C*(A*(u-1)) + (C*A + C*(2*a)) := by
          simpa [Nat.add_assoc] using hlin
        _ = C*(A*(u-1)) + (2*C*B + 3*C) := by rw [hconst]
        _ = (C*(A*(u-1)) + 2*C*B) + 3*C := by ac_rfl
    exact Nat.add_right_cancel hlin'
  calc
    2^(b+h+1) * up + 2^(h+1) * (2^b - 1)
        = D * (E * up) + D * (E - 1) := by
            rw [hpow]
            ac_rfl
    _ = D * E + C * (D * v) := hleft
    _ = 2^(b+h+1) + 3^h * (2^(a+1)+1) * (u-1) +
          2 * 3^h * (2^a+a-1) := by
            rw [← hpow, htarget]
            dsimp [A, B, C]
            ac_rfl

def weightedResidualS (a h b : Nat) : Int :=
  (3^h : Int) * ((2^a : Int) + (a : Int) - 1) -
    (2^h : Int) * ((2^b : Int) - 1)

theorem generic_residual_int
    (a h b u v up : Nat)
    (hu : 1 ≤ u)
    (hstep : 2^(h+1) * v + 3 = (2^(a+1)+1) * u + 2*a)
    (hout : 2^b * up = 1 + 3^h * v) :
    (2^(b+h+1) : Int) * ((up : Int) - 1) =
      (3^h : Int) * ((2^(a+1) : Int) + 1) * ((u : Int) - 1) +
        2 * weightedResidualS a h b := by
  have hnat := generic_residual_identity a h b u v up hu hstep hout
  have hcast := congrArg (fun n : Nat => (n : Int)) hnat
  have hpowU : 1 ≤ 2^b := Nat.one_le_pow b 2 (by decide)
  have hpowA : 1 ≤ 2^a + a := by
    have hp : 1 ≤ 2^a := Nat.one_le_pow a 2 (by decide)
    omega
  have hcastU : ((u-1 : Nat) : Int) = (u : Int) - 1 := Int.natCast_sub hu
  have hcastB : ((2^b-1 : Nat) : Int) = (2^b : Int) - 1 := Int.natCast_sub hpowU
  have hcastA : ((2^a+a-1 : Nat) : Int) = (2^a : Int) + (a : Int) - 1 := by
    have hh := Int.natCast_sub (n := 1) (m := 2^a+a) hpowA
    simpa [Int.natCast_add] using hh
  simp only [Int.natCast_add, Int.natCast_mul] at hcast
  rw [hcastU, hcastB, hcastA] at hcast
  simp at hcast
  let A0 : Int := 2^(b+h+1)
  let T0 : Int := 2^h * (2^b - 1)
  let Y0 : Int := 3^h * (2^(a+1) + 1) * ((u : Int) - 1)
  let Z0 : Int := 3^h * (2^a + (a : Int) - 1)
  have hpow : (2^(h+1) : Int) = 2 * 2^h := by rw [Int.pow_succ]; ac_rfl
  rw [hpow] at hcast
  have hcast' : A0 * (up : Int) + 2*T0 = A0 + Y0 + 2*Z0 := by
    dsimp [A0, T0, Y0, Z0]
    simpa [Int.mul_assoc, Int.mul_left_comm, Int.mul_comm] using hcast
  unfold weightedResidualS
  change A0 * ((up : Int) - 1) = Y0 + 2*(Z0-T0)
  rw [Int.mul_sub]
  omega

/-- The generic source transition and its exact odd-run return satisfy the
integer-cleared equations used by the weighted-cofactor identity. -/
theorem source_generic_even_return
    (a u : Nat) (ha : 1≤a) (hu : u%2=1) (hl : 5≤u) :
    ∃ h v b up,
      (2^a*u)%2=0 ∧ v%2=1 ∧ up%2=1 ∧
      2^(h+1)*v+3=(2^(a+1)+1)*u+2*a ∧
      2^b*up=1+3^h*v := by
  have hpow : 1 ≤ 2^a := Nat.one_le_pow a 2 (by decide)
  have hpowEven : 2^a % 2 = 0 := by
    have ha' : a = (a-1)+1 := by omega
    rw [ha', Nat.pow_succ]
    simp
  have hxeven : (2^a*u)%2=0 := by simp [Nat.mul_mod, hpowEven]
  have hx : 5 ≤ 2^a*u := by
    have hm := Nat.mul_le_mul_right u hpow
    omega
  have hs : SheepEven.Step (2^a*u) (2^a*u+a+(u-1)/2) :=
    SheepEven.Step.generic a u hu hl
  obtain ⟨h,v,hv,hz,hchain,heven,hinc⟩ := SheepEven.even_successor hx hs
  have hsource : 1+2^h*v = 2^a*u+a+(u-1)/2 := hz.symm
  have hstep : 2^(h+1)*v+3=(2^(a+1)+1)*u+2*a := by
    have hp : 2^(h+1)=2*2^h := by simp [Nat.pow_succ, Nat.mul_comm]
    have hpa : 2^(a+1)=2*2^a := by simp [Nat.pow_succ, Nat.mul_comm]
    have hdiv : 2*((u-1)/2)=u-1 := by omega
    have htwice := congrArg (fun n => 2*n) hsource
    simp only [Nat.mul_add] at htwice
    rw [hdiv] at htwice
    have htwice' : 2*2^h*v+2 = 2*2^a*u+2*a+(u-1) := by
      simpa [Nat.mul_assoc, Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using htwice
    rw [hp, hpa, Nat.add_mul]
    omega
  have hypos : 0 < 1+3^h*v := by
    have hpos : 0 < 2^a*u := by omega
    omega
  obtain ⟨b,up,hup,hy⟩ := SheepEven.factor_odd (1+3^h*v) hypos
  refine ⟨h,v,b,up,hxeven,hv,hup,hstep,?_⟩
  omega

/-- The actual source-level generic even return satisfies the weighted identity. -/
theorem source_generic_residual
    (a u : Nat) (ha : 1≤a) (hu : u%2=1) (hl : 5≤u) :
    ∃ h v b up,
      (2^a*u)%2=0 ∧ ((v : Nat)%2=1) ∧ ((up : Nat)%2=1) ∧
      (2^(b+h+1) : Int) * ((up : Int) - 1) =
        (3^h : Int) * ((2^(a+1) : Int) + 1) * ((u : Int) - 1) +
          2 * weightedResidualS a h b := by
  obtain ⟨h,v,b,up,hxeven,hv,hup,hstep,hout⟩ :=
    source_generic_even_return a u ha hu hl
  refine ⟨h,v,b,up,hxeven,hv,hup,?_⟩
  exact generic_residual_int a h b u v up (by omega) hstep hout

#print axioms generic_residual_identity
#print axioms generic_residual_int
#print axioms source_generic_even_return
#print axioms source_generic_residual

end SheepWeightedResidual
