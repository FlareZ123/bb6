import HighDyadicArithmetic
import Lean.Elab.Tactic.Omega

namespace BB6.Agent19AllDepth

/-- Exact arbitrary-depth Presburger core for the odd/odd inverse
    of a high stopping configuration. All hypotheses are arithmetic. -/
theorem abstract_depth_core (r j m k R P v w : Nat)
    (hm : 3≤m) (hm4 : m%4=(2*r+3)%4)
    (hR : 0<R) (hR4 : 4∣R) (hPpos : 0<P)
    (hPbound : 8*m+8≤P) (hPV : P=16*R*v)
    (hD : j+9*m+14=R*(16*w+12))
    (hstop : k+j+3*m+5=P*(j+3)) :
    let x := 2*j+3
    let a := (x+k-4)/2
    let b := (x+3*k-10)/4
    let u := (b+2)/R
    k%2=1 ∧ (x+k)%8=4 ∧ 24≤x+k ∧ 5≤k ∧
    x+k=2*a+4 ∧ x+3*k=4*b+10 ∧
    b+2=R*u ∧ u%4=1 ∧ 9≤u ∧
    (a+2*b+4*r)%8=0 := by
  let x := 2*j+3
  let a := (x+k-4)/2
  let b := (x+3*k-10)/4
  let u := (b+2)/R
  let D := j+9*m+14
  let z := v*(j+3)
  have hmOdd : m%2=1 := by omega
  have hP16 : 16∣P := by
    refine ⟨R*v, ?_⟩
    rw [hPV]
    simp [Nat.mul_add, Nat.add_mul, Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm]
  have hD16 : 16∣D := by
    obtain ⟨R0,hR0⟩ := hR4
    refine ⟨R0*(4*w+3),?_⟩
    dsimp [D]
    rw [hD,hR0]
    simp [Nat.mul_add, Nat.add_mul, Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm]
  have hPmod : P%16=0 := Nat.mod_eq_zero_of_dvd hP16
  have hDmod : D%16=0 := Nat.mod_eq_zero_of_dvd hD16
  have hPprod16 : 16∣P*(j+3) := by
    rcases hP16 with ⟨q,hq⟩
    refine ⟨q*(j+3),?_⟩
    rw [hq]
    simp only [Nat.mul_assoc]
  have hPprodmod : (P*(j+3))%16=0 := Nat.mod_eq_zero_of_dvd hPprod16
  have hodd : k%2=1 := by
    dsimp [D] at hDmod
    omega
  have hmod8 : (x+k)%8=4 := by
    dsimp [D,x] at hDmod ⊢
    omega
  have hPone : 1≤P := by omega
  have hj : j≤P*j := by
    simpa only [Nat.one_mul] using Nat.mul_le_mul_right j hPone
  have hmarg : 9*m+14≤3*P := by omega
  have hDle : D≤P*(j+3) := by
    dsimp [D]
    rw [Nat.mul_add]
    omega
  have hV : 1≤v := by
    by_cases hv : v=0
    · rw [hPV,hv] at hPpos
      simp at hPpos
    · omega
  have hPR : 16*R≤P := by
    rw [hPV]
    simpa only [Nat.mul_one] using Nat.mul_le_mul_left (16*R) hV
  have hP3 : 3*P≤P*(j+3) := by
    have hh := Nat.mul_le_mul_left P (show 3≤j+3 by omega)
    simpa only [Nat.mul_comm] using hh
  have hbig : 50≤k := by
    have hq : 3*(8*m+8)≤3*P := by omega
    rw [Nat.mul_add] at hstop
    omega
  have hXbig : 24≤x+k := by dsimp [x]; omega
  have hX2 : 2≤x+3*k := by dsimp [x]; omega
  have hxa : x+k=2*a+4 := by dsimp [a]; omega
  have hxb : x+3*k=4*b+10 := by
    dsimp [b]
    dsimp [D,x] at hDmod
    omega
  have hmultrel : x+3*k-2 + D = 3*(P*(j+3)) := by
    dsimp [x,D]
    omega
  have hHlower : 36*R≤x+3*k-2 := by
    have hPP : 6*P≤2*(P*(j+3)) := by omega
    omega
  have hPscale : 3*(P*(j+3)) = 4*R*(12*z) := by
    rw [hPV]
    dsimp [z]
    simp [Nat.mul_add, Nat.add_mul, Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm]
  have hDscale : D=4*R*(4*w+3) := by
    dsimp [D]
    rw [hD]
    simp [Nat.mul_add, Nat.add_mul, Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm]
  have hcoef_lt : 4*w+3<12*z := by
    have hp : 4*R*(4*w+3)<4*R*(12*z) := by omega
    exact (Nat.mul_lt_mul_left (by omega : 0<4*R)).mp hp
  let t := 12*z-(4*w+3)
  have htu : t+(4*w+3)=12*z := by
    dsimp [t]
    omega
  have hTscale : 4*R*t+D=3*(P*(j+3)) := by
    rw [hPscale,hDscale]
    calc
      4*R*t + 4*R*(4*w+3) = 4*R*(t+(4*w+3)) := by simp [Nat.mul_add, Nat.add_mul, Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm]
      _ = 4*R*(12*z) := by rw [htu]
  have hH : x+3*k-2=4*R*t := by omega
  have hbRt : b+2=R*t := by
    have hh : x+3*k-2=4*(R*t) := by simpa only [Nat.mul_assoc] using hH
    omega
  have ht9 : 9≤t := by
    have hq : 4*R*9≤4*R*t := by omega
    exact Nat.le_of_mul_le_mul_left hq (by omega)
  have ht4 : t%4=1 := by
    dsimp [t]
    omega
  have hu : u=t := by
    dsimp [u]
    rw [hbRt]
    simp [Nat.mul_div_cancel_left t hR]
  have hmass : (a+2*b+4*r)%8=0 := by
    have hh : a+2*b+7=x+2*k := by omega
    dsimp [x] at hh ⊢
    omega
  change k%2=1 ∧ (x+k)%8=4 ∧ 24≤x+k ∧ 5≤k ∧
    x+k=2*a+4 ∧ x+3*k=4*b+10 ∧
    b+2=R*u ∧ u%4=1 ∧ 9≤u ∧
    (a+2*b+4*r)%8=0
  exact ⟨hodd,hmod8,hXbig,by omega,hxa,hxb,by rw [hu]; exact hbRt,
    by rw [hu]; exact ht4,by rw [hu]; exact ht9,hmass⟩

/-- Every dyadic inverse depth r >= 2 up to 2*m-2 is arithmetically
    compatible with the exact source-cone conditions under this residue. -/
theorem powered_depth_core (r j m k : Nat)
    (hr : 2≤r) (hm : 3≤m)
    (hdepth : r+4≤2*m+2)
    (hm4 : m%4=(2*r+3)%4)
    (hpair : (j+9*m+14)%2^(r+4)=3*2^(r+2))
    (hstop : k+j+3*m+5=2^(2*m+2)*(j+3)) :
    let x := 2*j+3
    let a := (x+k-4)/2
    let b := (x+3*k-10)/4
    let u := (b+2)/2^r
    k%2=1 ∧ (x+k)%8=4 ∧ 24≤x+k ∧ 5≤k ∧
    x+k=2*a+4 ∧ x+3*k=4*b+10 ∧
    b+2=2^r*u ∧ u%4=1 ∧ 9≤u ∧
    (a+2*b+4*r)%8=0 := by
  let R := (2:Nat)^r
  let P := (2:Nat)^(2*m+2)
  let D := j+9*m+14
  have hR : 0<R := by
    dsimp [R]
    exact Nat.pow_pos (by decide)
  have hR4 : 4∣R := by
    dsimp [R]
    simpa only [show (2:Nat)^2=4 by decide] using
      (Nat.pow_dvd_pow 2 hr)
  have heP : (2:Nat)^(r+4)=16*R := by
    dsimp [R]
    rw [Nat.pow_add]
    simp only [show (2:Nat)^4=16 by decide]
    omega
  have heQ : (2:Nat)^(r+2)=4*R := by
    dsimp [R]
    rw [Nat.pow_add]
    simp only [show (2:Nat)^2=4 by decide]
    omega
  have hPowDvd : 16*R ∣ P := by
    dsimp [P]
    rw [←heP]
    exact Nat.pow_dvd_pow 2 hdepth
  obtain ⟨v,hPV⟩ := hPowDvd
  have hPpos : 0<P := by
    dsimp [P]
    exact Nat.pow_pos (by decide)
  have hPbound : 8*m+8≤P :=
    BB6.Agent19HighDyadic.eight_power_bound m (by omega)
  let w := D/(16*R)
  have hD : D=R*(16*w+12) := by
    have hm' : D%(16*R)=12*R := by
      dsimp [D]
      rw [←heP]
      calc
        (j+9*m+14)%2^(r+4)=3*2^(r+2) := hpair
        _ = 12*R := by rw [heQ]; omega
    have hh := Nat.mod_add_div D (16*R)
    rw [hm'] at hh
    dsimp [w]
    calc
      D = 12*R+16*R*(D/(16*R)) := hh.symm
      _ = R*(16*(D/(16*R))+12) := by
        rw [Nat.mul_add]
        ac_rfl
  have hcore := abstract_depth_core r j m k R P v w
    hm hm4 hR hR4 hPpos hPbound hPV hD hstop
  simpa only [R,P,D] using hcore

#print axioms powered_depth_core
#print axioms abstract_depth_core
end BB6.Agent19AllDepth
