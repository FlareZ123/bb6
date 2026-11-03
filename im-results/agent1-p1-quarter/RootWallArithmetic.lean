import UpperTail
import P1TwoSector

namespace BB6.Agent1RootWall
open BB6.Agent45TwoRoot

private theorem growth (q : Nat) (hq:1≤q) : 256*q ≤ 2^(8*q) := by
  induction q with
  | zero => omega
  | succ q ih =>
    cases q with
    | zero => decide
    | succ q =>
      have h := ih (by omega)
      have hp : 2^(8*(q+1+1)) = 256*2^(8*(q+1)) := by
        calc
          2^(8*(q+1+1)) = 2^(8*(q+1)+8) := by congr 1
          _ = 2^(8*(q+1))*2^8 := by rw [Nat.pow_add]
          _ = 256*2^(8*(q+1)) := by rw [show 2^8=256 by decide, Nat.mul_comm]
      have hscaled := Nat.mul_le_mul_left 256 h
      rw [hp]
      omega

theorem large_power (q : Nat) (hq:1≤q) : 65536*q*q ≤ 2^(16*q) := by
  have h := growth q hq
  have hp : 2^(16*q) = 2^(8*q)*2^(8*q) := by
    rw [show 16*q=8*q+8*q by omega, Nat.pow_add]
  rw [hp]
  have hmul := Nat.mul_le_mul h h
  have hconst : 65536*q*q=(256*q)*(256*q) := by
    calc
      65536*q*q=(256*256)*(q*q) := by
        rw [show 256*256=65536 by decide]
        ac_rfl
      _=(256*q)*(256*q) := by ac_rfl
  rw [hconst]
  exact hmul

/-- A generic dyadic wall equation with the authenticated q-sector
    parameter ranges has no natural solution at q>=1. -/
theorem generic_root_wall_impossible
    (q n A beta gamma delta : Nat)
    (hq:1≤q) (hA:28≤A) (hAu:A≤42)
    (hbeta:beta≤24) (hgamma:1≤gamma) (hgammax:gamma≤8)
    (hdelta:delta≤16)
    (heq:2^n*(4*n+64*q+delta+12)+beta*q+gamma=A*2^(16*q)) : False := by
  let P := 2^(16*q)
  let X := 2^n
  let C := 4*n+64*q+delta+12
  have hp : 0<P := Nat.two_pow_pos _
  have hx : 0<X := Nat.two_pow_pos _
  have hclower : 76≤C := by dsimp [C]; omega
  have hCpos : 0<C := by omega
  have hNA : n<16*q := by
    by_cases hn : n<16*q
    · exact hn
    have hnp : 16*q≤n := by omega
    have hpX : P≤X := Nat.pow_le_pow_right (by decide : 0<(2:Nat)) hnp
    have hXC : 76*P≤X*C := by
      calc
        76*P ≤ 76*X := Nat.mul_le_mul_left 76 hpX
        _ = X*76 := by omega
        _ ≤ X*C := Nat.mul_le_mul_left X hclower
    have hAP : A*P≤42*P := Nat.mul_le_mul_right P hAu
    have heq' : X*C+beta*q+gamma=A*P := heq
    omega
  have hCupper : C≤156*q := by dsimp [C]; omega
  have hdP : X ∣ P := by
    dsimp [X,P]
    exact Nat.pow_dvd_pow 2 (by omega)
  have hdAP : X ∣ A*P := by
    obtain ⟨z,hz⟩ := hdP
    refine ⟨A*z, ?_⟩
    rw [hz]
    ac_rfl
  have hdXC : X ∣ X*C := ⟨C,rfl⟩
  have hdSmall : X ∣ beta*q+gamma := by
    apply (Nat.dvd_add_iff_right hdXC).mpr
    rw [show X*C+(beta*q+gamma)=A*P by simpa only [X,C,P,Nat.add_assoc] using heq]
    exact hdAP
  have hboundX : X≤beta*q+gamma := Nat.le_of_dvd (by omega) hdSmall
  have hsmall0 : beta*q≤24*q := Nat.mul_le_mul_right q hbeta
  have hsmall : beta*q+gamma≤32*q := by omega
  have hUpper : X*C≤4992*(q*q) := by
    calc
      X*C ≤ (32*q)*(156*q) := Nat.mul_le_mul (by omega) hCupper
      _ = (32*156)*(q*q) := by ac_rfl
      _ = 4992*(q*q) := by rw [show 32*156=4992 by decide]
  have hAp : 28*P≤A*P := Nat.mul_le_mul_right P hA
  have hpp : 65536*q*q≤P := large_power q hq
  have hbig0 := Nat.mul_le_mul_left 28 hpp
  have hbig : 1835008*(q*q) ≤28*P := by
    have hl : 28*(65536*q*q)=1835008*(q*q) := by
      calc
        28*(65536*q*q)=(28*65536)*(q*q) := by ac_rfl
        _=1835008*(q*q) := by rw [show 28*65536=1835008 by decide]
    exact hl ▸ hbig0
  have hqq : q≤q*q := by
    have hh := Nat.mul_le_mul_right q hq
    omega
  have heq' : X*C+beta*q+gamma=A*P := heq
  omega

private theorem growth_top (q:Nat) (hq:1≤q) : 256*q ≤ 2^(16*q) := by
  have h:=growth q hq
  have hp: 2^(8*q)≤2^(16*q) :=
    Nat.pow_le_pow_right (by decide : 0<(2:Nat)) (by omega)
  omega

/-- Neither exact critical feeder can reach the affine wall through a run
    of only depth-zero source G-inverse edges, for any q>=1 and length. -/
theorem no_initial_upper_wall (q n:Nat) (root:Bool) (hq:1≤q) :
    (if root then 4*u2 q-4 else 6*u2 q-2)+12 ≠
      2^n*(4*n+64*q+(if root then 12 else 16)+12) := by
  intro h
  have hP:=growth_top q hq
  have hu: u2 q+4*q+3=7*2^(16*q) := by dsimp [u2]; omega
  cases root with
  | false =>
    simp only [Bool.false_eq_true,ite_false] at h
    have hEq : 2^n*(4*n+64*q+16+12)+24*q+8=42*2^(16*q) := by
      omega
    exact generic_root_wall_impossible q n 42 24 8 16 hq (by decide)
      (by decide) (by decide) (by decide) (by decide) (by decide) hEq
  | true =>
    simp only [ite_true] at h
    have hEq : 2^n*(4*n+64*q+12+12)+16*q+4=28*2^(16*q) := by
      omega
    exact generic_root_wall_impossible q n 28 16 4 12 hq (by decide)
      (by decide) (by decide) (by decide) (by decide) (by decide) hEq

#print axioms generic_root_wall_impossible
#print axioms no_initial_upper_wall
end BB6.Agent1RootWall
