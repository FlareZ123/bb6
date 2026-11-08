import Lean
import Lean.Elab.Tactic.Omega

/-! A self-contained Lean 4.36 proof excluding an infinite top strip of
Space Needle cancellation-feeder parent valuations. Pure natural arithmetic.
Original-source connection uses the already checked inverse parent equation.
-/

namespace CancellationNat

def P (A : Nat) : Nat → Nat
 | 0 => 0
 | r+1 => A*A*P A r + 9^r*(A-3)

theorem exact (A r:Nat) (hA : 3 ≤ A) :
    (A+3)*P A r+9^r=A^(2*r) := by
  induction r with
  | zero => simp [P]
  | succ r ih =>
    calc
      (A+3)*P A (r+1)+9^(r+1)
          = (A*A)*((A+3)*P A r+9^r) := by
              simp only [P, Nat.pow_succ]
              have hsub : A-3+3=A := Nat.sub_add_cancel hA
              grind
      _ = (A*A)*A^(2*r) := by rw [ih]
      _ = A^(2*(r+1)) := by
        rw [show 2*(r+1)=2*r+2 by omega, Nat.pow_add]
        simp [Nat.pow_succ, Nat.mul_comm, Nat.mul_assoc]

theorem P_lt_power (A r : Nat) (hA : 3 ≤ A) (hr : 1 ≤ r) :
    P A r < A^(2*r-1) := by
  have he : 2*r=(2*r-1)+1 := by omega
  have hpw : A^(2*r)=A*A^(2*r-1) := by
    rw [he, Nat.pow_succ]
    exact Nat.mul_comm _ _
  have hbase : 0 < A^(2*r-1) := Nat.pow_pos (by omega)
  have heq := exact A r hA
  rw [hpw] at heq
  by_cases hlt : P A r < A^(2*r-1)
  · exact hlt
  have hle : A^(2*r-1) ≤ P A r := by omega
  have hmul : (A+3)*A^(2*r-1) ≤ (A+3)*P A r :=
    Nat.mul_le_mul_left (A+3) hle
  have hdist : (A+3)*A^(2*r-1)= A*A^(2*r-1)+3*A^(2*r-1) := by
    exact Nat.add_mul A 3 _
  rw [hdist] at hmul
  have hNine : 0 ≤ 9^r := Nat.zero_le _
  omega

end CancellationNat

namespace CancellationGap

theorem pow_two_ge_square_aux (n : Nat) :
    (n+4)*(n+4) ≤ 2^(n+4) := by
  induction n with
  | zero => decide
  | succ n ih =>
    have hn : 4 ≤ n+4 := by omega
    have hmul : 4*(n+4) ≤ (n+4)*(n+4) := Nat.mul_le_mul_right (n+4) hn
    have hsquare : ((n+4)+1)*((n+4)+1)=(n+4)*(n+4)+2*(n+4)+1 := by
      simp only [Nat.add_mul, Nat.mul_add]
      omega
    have hgoal : ((n+4)+1)*((n+4)+1) ≤ 2^(n+4+1) := by
      rw [hsquare, Nat.pow_succ]
      omega
    simpa [Nat.add_assoc] using hgoal

theorem pow_two_ge_square (a : Nat) (ha : 4 ≤ a) : a*a ≤ 2^a := by
  have he : a-4+4=a := by omega
  simpa only [he] using pow_two_ge_square_aux (a-4)

theorem nine_pow_odd (r : Nat) : (9^r)%2=1 := by
  induction r with
  | zero => decide
  | succ r ih =>
    rw [Nat.pow_succ, Nat.mul_mod, ih]

theorem nine_pow_linear (r : Nat) : 8*r+1 ≤ 9^r := by
  induction r with
  | zero => decide
  | succ r ih =>
    rw [Nat.pow_succ]
    omega

def valuationA (r : Nat) : Nat := (9^r+5)/2

theorem valuationA_double (r : Nat) :
    2*valuationA r=9^r+5 := by
  have hp := nine_pow_odd r
  unfold valuationA
  omega

theorem valuationA_linear (r : Nat) : 4*r+3 ≤ valuationA r := by
  have hp:=nine_pow_linear r
  have hd:=valuationA_double r
  omega

theorem power_dominates_linear (r : Nat) :
    (4*r+2)*valuationA r ≤ 2^(valuationA r) := by
  cases r with
  | zero => decide
  | succ r =>
    have ha:=valuationA_linear (r+1)
    have hsq:=pow_two_ge_square (valuationA (r+1)) (by omega)
    have hmul : (4*(r+1)+2)*valuationA (r+1) ≤
        valuationA (r+1)*valuationA (r+1) :=
      Nat.mul_le_mul_right (valuationA (r+1)) (by omega)
    omega

theorem no_parent_of_small_deficit
    (B h E : Nat)
    (hEB : E ≤ B*h)
    (hpos : 0 < E)
    (hgap : E+3*h < B+3) :
    ¬ (B+3) ∣ (B*h-E) := by
  intro hd
  have hmul : B+3 ∣ (B+3)*h := ⟨h,rfl⟩
  have hdiff : (B+3)*h - (B*h-E) = E+3*h := by
    rw [Nat.add_mul]
    have hsub : B*h-E+E=B*h := Nat.sub_add_cancel hEB
    omega
  have hsm := Nat.dvd_sub hmul hd
  rw [hdiff] at hsm
  exact (Nat.not_dvd_of_pos_of_lt (by omega) hgap) hsm

end CancellationGap

namespace CancellationStrip
open CancellationGap CancellationNat

theorem exp_mono (x y : Nat) (h : x ≤ y) : 2^x ≤ 2^y := by
  exact Nat.pow_le_pow_right (by decide) h

theorem top_interval (r u : Nat) (hr : 1 ≤ r)
    (ha : ((2*r-1)*valuationA r)+3 ≤ u+1)
    (hb : u+1 ≤ (2*r)*valuationA r) :
    8 * 2^((2*r-1)*valuationA r) ≤ 2^(u+1) ∧
    8 * 2^((2*r)*valuationA r-(u+1)) ≤ 2^(valuationA r) := by
  constructor
  · have hpow := exp_mono (((2*r-1)*valuationA r)+3) (u+1) ha
    simpa [Nat.pow_add, Nat.mul_comm, Nat.mul_assoc] using hpow
  · have hlin : (2*r)*valuationA r = (2*r-1)*valuationA r + valuationA r := by
      have hh : 2*r=(2*r-1)+1 := by omega
      rw [hh]
      simp [Nat.add_mul]
    have hsub : ((2*r)*valuationA r-(u+1))+(u+1) =
        (2*r)*valuationA r := Nat.sub_add_cancel hb
    have he : ((2*r)*valuationA r-(u+1))+3 ≤ valuationA r := by omega
    have hp := exp_mono (((2*r)*valuationA r-(u+1))+3) (valuationA r) he
    simpa [Nat.pow_add, Nat.mul_comm, Nat.mul_assoc] using hp

theorem abstract_strip (A P T B h F u : Nat)
    (hP : 0 < P) (hPT : P < T) (hAT : A ≤ T)
    (hBT : 8*T ≤ B) (hhA : 8*h ≤ A)
    (hFu : F+2*u ≤ A) (hAu : 2*u ≤ A)
    (hC : B*h=A*P+3*P+F) (hF : 3 ≤ F) :
    ¬ (B+3) ∣ (A*P+3-2*u) := by
  let E := 3*P+F+2*u-3
  have hE : E+3=3*P+F+2*u := by
    dsimp [E]
    omega
  have hEpos : 0<E := by omega
  have hh3 : 3*h ≤ A := by omega
  have hAP : A ≤ A*P := by
    exact Nat.le_mul_of_pos_right A hP
  have hEbound : E+3*h < B+3 := by
    have hTpos : 0 < T := by omega
    omega
  have hEC : E ≤ B*h := by omega
  have hIdentity : B*h-E=A*P+3-2*u := by omega
  intro hd
  have hNo := no_parent_of_small_deficit B h E hEC hEpos hEbound
  apply hNo
  rw [hIdentity]
  exact hd

theorem P_pos (A r : Nat) (hA : 4 ≤ A) (hr : 1 ≤ r) :
    0 < P A r := by
  cases r with
  | zero => omega
  | succ r =>
    simp only [P]
    have hp : 0 < 9^r*(A-3) :=
      Nat.mul_pos (Nat.pow_pos (by decide)) (by omega)
    omega

/-- Infinitely many cancellation feeder parent valuations are excluded
uniformly, for each r>=1, without finite enumeration. -/
theorem cancellation_top_no_parent (r u : Nat) (hr : 1 ≤ r)
    (hlow : (2*r-1)*valuationA r+3 ≤ u+1)
    (hhigh : u+1 ≤ (2*r)*valuationA r) :
    ¬ (2^(u+1)+3) ∣
      (2^(valuationA r)*P (2^(valuationA r)) r+3-2*u) := by
  let a := valuationA r
  let A := 2^a
  let T := A^(2*r-1)
  let B := 2^(u+1)
  let h := 2^((2*r)*a-(u+1))
  have haLinear : 4*r+3 ≤ a := valuationA_linear r
  have ha4 : 4 ≤ a := by omega
  have hA4 : 4 ≤ A := by
    have he := exp_mono 4 a ha4
    dsimp [A]
    omega
  have hPt : P A r < T := P_lt_power A r (by omega) hr
  have hPpos : 0 < P A r := P_pos A r hA4 hr
  have hAT : A ≤ T := by
    have hexp : 1 ≤ 2*r-1 := by omega
    have hpow := Nat.pow_le_pow_right (by omega : 1 ≤ A) hexp
    simpa [T] using hpow
  have hBounds := top_interval r u hr hlow hhigh
  have hBT : 8*T ≤ B := by
    have hp : T=2^((2*r-1)*a) := by
      dsimp [T,A]
      rw [←Nat.pow_mul]
      congr 1
      exact Nat.mul_comm _ _
    simpa only [B, hp, a] using hBounds.1
  have hhA : 8*h ≤ A := by
    simpa only [h,A,a] using hBounds.2
  have h2u1 : 2*(u+1) ≤ (4*r)*a := by
    calc
      2*(u+1) ≤ 2*((2*r)*a) := Nat.mul_le_mul_left 2 hhigh
      _ = (4*r)*a := by simp [Nat.mul_comm, Nat.mul_left_comm]
  have h2u : 2*u ≤ (4*r)*a := by omega
  have hval : 2*a=9^r+5 := valuationA_double r
  have hlin : (4*r+2)*a=(4*r)*a+2*a := Nat.add_mul (4*r) 2 a
  have hFu : 9^r+2*u ≤ A := by
    have hp : (4*r+2)*a ≤ A := power_dominates_linear r
    omega
  have hAu : 2*u ≤ A := by omega
  have hF : 3 ≤ 9^r := by
    have hp := Nat.pow_le_pow_right (by decide : 1 ≤ (9:Nat)) hr
    omega
  have hBh : B*h=A^(2*r) := by
    have hhi : u+1 ≤ (2*r)*a := hhigh
    have hsum : (u+1)+((2*r)*a-(u+1)) = (2*r)*a := by omega
    calc
      B*h = 2^((u+1)+((2*r)*a-(u+1))) := by
        dsimp [B,h]
        exact (Nat.pow_add 2 (u+1) ((2*r)*a-(u+1))).symm
      _ = 2^((2*r)*a) := by rw [hsum]
      _ = A^(2*r) := by
        dsimp [A]
        rw [←Nat.pow_mul]
        congr 1
        exact Nat.mul_comm _ _
  have hC : B*h=A*P A r+3*P A r+9^r := by
    rw [hBh]
    have he := CancellationNat.exact A r (by omega : 3 ≤ A)
    rw [Nat.add_mul] at he
    omega
  exact abstract_strip A (P A r) T B h (9^r) u
    hPpos hPt hAT hBT hhA hFu hAu hC hF

theorem cancellation_top_no_parent_odd (r u q : Nat) (hr : 1 ≤ r)
    (hlow : (2*r-1)*valuationA r+3 ≤ u+1)
    (hhigh : u+1 ≤ (2*r)*valuationA r)
    (hq : 2*q+3=P (2^(valuationA r)) r) :
    ¬ (2^(u+1)+3) ∣
      (2^(valuationA r)*(2*q+3)+3-2*u) := by
  simpa only [hq] using cancellation_top_no_parent r u hr hlow hhigh

/-- Direct source-equation interface: the hypothesis is the exact
cancellation-form terminal equation for the original accelerator. -/
theorem cancellation_top_no_parent_source_equation
    (r u q : Nat) (hr : 1 ≤ r)
    (hlow : (2*r-1)*valuationA r+3 ≤ u+1)
    (hhigh : u+1 ≤ (2*r)*valuationA r)
    (heq : (2^(valuationA r)+3)*(2*q+3)+9^r =
      (2^(valuationA r))^(2*r)) :
    ¬ (2^(u+1)+3) ∣
      (2^(valuationA r)*(2*q+3)+3-2*u) := by
  let A := 2^(valuationA r)
  have hA : 3 ≤ A := by
    have ha := valuationA_linear r
    have hp := exp_mono 4 (valuationA r) (by omega)
    dsimp [A]
    omega
  have he : (A+3)*P A r+9^r=A^(2*r) :=
    CancellationNat.exact A r hA
  change (A+3)*(2*q+3)+9^r=A^(2*r) at heq
  have hm : (A+3)*(2*q+3)=(A+3)*P A r := by
    omega
  have hq : 2*q+3=P A r :=
    Nat.mul_left_cancel (by omega : 0<A+3) hm
  exact cancellation_top_no_parent_odd r u q hr hlow hhigh hq

#print axioms cancellation_top_no_parent_source_equation
#print axioms cancellation_top_no_parent_odd
#print axioms cancellation_top_no_parent
#print axioms abstract_strip
#print axioms top_interval
end CancellationStrip
