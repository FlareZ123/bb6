import RightFiveTwoArithmetic

namespace BB6.Agent50Energy
open BB6.Agent50RightFiveTwo

/-- Future-budget exponential threshold for a negative shifted defect. -/
def threshold (n M m : Nat) : Nat :=
  16*(M+n+6)*(M-m+1)*2^(M-m)

/-- Bound the threshold by the original 2^n scale with n/2 budget. -/
theorem threshold_under_pow (n M m : Nat)
    (hn : 128 ≤ n) (hM : 2*M ≤ n) (hm : m ≤ M) :
    threshold n M m ≤ 2^n := by
  let u := n/4
  have hu : 14≤u := by dsimp [u]; omega
  have hnBound : n+2≤5*u := by
    dsimp [u]
    omega
  have hpowu := hundred_mul_le_pow u hu
  have hsq : (100*u)*(100*u) ≤ (2^u)*(2^u) :=
    Nat.mul_le_mul hpowu hpowu
  have hmax : M+n+6 ≤ 2*n+6 := by omega
  have hidx : M-m ≤ M := by omega
  have hf : M-m+1 ≤ n+1 := by omega
  have hpoly : 16*(M+n+6)*(M-m+1) ≤ 64*(n+2)*(n+2) := by
    have h1: M+n+6≤4*(n+2) := by omega
    have h2: M-m+1≤n+2 := by omega
    have hh := Nat.mul_le_mul h1 h2
    have hhh := Nat.mul_le_mul_left 16 hh
    have hh3 : 16*(4*(n+2)*(n+2))=64*(n+2)*(n+2) := by
      calc
        _ = (16*4)*((n+2)*(n+2)) := by ac_rfl
        _ = 64*((n+2)*(n+2)) := by rw [show (16:Nat)*4=64 by decide]
        _ = 64*(n+2)*(n+2) := by ac_rfl
    simpa only [Nat.mul_assoc] using (Nat.le_trans hhh (Nat.le_of_eq hh3))
  have h1 : (n+2)*(n+2) ≤ (5*u)*(5*u) :=
    Nat.mul_le_mul hnBound hnBound
  have h2 : 64*(n+2)*(n+2) ≤ (100*u)*(100*u) := by
    have hMul := Nat.mul_le_mul_left 64 h1
    have hA : 64*((5*u)*(5*u))=(40*u)*(40*u) := by
      calc
        _ = (64*25)*(u*u) := by ac_rfl
        _ = (40*40)*(u*u) := by rw [show (64:Nat)*25=40*40 by decide]
        _ = (40*u)*(40*u) := by ac_rfl
    have h40 : 40*u≤100*u :=
      Nat.mul_le_mul_right u (by decide)
    have hB := Nat.mul_le_mul h40 h40
    calc
      _ ≤ 64*((5*u)*(5*u)) := by simpa only [Nat.mul_assoc] using hMul
      _ = (40*u)*(40*u) := hA
      _ ≤ (100*u)*(100*u) := hB
  have hpolyBound : 16*(M+n+6)*(M-m+1) ≤ 2^(2*u) := by
    calc
      _ ≤ 64*(n+2)*(n+2) := hpoly
      _ ≤ (100*u)*(100*u) := h2
      _ ≤ (2^u)*(2^u) := hsq
      _ = 2^(2*u) := by rw [show 2*u=u+u by omega, Nat.pow_add]
  have hPow : 2^(M-m) ≤ 2^M := Nat.pow_le_pow_right (by decide) hidx
  have hmplus : M+2*u≤n := by dsimp [u]; omega
  calc
    threshold n M m = (16*(M+n+6)*(M-m+1))*2^(M-m) := by rfl
    _ ≤ 2^(2*u)*2^M := Nat.mul_le_mul hpolyBound hPow
    _ = 2^(M+2*u) := by rw [show M+2*u=2*u+M by omega, Nat.pow_add]
    _ ≤ 2^n := Nat.pow_le_pow_right (by decide) hmplus

/-- Cost of one t=2 step consumes at least one complete geometric
buffer interval. -/
theorem threshold_decay (n M m : Nat) (hm : m+3≤M) :
    8*threshold n M (m+3)+16*(m+n+6) ≤ threshold n M m := by
  let q := M-(m+3)
  let N := M+n+6
  have hq : M-m=q+3 := by dsimp [q]; omega
  have hq3 : M-(m+3)=q := rfl
  have hpow : 2^(q+3)=8*2^q := by
    rw [Nat.pow_add]
    omega
  have hp0 : 1≤2^q := Nat.pow_pos (by decide)
  have hN : m+n+6≤N := by dsimp [N]; omega
  have hsmall : 16*(m+n+6) ≤ 24*(16*N*2^q) := by
    have hscale : 16*(m+n+6) ≤ 16*N := Nat.mul_le_mul_left 16 hN
    have hgrow: 16*N ≤ 16*N*2^q := by
      have hprod:=Nat.mul_le_mul_left (16*N) hp0
      simpa using hprod
    omega
  have hr : threshold n M m=8*16*N*(q+4)*2^q := by
    unfold threshold
    rw [hq,hpow]
    dsimp [N]
    simp only [show q+3+1=q+4 by omega]
    simp [Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm]
  have hl : 8*threshold n M (m+3)=8*16*N*(q+1)*2^q := by
    unfold threshold
    rw [hq3]
    dsimp [N]
    simp [Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm]
  rw [hl,hr]
  have hdiff :
    8*16*N*(q+4)*2^q =
       8*16*N*(q+1)*2^q + 24*(16*N*2^q) := by
    calc
      _ = 8*16*N*((q+1)+3)*2^q := by congr 2 <;> omega
      _ = (8*16*N*(q+1)*2^q)+(8*16*N*3*2^q) := by
        simp [Nat.add_mul, Nat.mul_add, Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm]
      _ = 8*16*N*(q+1)*2^q + 24*(16*N*2^q) := by
        congr 1
        calc
          _ = (8*3)*(16*N*2^q) := by ac_rfl
          _ = 24*(16*N*2^q) := by rw [show (8:Nat)*3=24 by decide]
  omega

#print axioms BB6.Agent50Energy.threshold_under_pow
#print axioms BB6.Agent50Energy.threshold_decay

end BB6.Agent50Energy
