import BoundaryExact
import Lean.Elab.Tactic.Omega
set_option maxHeartbeats 0
namespace BB6.Agent48.OffsetStrip
open BB6.Agent48.Boundary

private theorem poly (x y : Nat) :
  (x+3)*(2*y*x*x+18*y) = 2*y*(x*x*x)+54*y+6*y*x*(x+3) := by
  simp [Nat.mul_add, Nat.add_mul, Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm]
  ac_rfl

private theorem pow_formula (v s : Nat) :
   (2:Nat)^(3*v+3+s) = (2:Nat)^s*((2:Nat)^(v+1)*(2:Nat)^(v+1)*(2:Nat)^(v+1)) := by
  have hh : 3*v+3+s = s+(v+1)*3 := by omega
  rw [hh, Nat.pow_add, Nat.pow_mul]
  simp [Nat.pow_succ, Nat.pow_zero, Nat.mul_assoc]

private theorem strip_divisibility (q v s : Nat)
    (h : equation q v (3*v+3+s)) :
    den v ∣ (2*v+54*(2:Nat)^s-3) := by
  let x : Nat := (2:Nat)^(v+1)
  let z : Nat := (2:Nat)^v
  let y : Nat := (2:Nat)^s
  have hy : 0 < y := Nat.pow_pos (by decide)
  have hx : x=2*z := by
    dsimp [x,z]
    rw [Nat.pow_succ]
    omega
  have hp : (2:Nat)^(3*v+3+s)=y*(x*x*x) := pow_formula v s
  have he : (x+3)*q+3*z+v+3=y*(x*x*x) := by
    have he0 : den v*q+bias v=(2:Nat)^(3*v+3+s) := h
    rw [hp] at he0
    simpa only [den,bias,x,z,y, Nat.add_assoc] using he0
  have hr : 2*y*(x*x*x)+54*y+3=(x+3)*(2*q+3)+(2*v+54*y) := by
    calc
      2*y*(x*x*x)+54*y+3=2*((x+3)*q+3*z+v+3)+54*y+3 := by
        have hn : 2*y*(x*x*x)=2*(y*(x*x*x)) := by ac_rfl
        rw [hn, ←he]
      _ = (x+3)*(2*q+3)+(2*v+54*y) := by
        simp [Nat.mul_add, Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm]
        omega
  have hbig : (x+3)*(2*y*x*x+18*y)+3 =
      (x+3)*(2*q+3+6*y*x)+(2*v+54*y) := by
    calc
      (x+3)*(2*y*x*x+18*y)+3 = 2*y*(x*x*x)+54*y+6*y*x*(x+3)+3 := by rw [poly]
      _ = (x+3)*(2*q+3)+(2*v+54*y)+6*y*x*(x+3) := by
        have ht : 2*y*(x*x*x)+54*y+6*y*x*(x+3)+3=
            (2*y*(x*x*x)+54*y+3)+6*y*x*(x+3) := by omega
        rw [ht,hr]
      _ = (x+3)*(2*q+3+6*y*x)+(2*v+54*y) := by
        simp [Nat.mul_add, Nat.add_mul, Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm]
        omega
  have hBA : 2*q+3+6*y*x ≤ 2*y*x*x+18*y := by
    have hpos : 0 < x+3 := by omega
    by_cases hb : 2*q+3+6*y*x ≤ 2*y*x*x+18*y
    · exact hb
    · have hlt : 2*y*x*x+18*y < 2*q+3+6*y*x := by omega
      have hm := Nat.mul_lt_mul_of_pos_left hlt hpos
      omega
  have hs : (2*q+3+6*y*x)+((2*y*x*x+18*y)-(2*q+3+6*y*x))=2*y*x*x+18*y := by omega
  have hgap : 2*v+54*y-3=(x+3)*((2*y*x*x+18*y)-(2*q+3+6*y*x)) := by
    have ha := congrArg (fun a : Nat => (x+3)*a) hs
    rw [Nat.mul_add] at ha
    omega
  refine ⟨(2*y*x*x+18*y)-(2*q+3+6*y*x), ?_⟩
  simpa only [den,x,y] using hgap

private theorem double_le_pow (v : Nat) (hv : 2 ≤ v) :
    2*v ≤ (2:Nat)^v := by
  have h : ∀ n : Nat, 2*(2+n) ≤ (2:Nat)^(2+n) := by
    intro n
    induction n with
    | zero => decide
    | succ n ih =>
      have hp : 2 ≤ (2:Nat)^(2+n) := by
        have hh := Nat.pow_le_pow_right (by decide : 0<(2:Nat)) (by omega : 1≤2+n)
        simpa using hh
      have he : (2:Nat)^(2+(n+1))=2*((2:Nat)^(2+n)) := by
        have hh : 2+(n+1)=(2+n)+1 := by omega
        rw [hh,Nat.pow_succ']
      rw [he]
      omega
  have ha : 2+(v-2)=v := by omega
  simpa only [ha] using h (v-2)

theorem no_narrow_terminal_strip (q v s : Nat)
    (heq : equation q v (3*v+3+s)) : v ≤ s+5 := by
  have hdvd := strip_divisibility q v s heq
  by_cases hv : v ≤ s+5
  · exact hv
  · have hvbig : s+6 ≤ v := by omega
    have htwo : 2*v ≤ (2:Nat)^v := double_le_pow v (by omega)
    have he : (2:Nat)^(s+6) ≤ (2:Nat)^v :=
      Nat.pow_le_pow_right (by decide : 0<(2:Nat)) hvbig
    have hs : (2:Nat)^(s+6)=64*((2:Nat)^s) := by
      have hswap : s+6=6+s := by omega
      rw [hswap,Nat.pow_add]
    have hy : 54*(2:Nat)^s ≤ (2:Nat)^v := by
      rw [hs] at he
      have hh := Nat.mul_le_mul_right ((2:Nat)^s) (by decide : 54≤64)
      omega
    have hpow : (2:Nat)^(v+1)=2*((2:Nat)^v) := by rw [Nat.pow_succ'];
    have hsmall : 0 < 2*v+54*(2:Nat)^s-3 := by
      have hp : 0 < (2:Nat)^s := Nat.pow_pos (by decide)
      omega
    have hless : 2*v+54*(2:Nat)^s-3 < den v := by
      unfold den
      rw [hpow]
      omega
    have hlarge := Nat.le_of_dvd hsmall hdvd
    omega

/-- Strengthening of any established sharp 3v+3 lower bound, via modular strips. -/
theorem stronger_from_sharp (q v K : Nat)
    (heq : equation q v K) (hsharp : 3*v+3 ≤ K) :
    4*v ≤ K+2 := by
  let s := K-(3*v+3)
  have hs : 3*v+3+s=K := by omega
  have he : equation q v (3*v+3+s) := by simpa only [hs] using heq
  have hb := no_narrow_terminal_strip q v s he
  omega

#print axioms stronger_from_sharp
#print axioms no_narrow_terminal_strip
#print axioms strip_divisibility
end BB6.Agent48.OffsetStrip
