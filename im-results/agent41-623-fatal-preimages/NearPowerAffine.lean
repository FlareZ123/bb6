import NearPowerPump
import NearPowerCertificate

namespace BB6.Agent41NearPower

structure Aff where
  a : Int
  b : Int
  c : Int
  deriving Repr, DecidableEq

def Aff.eval (f : Aff) (n : Nat) : Int := f.a*9^n+f.b*n+f.c

def Aff.add (f g : Aff) : Aff := ⟨f.a+g.a,f.b+g.b,f.c+g.c⟩
def Aff.neg (f : Aff) : Aff := ⟨-f.a,-f.b,-f.c⟩
def Aff.sub (f g : Aff) : Aff := f.add g.neg
def Aff.scale (m : Int) (f : Aff) : Aff := ⟨m*f.a,m*f.b,m*f.c⟩
def ac (c : Int) : Aff := ⟨0,0,c⟩
def an : Aff := ⟨0,1,0⟩
def aq : Aff := ⟨1,0,0⟩
instance : Add Aff := ⟨Aff.add⟩
instance : Neg Aff := ⟨Aff.neg⟩
instance : Sub Aff := ⟨Aff.sub⟩
instance : HMul Int Aff Aff := ⟨Aff.scale⟩

@[simp] theorem eval_add (f g : Aff) (n : Nat) : (f+g).eval n=f.eval n+g.eval n := by
  change (f.a+g.a)*9^n+(f.b+g.b)*(n:Int)+(f.c+g.c)=_
  unfold Aff.eval
  simp only [Int.add_mul]
  omega
@[simp] theorem eval_neg (f : Aff) (n : Nat) : (-f).eval n= -f.eval n := by
  change (-f.a)*9^n+(-f.b)*(n:Int)-f.c=_
  unfold Aff.eval
  simp only [Int.neg_mul]
  omega
@[simp] theorem eval_sub (f g : Aff) (n : Nat) : (f-g).eval n=f.eval n-g.eval n := by
  change (f+(-g)).eval n=_
  rw [eval_add,eval_neg]; omega
@[simp] theorem eval_scale (m : Int) (f : Aff) (n : Nat) : (m*f).eval n=m*f.eval n := by
  change (m*f.a)*9^n+(m*f.b)*(n:Int)+m*f.c=_
  unfold Aff.eval
  simp only [Int.mul_add,Int.mul_assoc]
@[simp] theorem eval_ac (c : Int) (n : Nat) : (ac c).eval n=c := by simp [ac,Aff.eval]
@[simp] theorem eval_an (n : Nat) : an.eval n=n := by simp [an,Aff.eval]
@[simp] theorem eval_aq (n : Nat) : aq.eval n=9^n := by simp [aq,Aff.eval]

def ge (f : Aff) (z : Int) : Bool := decide (0≤f.a ∧ 0≤f.a+f.b ∧ z≤f.a+f.c)

theorem pow9_lower (n : Nat) : (n:Int)+1≤(9:Int)^n := by
  induction n with
  | zero => decide
  | succ n ih => rw [Int.pow_succ,Int.natCast_succ]; omega

theorem ge_sound {f : Aff} {z : Int} (h : ge f z=true) (n : Nat) : z≤f.eval n := by
  have hc : 0≤f.a ∧ 0≤f.a+f.b ∧ z≤f.a+f.c := by simpa [ge] using h
  have h1 := Int.mul_le_mul_of_nonneg_left (pow9_lower n) hc.1
  have h2 := Int.mul_nonneg hc.2.1 (show 0≤(n:Int) by omega)
  simp only [Int.mul_add,Int.mul_one,Int.add_mul] at h1 h2
  unfold Aff.eval
  omega

theorem pow9_mod8 (n : Nat) : (9:Int)^n%8=1 := by
  induction n with
  | zero => decide
  | succ n ih => rw [Int.pow_succ,Int.mul_emod,ih]; decide

def modEq (f : Aff) (m z : Int) : Bool := decide (f.b%m=0 ∧ (f.a+f.c)%m=z)

theorem modEq_sound {f : Aff} {m z : Int} (hm : m=2 ∨ m=4 ∨ m=8) (h : modEq f m z=true) (n : Nat) : f.eval n%m=z := by
  have hc : f.b%m=0 ∧ (f.a+f.c)%m=z := by simpa [modEq] using h
  have hpow : (9:Int)^n%m=1 := by have hp := pow9_mod8 n; rcases hm with h|h|h <;> subst m <;> omega
  unfold Aff.eval
  rw [Int.add_emod,Int.add_emod (f.a*9^n) (f.b*n),Int.mul_emod f.a,Int.mul_emod f.b,hpow,hc.1]
  simp only [Int.mul_one,Int.zero_mul,Int.zero_emod,Int.add_zero,Int.emod_emod]
  rw [←Int.add_emod]
  exact hc.2

theorem pow9_eq (n : Nat) : (9:Int)^n=3^(2*n) := by
  rw [Int.pow_mul]; rfl

def dominance (k : Aff) (W B : Int) : Bool :=
  let M := (W.natAbs+B.natAbs+5).log2+1
  ge (k-(2:Int)*an) M && decide (W.natAbs+B.natAbs+5≤3^M)

theorem dominance_sound {k : Aff} {W B : Int} (h : dominance k W B=true) (n : Nat) :
    2*(n:Int)≤k.eval n ∧ (W.natAbs+B.natAbs+5:Int)≤3^((k.eval n-2*n).toNat) := by
  simp only [dominance,Bool.and_eq_true,decide_eq_true_eq] at h
  have hg := ge_sound h.1 n
  simp only [eval_sub,eval_scale,eval_an] at hg
  have hle : (W.natAbs+B.natAbs+5).log2+1≤(k.eval n-2*n).toNat := by omega
  have hp := Nat.pow_le_pow_right (show 0<3 by decide) hle
  have hcast : ((3^((k.eval n-2*n).toNat):Nat):Int)=(3:Int)^((k.eval n-2*n).toNat) := Int.natCast_pow _ _
  rw [←hcast]
  omega

theorem dominance_positive {C : Nat} {k : Aff} {W B : Int} (hC : 0<C) (h : dominance k W B=true) (n : Nat) :
    5≤(C:Int)*3^((k.eval n-2*n).toNat)+W ∧
    2≤(C:Int)*3^(k.eval n).toNat+W*9^n+B := by
  obtain ⟨hk,hp⟩ := dominance_sound h n
  let l := (k.eval n-2*n).toNat
  have hk' : (k.eval n).toNat=l+2*n := by dsimp [l]; omega
  have hmul := Int.mul_le_mul_of_nonneg_right (show (1:Int)≤C by omega) (show 0≤(3:Int)^l by exact Int.le_of_lt (Int.pow_pos (by decide)))
  simp only [Int.one_mul] at hmul
  have hbase : (B.natAbs:Int)+5≤(C:Int)*3^l+W := by
    change (W.natAbs+B.natAbs+5:Int)≤3^l at hp
    omega
  constructor
  · change 5≤(C:Int)*3^l+W; omega
  · rw [hk',Int.pow_add,←pow9_eq,←Int.mul_assoc,←Int.add_mul]
    have hm := Int.mul_le_mul_of_nonneg_left (show (1:Int)≤9^n by have hh:=pow9_lower n; omega) (show 0≤(C:Int)*3^l+W by omega)
    simp only [Int.mul_one] at hm
    omega

#print axioms ge_sound
#print axioms modEq_sound
#print axioms dominance_positive
end BB6.Agent41NearPower
