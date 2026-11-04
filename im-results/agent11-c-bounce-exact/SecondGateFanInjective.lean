import SecondGateFanArithmetic
import Lean.Elab.Tactic.Omega

namespace FanArithmetic

def source (n : Nat) (i : Fin n) : Nat × Nat :=
  (p i.val (n-i.val-1),q i.val (n-i.val-1))

def secondX (n : Nat) := 6*n+5
def secondY (n : Nat) := 4^(n+1)*(3*n+4)-(6*n+6)

theorem source_m (n:Nat)(i:Fin n):m i.val (n-i.val-1)=n:=by
  unfold m
  have hi:=i.isLt
  omega

theorem source_target (n:Nat)(i:Fin n):
 x i.val (n-i.val-1)=secondX n ∧
 y i.val (n-i.val-1)=secondY n := by
  constructor
  · simp only [x,secondX,source_m]
  · simp only [y,d,b,secondY,source_m]

theorem second_halt_parameter (n:Nat):
 secondY n+(3*n+1)+3*n+5=2^(2*n+2)*((3*n+1)+3):=by
 have hpow : 2^(2*n+2)=4^(n+1) := by
   rw [show 2*n+2=2*(n+1) by omega,Nat.pow_mul,show 2^2=4 by decide]
 rw [hpow]
 have hB : 3*n+1+3=3*n+4:=by omega
 rw [hB]
 have hpow4 : 4≤4^(n+1):=by
   rw [show n+1=1+n by omega,Nat.pow_add]
   have ht:1≤4^n:=Nat.one_le_pow n 4 (by decide)
   omega
 have hmul := Nat.mul_le_mul_right (3*n+4) hpow4
 have hl : 6*n+6 ≤ 4^(n+1)*(3*n+4) := by omega
 unfold secondY
 have hs:=Nat.sub_add_cancel hl
 omega

theorem source_p_strict (n:Nat)(i j:Fin n) (h:i.val<j.val):
 p j.val (n-j.val-1)<p i.val (n-i.val-1) := by
  have hi:=i.isLt
  have hj:=j.isLt
  have ht : n-j.val-1<n-i.val-1 := by omega
  have hp : 4^(n-j.val-1)<4^(n-i.val-1) := Nat.pow_lt_pow_right (by decide) ht
  have hmul : 4^(n-j.val-1)*(3*n+4)<4^(n-i.val-1)*(3*n+4) :=
    Nat.mul_lt_mul_of_pos_right hp (by omega)
  have hai : a i.val (n-i.val-1)=4^(n-i.val-1)*(3*n+4) := by
    simp only [a,b,source_m]
  have haj : a j.val (n-j.val-1)=4^(n-j.val-1)*(3*n+4) := by
    simp only [a,b,source_m]
  have hpi : p i.val (n-i.val-1)+3=4*a i.val (n-i.val-1) := by
    have hA:=a_ge_b i.val (n-i.val-1)
    have hB : b i.val (n-i.val-1)=3*m i.val (n-i.val-1)+4 := rfl
    have hge : 3≤4*a i.val (n-i.val-1) := by omega
    simpa only [p] using Nat.sub_add_cancel hge
  have hpj : p j.val (n-j.val-1)+3=4*a j.val (n-j.val-1) := by
    have hA:=a_ge_b j.val (n-j.val-1)
    have hB : b j.val (n-j.val-1)=3*m j.val (n-j.val-1)+4 := rfl
    have hge : 3≤4*a j.val (n-j.val-1) := by omega
    simpa only [p] using Nat.sub_add_cancel hge
  have hlt : a j.val (n-j.val-1) < a i.val (n-i.val-1) := by
    rw [haj,hai]
    exact hmul
  omega

theorem source_injective (n:Nat):Function.Injective (source n):=by
 intro i j h
 have hp : p i.val (n-i.val-1)=p j.val (n-j.val-1) := congrArg Prod.fst h
 by_cases hij : i.val<j.val
 · have hlt:=source_p_strict n i j hij
   omega
 by_cases hji : j.val<i.val
 · have hlt:=source_p_strict n j i hji
   omega
 exact Fin.ext (by omega)

#print axioms source_injective
end FanArithmetic
