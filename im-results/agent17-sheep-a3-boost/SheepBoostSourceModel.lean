import Std
namespace SheepBoostSourceModel

def GenericF (a v : Nat) : Nat := 2^a*v+a+(v-1)/2

def EvenGenericEdge (a v y : Nat) : Prop :=
  1≤a ∧ v%2=1 ∧ 5≤v ∧
  ∃ h q : Nat, q%2=1 ∧ GenericF a v=1+2^h*q ∧ y=1+3^h*q

theorem generic_return_identity (a v h q : Nat)
    (ha : 2≤a) (hv : v%2=1)
    (heq : (2^(a+1)+1)*v+(2*a-3)=2^(h+1)*q) :
    GenericF a v = 1+2^h*q := by
  have hv2 : 2*((v-1)/2)=v-1 := by omega
  have hK : 2*a-3+3=2*a := by omega
  have hlin : 2*(2^a*v)+v+(2*a-3)=2*(2^h*q) := by
    calc
      2*(2^a*v)+v+(2*a-3) = (2^(a+1)+1)*v+(2*a-3) := by
        rw [Nat.pow_succ,Nat.add_mul,Nat.one_mul]
        ac_rfl
      _ = 2^(h+1)*q := heq
      _ = 2*(2^h*q) := by rw [Nat.pow_succ]; ac_rfl
  dsimp [GenericF]
  omega

theorem odd_quotient_of_power (j h q : Nat) (hj : 0<j)
    (heq : 3^h*q+1=2^j) : q%2=1 := by
  have h3 : (3:Nat)^h%2=1 := by
    rw [Nat.pow_mod]
    simp
  have hp : (2:Nat)^j%2=0 := by
    cases j with
    | zero => omega
    | succ j => rw [Nat.pow_succ,Nat.mul_mod]; simp
  have hm := congrArg (fun x : Nat => x%2) heq
  rw [Nat.add_mod,Nat.mul_mod,h3,hp] at hm
  omega

theorem generic_edge_of_equation (a v h q j : Nat)
    (ha : 2≤a) (hv : v%2=1) (hvmin : 5≤v) (hqodd : q%2=1)
    (hsrc : (2^(a+1)+1)*v+(2*a-3)=2^(h+1)*q)
    (htarget : 3^h*q+1=2^j) : EvenGenericEdge a v (2^j) := by
  refine ⟨by omega,hv,hvmin,h,q,hqodd,?_,?_⟩
  · exact generic_return_identity a v h q ha hv hsrc
  · omega

#print axioms odd_quotient_of_power
#print axioms generic_return_identity
#print axioms generic_edge_of_equation
end SheepBoostSourceModel
