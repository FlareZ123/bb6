import Five80Compact
set_option maxHeartbeats 0
namespace A4Five80

private theorem four_pow_even_mod80 (n : Nat) : 4^(2*n+2)%80=16 := by
  induction n with
  | zero => decide
  | succ n ih =>
    have he : 2*(n+1)+2=(2*n+2)+2 := by omega
    rw [he,Nat.pow_add,Nat.mul_mod,ih]

private theorem four_pow_m11_mod80 (m:Nat) (hm:m%80=11) : 4^(m+1)%80=16 := by
  have hm' : m=80*(m/80)+11 := by omega
  rw [hm']
  have he : 80*(m/80)+11+1=2*(40*(m/80)+5)+2 := by omega
  rw [he]
  exact four_pow_even_mod80 _

theorem stop_parameters_mod80 (u m k : Nat) (hu:u%80=60) (hm:m%80=11)
    (eqn:k+u+3*m+4=4^(m+1)*(u+2)) :
    (2*u+1)%80=41 ∧ k%80=15 := by
  have hp:=four_pow_m11_mod80 m hm
  have powrhs : (4^(m+1)*(u+2))%80=32 := by
    rw [Nat.mul_mod,hp]
    omega
  constructor <;> omega

theorem stop_m11_u60_unreachable (u m k:Nat)
    (hu:u%80=60) (hm:m%80=11)
    (eqn:k+u+3*m+4=4^(m+1)*(u+2)) :
    ¬ A4Backward.Reach (2*u+1,k,0) := by
  obtain ⟨ha,hk⟩ := stop_parameters_mod80 u m k hu hm eqn
  exact zero_c_41_15_unreachable (2*u+1) k ha hk

#print axioms stop_m11_u60_unreachable
end A4Five80
