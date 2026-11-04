import First80
set_option maxHeartbeats 0
namespace A4First80

private theorem pow_even_mod80 (n:Nat) : 4^(2*n+2)%80=16 := by
  induction n with
  | zero => decide
  | succ n ih =>
    have he : 2*(n+1)+2=(2*n+2)+2 := by omega
    rw [he,Nat.pow_add,Nat.mul_mod,ih]

private theorem pow_odd_mod80 (n:Nat) : 4^(2*n+3)%80=64 := by
  induction n with
  | zero => decide
  | succ n ih =>
    have he : 2*(n+1)+3=(2*n+3)+2 := by omega
    rw [he,Nat.pow_add,Nat.mul_mod,ih]

theorem first_m39_mod80 (m k:Nat) (hm:m%80=39)
    (eqn:k+3*m+4=2*4^(m+1)) : k%80=71 := by
  have hmrep : m=80*(m/80)+39 := by omega
  have hp:4^(m+1)%80=16 := by
    rw [hmrep]
    have he : 80*(m/80)+39+1=2*(40*(m/80)+19)+2 := by omega
    rw [he]
    exact pow_even_mod80 _
  have rhs : (2*4^(m+1))%80=32 := by rw [Nat.mul_mod,hp]
  omega

theorem first_only_m39 (m k:Nat) (hm:2≤m)
    (eqn:k+3*m+4=2*4^(m+1)) (hk:k%80=71) : m%80=39 := by
  by_cases he:m%2=0
  · obtain ⟨n,hn⟩ : ∃ n:Nat, m=2*n+2 := ⟨m/2-1,by omega⟩
    have hp:4^(m+1)%80=64 := by
      rw [hn]
      have he' : 2*n+2+1=2*n+3 := by omega
      rw [he']
      exact pow_odd_mod80 n
    have rhs : (2*4^(m+1))%80=48 := by rw [Nat.mul_mod,hp]
    omega
  · have hn : m=2*(m/2)+1 := by omega
    have hp:4^(m+1)%80=16 := by
      rw [hn]
      have he' : 2*(m/2)+1+1=2*(m/2)+2 := by omega
      rw [he']
      exact pow_even_mod80 _
    have rhs : (2*4^(m+1))%80=32 := by rw [Nat.mul_mod,hp]
    omega

theorem first_m80_iff (m k:Nat) (hm:2≤m)
    (eqn:k+3*m+4=2*4^(m+1)) :
    k%80=71 ↔ m%80=39 := by
  constructor
  · exact first_only_m39 m k hm eqn
  · intro hm39
    exact first_m39_mod80 m k hm39 eqn

#print axioms first_m80_iff
end A4First80
