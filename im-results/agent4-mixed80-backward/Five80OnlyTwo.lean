import Five80Stop
set_option maxHeartbeats 0
namespace A4Five80

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

private theorem pow_mod80_if_even (m:Nat) (hm:2≤m) (he:m%2=0):
    4^(m+1)%80=64 := by
  obtain ⟨n,hn⟩ : ∃ n:Nat, m=2*n+2 := ⟨m/2-1,by omega⟩
  rw [hn]
  have hx:2*n+2+1=2*n+3 := by omega
  rw [hx]
  exact pow_odd_mod80 n

private theorem pow_mod80_if_odd (m:Nat) (he:m%2≠0):
    4^(m+1)%80=16 := by
  have hn: m=2*(m/2)+1 := by omega
  rw [hn]
  have hx:2*(m/2)+1+1=2*(m/2)+2 := by omega
  rw [hx]
  exact pow_even_mod80 (m/2)

theorem stopping_m80_only_two (u m k:Nat) (hm:2≤m)
    (eqn:k+u+3*m+4=4^(m+1)*(u+2))
    (ha:(2*u+1)%80=41) (hk:k%80=15) :
    (u%80=20 ∧ m%80=51) ∨ (u%80=60 ∧ m%80=11) := by
  have hu : u%80=20 ∨ u%80=60 := by omega
  by_cases he:m%2=0
  · have hp:=pow_mod80_if_even m hm he
    have powrhs : (4^(m+1)*(u+2))%80=48 := by
      rw [Nat.mul_mod,hp]
      rcases hu with hu|hu <;> omega
    rcases hu with hu|hu <;> omega
  · have hp:=pow_mod80_if_odd m he
    have powrhs : (4^(m+1)*(u+2))%80=32 := by
      rw [Nat.mul_mod,hp]
      rcases hu with hu|hu <;> omega
    rcases hu with hu|hu
    · exact Or.inl ⟨hu,by omega⟩
    · exact Or.inr ⟨hu,by omega⟩

theorem stopping_m80_iff_two (u m k:Nat) (hm:2≤m)
    (eqn:k+u+3*m+4=4^(m+1)*(u+2)) :
    ((2*u+1)%80=41 ∧ k%80=15) ↔
    (u%80=20 ∧ m%80=51) ∨ (u%80=60 ∧ m%80=11) := by
  constructor
  · rintro ⟨ha,hk⟩
    exact stopping_m80_only_two u m k hm eqn ha hk
  · intro h
    rcases h with ⟨hu,hm⟩|⟨hu,hm⟩
    · exact stop_parameters_mod80_20_51 u m k hu hm eqn
    · exact stop_parameters_mod80 u m k hu hm eqn

#print axioms stopping_m80_iff_two
#print axioms stopping_m80_only_two
end A4Five80
