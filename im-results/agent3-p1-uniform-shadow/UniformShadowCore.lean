import Lean.Elab.Tactic.Omega
namespace BB6.P1Shadow

theorem growth_bound (q u E : Nat) (hq : 2≤q) (hE:2*u+343≤E) :
    E+q*u+343 ≤ q*E := by
  obtain ⟨t,rfl⟩ : ∃ t : Nat, q=t+2 := ⟨q-2, by omega⟩
  have hm := Nat.mul_le_mul_left t hE
  have hex : t*(2*u+343)=2*(t*u)+343*t := by simp [Nat.mul_add, Nat.add_mul, Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm]
  rw [hex] at hm
  have hm1 : (t+2)*E=t*E+2*E := by simp [Nat.mul_add, Nat.add_mul, Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm]
  have hm2 : (t+2)*u=t*u+2*u := by simp [Nat.mul_add, Nat.add_mul, Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm]
  rw [hm1,hm2]
  omega

/-- A uniform exact error-frame certificate for one ideal dyadic P1 inverse
    step. Works for arbitrarily large counters and errors. -/
theorem certified_inverse_step
  (D N E p p' k q : Nat)
  (hqlo : 2≤q) (hqhi : q≤512)
  (hk : k≤9) (hpl : 1≤p') (hphi : p'≤342)
  (hqp : q*p=343+p')
  (hframe : 343*D=p*N+E)
  (hE : 14000≤E) (hsmall : 1024*E≤N) (hN : 10000≤N)
  (hpk : 4*k*p+343≤E) :
  let N' := N+2*k
  let D' := q*D-N'-1
  let E' := q*E-(2*k*q*p+343)
  N'+1≤q*D ∧ q*D≤2*N'-14 ∧
  E≤E' ∧ E'≤q*E ∧ 343*D'=p'*N'+E' := by
  dsimp
  have key : 343*(q*D)=343*N+p'*N+q*E := by
    calc
      343*(q*D)=q*(343*D) := by simp [Nat.mul_add, Nat.add_mul, Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm]
      _=q*(p*N+E) := by rw [hframe]
      _=(q*p)*N+q*E := by simp [Nat.mul_add, Nat.add_mul, Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm]
      _=(343+p')*N+q*E := by rw [hqp]
      _=343*N+p'*N+q*E := by simp [Nat.mul_add, Nat.add_mul, Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm]
  have hpN : N≤p'*N := by
    have h := Nat.mul_le_mul_right N hpl
    simpa only [Nat.one_mul] using h
  have hpNhi : p'*N≤342*N := Nat.mul_le_mul_right N hphi
  have hqE : q*E ≤ 512*E := Nat.mul_le_mul_right E hqhi
  have hlo : N+2*k+1 ≤q*D := by omega
  have hhi : q*D+14≤2*(N+2*k) := by omega
  have hg : E+q*(2*k*p)+343≤q*E :=
    growth_bound q (2*k*p) E hqlo (by
      have hfact : 2*(2*k*p)=4*k*p := by
        simp only [Nat.mul_assoc]
        omega
      rw [hfact]
      exact hpk)
  have hrewrite : q*(2*k*p)=2*k*q*p := by simp [Nat.mul_add, Nat.add_mul, Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm]
  rw [hrewrite] at hg
  have hc : 2*k*q*p+343 ≤q*E := by omega
  have he' : E≤q*E-(2*k*q*p+343) := by omega
  have he'hi : q*E-(2*k*q*p+343)≤q*E := Nat.sub_le _ _
  have heq1 : q*D=(N+2*k+1)+(q*D-(N+2*k)-1) := by omega
  have heq2 : q*E=(2*k*q*p+343)+(q*E-(2*k*q*p+343)) := by omega
  have hf : 343*(q*D-(N+2*k)-1)=p'*(N+2*k)+(q*E-(2*k*q*p+343)) := by
    have hkp : 2*k*q*p=2*k*(343+p') := by
      calc
        2*k*q*p=2*k*(q*p) := by simp [Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm]
        _=2*k*(343+p') := by rw [hqp]
    have hcomm : (2*k)*p' = p'*(2*k) := Nat.mul_comm _ _
    have hmul : (2*k)*(343+p')=686*k+(2*k)*p' := by
      simp only [Nat.mul_add, Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm]
    rw [heq1,heq2,hkp,hmul] at key
    simp only [Nat.mul_add] at key ⊢
    omega
  exact ⟨hlo,by omega,he',he'hi,hf⟩

#print axioms growth_bound
#print axioms certified_inverse_step
end BB6.P1Shadow
