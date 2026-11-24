import ZeroTwoSpine
import Lean.Elab.Tactic.Omega

namespace BB429.ZeroTwoEndpoint
set_option maxHeartbeats 5000000
open ZeroTwoSpine

private theorem power_size (e c : Nat) (hc : 3≤c) : 3≤2^e*c := by
  exact Nat.le_trans hc (Nat.le_mul_of_pos_left c (Nat.pow_pos (by decide)))

private theorem factor_two (e c : Nat) : 2^(e+1)*c=2*(2^e*c) := by
  rw [Nat.pow_succ,Nat.mul_right_comm,Nat.mul_comm (2^e*c) 2]

private theorem generic_edge (e c b : Nat) (hc : 3≤c) :
    backStep (2^(e+1)*c-3,b)=(2^e*c-3,2^(e+1)*c-3+b) ∧
    next (backStep (2^(e+1)*c-3,b))=some (2^(e+1)*c-3,b) := by
  have h := power_size e c hc
  have hp := factor_two e c
  have hb : (2^(e+1)*c-3-3)/2=2^e*c-3 := by omega
  constructor
  · simp [backStep,hb]
  · simp only [backStep,hb]
    have hguard : 2*(2^e*c-3)+3≤2^(e+1)*c-3+b := by omega
    simp only [next,ite_eq_left hguard,Option.some.injEq,Prod.mk.injEq]
    omega

/-- Exact complete inverse F burst; the rank drops by 3 at each edge. -/
theorem burst (k c b i : Nat) (hc : 3≤c) (hi : i≤k) :
    (back i (2^k*c-3,b)).1=2^(k-i)*c-3 ∧
    rank (back i (2^k*c-3,b))+3*i=rank (2^k*c-3,b) := by
  induction i with
  | zero => simp [back]
  | succ i ih =>
    obtain ⟨hp,hr⟩ := ih (by omega)
    have heq : k-i=(k-(i+1))+1 := by omega
    rw [heq] at hp
    let q := back i (2^k*c-3,b)
    have hpair : q=(2^((k-(i+1))+1)*c-3,q.2) := Prod.ext hp rfl
    change (backStep q).1=2^(k-(i+1))*c-3 ∧
      rank (backStep q)+3*(i+1)=rank (2^k*c-3,b)
    have hh := (generic_edge (k-(i+1)) c q.2 hc).1
    rw [hpair,hh]
    refine ⟨rfl,?_⟩
    have hpow := factor_two (k-(i+1)) c
    have hsize := power_size (k-(i+1)) c hc
    change rank q+3*i=rank (2^k*c-3,b) at hr
    rw [hpair] at hr
    simp only [rank] at hr ⊢
    omega

theorem burst_edge (k c b i : Nat) (hc : 3≤c) (hi : i<k) :
    next (back (i+1) (2^k*c-3,b))=some (back i (2^k*c-3,b)) := by
  have hp := (burst k c b i hc (by omega)).1
  have heq : k-i=(k-(i+1))+1 := by omega
  rw [heq] at hp
  let q := back i (2^k*c-3,b)
  have hpair : q=(2^((k-(i+1))+1)*c-3,q.2) := Prod.ext hp rfl
  change next (backStep q)=some q
  rw [hpair]
  exact (generic_edge (k-(i+1)) c q.2 hc).2

/-- The terminal even-row test is a four-class arithmetic restriction. -/
theorem endpoint_arith (k c a u w : Nat) (hc : 5≤c) (ho : c%2=1)
    (ha : a%16=13) (hu : u+3=c) (hr : 2*u+w+3*k=4*a+2)
    (hf : necessary u w) :
    (k%16=0 ∧ c%8=1) ∨ (k%16=4 ∧ c%8=7) ∨
    (k%16=8 ∧ c%8=5) ∨ (k%16=12 ∧ c%8=3) := by
  have he : u%2=0 := by omega
  unfold necessary at hf
  simp only [he,ite_true] at hf
  have h := hf.1
  split at h <;> omega

/-- A maximal F-only inverse path from an upper boundary with odd c
    terminates at an even first counter. The copied necessary predicate
    forces one of four joint congruence classes. -/
theorem endpoint_necessary (k c : Nat) (hk : 4≤k) (hc : 5≤c) (ho : c%2=1)
    (hfilter : necessary (back k (2^k*c-3,2*(2^k*c-3)+2)).1
                        (back k (2^k*c-3,2*(2^k*c-3)+2)).2) :
    (k%16=0 ∧ c%8=1) ∨ (k%16=4 ∧ c%8=7) ∨
    (k%16=8 ∧ c%8=5) ∨ (k%16=12 ∧ c%8=3) := by
  let a := 2^k*c-3
  let b := 2*a+2
  let q := back k (a,b)
  obtain ⟨hcoord,hrank⟩ := burst k c b k (by omega) (by omega)
  change q.1=2^(k-k)*c-3 at hcoord
  simp only [Nat.sub_self,Nat.pow_zero,Nat.one_mul] at hcoord
  change rank q+3*k=rank (a,b) at hrank
  have ha : a%16=13 := by
    dsimp [a]
    rw [show k=4+(k-4) by omega,Nat.pow_add,show (2:Nat)^4=16 by decide,Nat.mul_assoc]
    have hp : 0<2^(k-4)*c := Nat.mul_pos (Nat.pow_pos (by decide)) (by omega)
    omega
  have hb : b=2*a+2 := rfl
  simp only [rank] at hrank
  exact endpoint_arith k c a q.1 q.2 hc ho ha (by omega) (by omega) hfilter

#print axioms burst
#print axioms burst_edge
#print axioms endpoint_necessary
end BB429.ZeroTwoEndpoint
