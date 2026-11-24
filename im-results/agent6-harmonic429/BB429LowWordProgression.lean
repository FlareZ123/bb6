import BB429LowWordPeriod
import Lean.Elab.Tactic.Omega

namespace BB429.LowWord
set_option maxHeartbeats 3000000

theorem cancel_gcd (M k z : Nat) (hM : 0<M) :
    M ∣ k*z ↔ M/Nat.gcd k M ∣ z := by
  let g := Nat.gcd k M
  let a := k/g
  let b := M/g
  have hg : 0<g := Nat.gcd_pos_of_pos_right k hM
  have hk : k=g*a := by
    rw [Nat.mul_comm]; exact (Nat.div_mul_cancel (Nat.gcd_dvd_left k M)).symm
  have hm : M=g*b := by
    rw [Nat.mul_comm]; exact (Nat.div_mul_cancel (Nat.gcd_dvd_right k M)).symm
  have hc : Nat.Coprime b a := (Nat.coprime_div_gcd_div_gcd hg).symm
  change M ∣ k*z ↔ b ∣ z
  constructor
  · rintro ⟨q,hq⟩
    rw [hk,hm, Nat.mul_assoc, Nat.mul_assoc] at hq
    exact hc.dvd_of_dvd_mul_left ⟨q,Nat.eq_of_mul_eq_mul_left hg hq⟩
  · rintro ⟨q,hq⟩
    refine ⟨a*q,?_⟩
    rw [hk,hm,hq]; ac_rfl

def reduced (M K : Int) : Nat := M.natAbs / Nat.gcd (K/4).natAbs M.natAbs

theorem reduced_pos_odd (M K : Int) (hM : 0<M) (ho : M%2=1) :
    0<reduced M K ∧ reduced M K%2=1 := by
  have hA : (M.natAbs:Int)=M := Int.natAbs_of_nonneg (by omega)
  have hp : 0<M.natAbs := by omega
  have hod : M.natAbs%2=1 := by omega
  have hd : reduced M K ∣ M.natAbs := Nat.div_dvd_of_dvd (Nat.gcd_dvd_right _ _)
  obtain ⟨q,hq⟩ := hd
  have hpos : 0<reduced M K := by
    by_cases h : reduced M K=0
    · have hz := h
      rw [hz, Nat.zero_mul] at hq; omega
    · omega
  have hodd : reduced M K%2=1 := by
    by_cases hz : reduced M K%2=0
    · have hh := congrArg (fun x : Nat => x%2) hq
      change M.natAbs%2=(reduced M K*q)%2 at hh
      rw [Nat.mul_mod,hz,Nat.zero_mul,Nat.zero_mod] at hh
      omega
    · omega
  exact ⟨hpos,hodd⟩

theorem congruence_difference (M K H X Y : Int) (hM : 0<M) (hk : K%4=0)
    (hy : congruence M K H Y) :
    congruence M K H X ↔ (reduced M K:Int) ∣ X-Y := by
  have hA : 0<M.natAbs := by
    have hh := Int.natAbs_of_nonneg (show 0≤M by omega); omega
  have he : K=4*(K/4) := by omega
  have hdiff : (4*M) ∣ (K*(X-Y)) ↔ M ∣ (K/4)*(X-Y) := by
    conv => lhs; rhs; rw [he,Int.mul_assoc]
    constructor
    · rintro ⟨q,hq⟩
      refine ⟨q,?_⟩
      rw [Int.mul_assoc] at hq
      omega
    · rintro ⟨q,hq⟩
      refine ⟨q,?_⟩
      rw [hq,Int.mul_assoc]
  have hcancel : (M ∣ (K/4)*(X-Y)) ↔ (reduced M K:Int) ∣ X-Y := by
    rw [←Int.natAbs_dvd_natAbs,Int.natAbs_mul,cancel_gcd _ _ _ hA,
      ←Int.natAbs_dvd_natAbs (a := (reduced M K:Int)),Int.natAbs_natCast]
    rfl
  unfold congruence at hy ⊢
  have hh : K*(X-Y)=(K*X-H-2*M)-(K*Y-H-2*M) := by rw [Int.mul_sub]; omega
  rw [←hcancel,←hdiff,hh]
  constructor
  · intro hx; exact Int.dvd_sub hx hy
  · intro hx
    have hz := Int.dvd_add hx hy
    have eq : K*X-H-2*M-(K*Y-H-2*M)+(K*Y-H-2*M)=K*X-H-2*M := by omega
    rwa [eq] at hz


theorem power_difference (N m n : Nat) :
    (N:Int) ∣ (16:Int)^m-(16:Int)^n ↔ 16^m%N=16^n%N := by
  rw [Int.dvd_iff_emod_eq_zero,←Int.emod_eq_emod_iff_emod_sub_eq_zero]
  change ((16:Nat):Int)^m % (N:Int) = ((16:Nat):Int)^n % (N:Int) ↔ _
  rw [←Int.natCast_pow,←Int.natCast_pow,←Int.natCast_emod,←Int.natCast_emod]
  omega

theorem odd_coprime16 (N : Nat) (ho : N%2=1) : Nat.Coprime 16 N := by
  have h : Nat.Coprime 2 N := by
    change Nat.gcd 2 N=1
    rw [Nat.gcd_rec 2 N,ho]
    decide
  exact h.pow_left 4

theorem power_period (N : Nat) (hN : 0<N) (ho : N%2=1) :
    ∃ p, 0<p ∧ p≤N ∧ ∀ m n : Nat, 16^m%N=16^n%N ↔ m%p=n%p := by
  by_cases h : N=1
  · subst N; exact ⟨1,by decide,by decide,fun m n => by omega⟩
  · have hc := odd_coprime16 N ho
    have h2 : 1<N := by omega
    obtain ⟨p,hp,hpN,hper,hmin⟩ := LowPeriod.least_period N h2 hc
    refine ⟨p,hp,hpN,fun m n => ⟨?_,?_⟩⟩
    · exact LowPeriod.unique_exponent N p m n h2 hp hc hper hmin
    · intro he; rw [LowPeriod.reduce_power N p m h2 hp hper,LowPeriod.reduce_power N p n h2 hp hper,he]

theorem congruence_period (vs : List Move) :
    let f := symbolic vs initial
    ∃ p, 0<p ∧ p≤reduced (Modulus f) (Coefficient f) ∧
      ∀ m n : Nat, congruence (Modulus f) (Coefficient f) (Offset f) (16^n) →
        (congruence (Modulus f) (Coefficient f) (Offset f) (16^m) ↔ m%p=n%p) := by
  let f := symbolic vs initial
  let M := Modulus f
  let K := Coefficient f
  let H := Offset f
  have ⟨hM,ho⟩ := modulus_positive_odd vs
  have hk : K%4=0 := by
    have hh := coefficient_identity vs
    change K=96*(2:Int)^vs.length-72*M at hh
    omega
  obtain ⟨hN,hNo⟩ := reduced_pos_odd M K hM ho
  obtain ⟨p,hp,hpN,hper⟩ := power_period (reduced M K) hN hNo
  refine ⟨p,hp,hpN,?_⟩
  intro m n hn
  rw [congruence_difference M K H _ _ hM hk hn,power_difference,hper]

/-- Any nonempty word-specific terminal scale set is exactly a single
    arithmetic progression intersected with a finite system of linear inequalities. -/
theorem terminal_progression (vs : List Move) (m0 : Nat) (h0 : Terminal m0 vs) :
    let f := symbolic vs initial
    ∃ p r, 0<p ∧ p≤reduced (Modulus f) (Coefficient f) ∧ r<p ∧
      ∀ m, Terminal m vs ↔ 1≤m ∧ m%p=r ∧
        ∀ l ∈ allForms vs, 0≤l.elim (Modulus f) (Coefficient f) (Offset f) (16^m) := by
  obtain ⟨p,hp,hpN,hper⟩ := congruence_period vs
  obtain ⟨hm0,hphase,hcong,hguards⟩ := (terminal_iff_scale m0 vs).mp h0
  refine ⟨p,m0%p,hp,hpN,Nat.mod_lt _ hp,?_⟩
  intro m
  rw [terminal_iff_scale]
  constructor
  · rintro ⟨hm,hph,hc,hg⟩
    exact ⟨hm,(hper m m0 hcong).mp hc,hg⟩
  · rintro ⟨hm,hr,hg⟩
    exact ⟨hm,hphase,(hper m m0 hcong).mpr hr,hg⟩

#print axioms terminal_progression
end BB429.LowWord
