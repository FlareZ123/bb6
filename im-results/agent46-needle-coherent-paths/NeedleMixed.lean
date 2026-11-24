import NeedlePeriod
import NeedleWord

namespace NeedleMixed
open NeedleCongruence NeedlePeriod NeedleWord

theorem inverse_two (M : Nat) (hodd : M%2=1) :
    ∃ u : Nat, u.Coprime M ∧ 2*u=M+1 := by
  let u := M/2+1
  have he : 2*u=M+1 := by dsimp [u]; omega
  refine ⟨u,?_,he⟩
  let g := u.gcd M
  have hg1 : g∣u := Nat.gcd_dvd_left u M
  have hg2 : g∣M := Nat.gcd_dvd_right u M
  have hg3 : g∣2*u := Nat.dvd_trans hg1 (Nat.dvd_mul_left _ _)
  rw [he] at hg3
  have hg4 : g∣1 := (Nat.dvd_add_iff_right hg2).mpr hg3
  exact Nat.dvd_one.mp hg4

/-- One actual edge can be lifted from an arbitrary odd source residue to
an arbitrary odd target residue, simultaneously prescribing all target
low bits. The valuation and cofactor can exceed arbitrary lower bounds. -/
theorem mixed_edge (M h : Nat) (hodd : M%2=1) (a b z : Int) (V Q : Nat) :
    ∃ v q p c : Nat, V≤v ∧ Q≤q ∧
      p=2^v*(2*q+3) ∧ c=p+v+3*(q+1) ∧
      (M:Int) ∣ (p:Int)-a ∧ (M:Int) ∣ (c:Int)-b ∧
      (2:Int)^h ∣ (c:Int)-z := by
  have hM : 0<M := by omega
  obtain ⟨u,hu,he⟩ := inverse_two M hodd
  have heI : 2*(u:Int)=(M:Int)+1 := by exact_mod_cast he
  obtain ⟨v,hv,hf⟩ := affine_exponential_surjective M u hM hu (3*(u:Int)*a) (a-3*(u:Int)) b V
  have hcop : (2^(v+1)).Coprime M := Nat.coprime_comm.mp (odd_coprime_pow M (v+1) hodd)
  obtain ⟨q₁,_,hq₁⟩ := coprime_solve (2^(v+1)) M (3*(2:Int)^v) a 0 hM hcop
  let D := 2^(v+1)+3
  have hDodd : D%2=1 := by simp [D,Nat.pow_succ,Nat.add_mod]
  obtain ⟨q₂,_,hq₂⟩ := coprime_solve D (2^h) (3*(2:Int)^v+(v:Int)+3) z 0 (Nat.two_pow_pos h) (odd_coprime_pow D h hDodd)
  obtain ⟨q,hQ,hqM,hq2⟩ := crt M (2^h) q₁ q₂ Q hM (Nat.two_pow_pos h) (odd_coprime_pow M h hodd)
  let p := 2^v*(2*q+3)
  let c := p+v+3*(q+1)
  have hp : (p:Int)=2^(v+1)*(q:Int)+3*2^v := by simp [p]; push_cast; grind
  have hc : (c:Int)=(D:Int)*(q:Int)+3*2^v+(v:Int)+3 := by simp [c,D,hp]; push_cast; grind
  have hpM : (M:Int) ∣ (p:Int)-a := by
    obtain ⟨x,hx⟩ := hq₁
    obtain ⟨y,hy⟩ := hqM
    refine ⟨x+(2:Int)^(v+1)*y,?_⟩
    rw [hp]
    push_cast at hx
    grind
  have hc2 : (2:Int)^h ∣ (c:Int)-z := by
    obtain ⟨x,hx⟩ := hq₂
    obtain ⟨y,hy⟩ := hq2
    refine ⟨x+(D:Int)*y,?_⟩
    rw [hc]
    push_cast at hx hy
    grind
  have hunit : (M:Int) ∣ (2:Int)*(u:Int)-1 := ⟨1,by omega⟩
  have hunitpow := dvd_pow_sub M (2*(u:Int)) 1 v hunit
  have hprod : (2*(u:Int))^v=(2:Int)^v*(u:Int)^v := Int.mul_pow
  rw [hprod] at hunitpow
  have huq : (M:Int) ∣ (u:Int)^(v+1)*(p:Int)-(u:Int)-(q:Int)-1 := by
    obtain ⟨x,hx⟩ := hunitpow
    refine ⟨(u:Int)*(2*(q:Int)+3)*x+(q:Int)+1,?_⟩
    simp only [p,Int.natCast_mul,Int.natCast_add,Int.natCast_pow]
    rw [Int.pow_succ (u:Int) v]
    have hpow1 : ∀ k : Nat, (1:Int)^k=1 := by
      intro k
      induction k with
      | zero => rfl
      | succ k ih => rw [Int.pow_succ,ih]; decide
    rw [hpow1] at hx
    grind
  have hcM : (M:Int) ∣ (c:Int)-b := by
    obtain ⟨x,hx⟩ := hpM
    obtain ⟨y,hy⟩ := huq
    obtain ⟨w,hw⟩ := hf
    refine ⟨w+(1+3*(u:Int)^(v+1))*x-3*y,?_⟩
    have hc' : (c:Int)=(p:Int)+(v:Int)+3*((q:Int)+1) := by simp [c]
    rw [hc']
    have heq : (p:Int)+(v:Int)+3*((q:Int)+1)-b =
      ((v:Int)+3*(u:Int)*a*(u:Int)^v+(a-3*(u:Int))-b) +
      (1+3*(u:Int)^(v+1))*((p:Int)-a) - 3*((u:Int)^(v+1)*(p:Int)-(u:Int)-(q:Int)-1) := by
      rw [Int.pow_succ (u:Int) v]
      grind only
    rw [heq,hw,hx,hy]
    grind only
  exact ⟨v,q,p,c,hv,hQ,rfl,rfl,hpM,hcM,hc2⟩

#print axioms mixed_edge
end NeedleMixed
