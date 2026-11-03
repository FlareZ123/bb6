import Three
namespace BB6.Agent17Forward

def W4 : Nat → Nat
  | 0 => 0
  | b+1 => 4*W4 b + 1

theorem pow4_one (b : Nat) : 4^b = 1+3*W4 b := by
  induction b with
  | zero => decide
  | succ b ih =>
    rw [Nat.pow_succ, ih]
    simp only [W4]
    omega

def P (r c b : Nat) : Nat := 4^b*(4*b+c)+r

private theorem p_shift_raw (r c b k : Nat) :
 P r c (b+3^k) =
   P r c b + 3^k + 3^(k+1)*(1+4*W4 b+Q k*4^b*(4*b+4*3^k+c)) := by
  let q:=3^k
  let z:=4^b
  have hp : 4^(3^k) = 1+3^(k+1)*Q k := power_three_lifting k
  have hz : 4^b=1+3*W4 b := pow4_one b
  have hpow : 4^(b+3^k) = 4^b*4^(3^k) := Nat.pow_add 4 b (3^k)
  have hpower : 3^(k+1)=3*3^k := by rw [Nat.pow_succ]; omega
  simp only [P, hpow, hp, hpower]
  simp only [Nat.mul_add, Nat.add_mul, Nat.mul_assoc]
  rw [hz]
  simp only [Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm]
  grind

theorem p_shift_mod (r c b k : Nat) :
 P r c (b+3^k) % 3^(k+1) = (P r c b + 3^k) % 3^(k+1) := by
 rw [p_shift_raw]
 have hp : 3^(k+1) = 3*3^k := by rw [Nat.pow_succ]; omega
 simp only [← Nat.add_assoc, Nat.add_mul_mod_self_left]

private theorem add_q_mod (x q : Nat) :
 (x+q)%(q*3) = (x%(q*3)+q)%(q*3) := (Nat.mod_add_mod _ _ _).symm

private theorem add_two_q_mod (x q : Nat) :
 (x+q+q)%(q*3) = (x%(q*3)+q+q)%(q*3) := by
  calc
    (x+q+q)%(q*3) = ((x+q)%(q*3)+q)%(q*3) := (Nat.mod_add_mod _ _ _).symm
    _ = ((x%(q*3)+q)%(q*3)+q)%(q*3) := congrArg (fun z => (z+q)%(q*3)) (add_q_mod x q)
    _ = (x%(q*3)+q+q)%(q*3) := Nat.mod_add_mod _ _ _

theorem p_root_lt (r c k : Nat) : ∃ b : Nat, b < 3^k ∧ P r c b % 3^k = 0 := by
  induction k with
  | zero => exact ⟨0, by decide, by simp only [Nat.pow_zero, Nat.mod_one]⟩
  | succ k ih =>
    obtain ⟨b, hblt, hb⟩ := ih
    let q := 3^k
    have hq : 0<q := Nat.pow_pos (by decide)
    have hp : 3^(k+1)=q*3 := by rw [Nat.pow_succ]
    have hxmod : (P r c b % (q*3)) % q = 0 := by
      simpa [q] using hb
    have hlt : P r c b % (q*3) < q*3 := Nat.mod_lt _ (by omega)
    have hres : P r c b % (q*3)=0 ∨ P r c b % (q*3)=q ∨ P r c b % (q*3)=2*q := by
      obtain ⟨z,hz⟩ : q ∣ (P r c b % (q*3)) := (Nat.dvd_iff_mod_eq_zero).mpr hxmod
      have hzlt : z < 3 := by
        by_cases ht : z < 3
        · exact ht
        · have hzge : 3 ≤ z := by omega
          have hmul := Nat.mul_le_mul_left q hzge
          have hlt2 : q*z<q*3 := by rw [←hz]; exact hlt
          omega
      have hzcases : z=0 ∨ z=1 ∨ z=2 := by omega
      rcases hzcases with h0|h1|h2
      · left; rw [hz,h0]; omega
      · right;left; rw [hz,h1]; omega
      · right;right; rw [hz,h2]; omega
    rcases hres with h0 | h1 | h2
    · exact ⟨b, by rw [hp]; omega, by rw [hp]; exact h0⟩
    · refine ⟨b+q+q, ?_, ?_⟩
      · rw [hp]; omega
      have hs1 := p_shift_mod r c b k
      have hs2 := p_shift_mod r c (b+q) k
      have hc : P r c (b+q+q) % 3^(k+1) = (P r c b + q + q) % 3^(k+1) := by
        calc
          P r c (b+q+q) % 3^(k+1) = (P r c (b+q)+q) % 3^(k+1) := hs2
          _ = (P r c (b+q) % 3^(k+1)+q) % 3^(k+1) := (Nat.mod_add_mod _ _ _).symm
          _ = ((P r c b +q)%3^(k+1)+q)%3^(k+1) := by rw [hs1]
          _ = (P r c b + q + q)%3^(k+1) := Nat.mod_add_mod _ _ _
      rw [hc,hp,add_two_q_mod,h1]
      rw [show q+q+q = q*3 by omega, Nat.mod_self]
    · refine ⟨b+q, ?_, ?_⟩
      · rw [hp]; omega
      have hs := p_shift_mod r c b k
      change P r c (b+3^k)%3^(k+1)=0
      rw [hs,hp,add_q_mod,h2]
      rw [show 2*q+q = q*3 by omega, Nat.mod_self]

theorem p_root_all (r c k : Nat) : ∃ b : Nat, P r c b % 3^k = 0 := by
  obtain ⟨b, _, hb⟩ := p_root_lt r c k
  exact ⟨b, hb⟩

#print axioms p_root_lt
#print axioms p_root_all
end BB6.Agent17Forward
