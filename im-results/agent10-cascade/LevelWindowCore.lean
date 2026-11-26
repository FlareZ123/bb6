import Lean
set_option maxHeartbeats 0
namespace CascadeLevelWindow

def Band (h k : Nat) : Prop := 4*2^k ≤ h+k+4 ∧ h+k+5 < 8*2^k

def Edge (h u k a : Nat) : Prop :=
  4*2^k < h+k+4 ∧ h+k+5 < 8*2^k ∧
  2^a*(2*u+5) = 3^a*(h+k+5+8*2^k)

private theorem pow_pos_two (n : Nat) : 0 < 2^n := Nat.pow_pos (by decide)

private theorem pow_mul_ge (d : Nat) : 3*3^(2*d+1) ≥ 4*2^(2*d+1+d) := by
  induction d with
  | zero => decide
  | succ d ih =>
    have e3 : 3^(2*(d+1)+1) = 3^(2*d+1)*9 := by
      rw [show 2*(d+1)+1=(2*d+1)+2 by omega,Nat.pow_add]
    have e2 : 2^(2*(d+1)+1+(d+1)) = 2^(2*d+1+d)*8 := by
      rw [show 2*(d+1)+1+(d+1)=(2*d+1+d)+3 by omega,Nat.pow_add]
    rw [e3,e2]
    have h := Nat.mul_le_mul_right 9 ih
    omega

theorem valuation_le_twice_jump (h u k d a : Nat)
    (he : Edge h u k a) (hb : Band u (k+d)) : a ≤ 2*d := by
  rcases he with ⟨hlo,hhi,heq⟩
  rcases hb with ⟨ulo,uhi⟩
  by_cases hgood : a ≤ 2*d
  · exact hgood
  · exfalso
    have ha : 2*d+1 ≤ a := by omega
    obtain ⟨r,hr⟩ : ∃r, a=2*d+1+r := ⟨a-(2*d+1),by omega⟩
    have h23 : ∀ n : Nat, 2^n ≤ 3^n := by
      intro n
      induction n with
      | zero => decide
      | succ n ih =>
        rw [Nat.pow_succ,Nat.pow_succ]
        exact Nat.mul_le_mul ih (by decide)
    have hratio : 4*2^(a+d) ≤ 3*3^a := by
      rw [hr,show 2*d+1+r+d=(2*d+1+d)+r by omega, Nat.pow_add 2 (2*d+1+d) r, Nat.pow_add 3 (2*d+1) r]
      calc
        4*(2^(2*d+1+d)*2^r) = (4*2^(2*d+1+d))*2^r := by ac_rfl
        _ ≤ (3*3^(2*d+1))*3^r := Nat.mul_le_mul (pow_mul_ge d) (h23 r)
        _ = 3*(3^(2*d+1)*3^r) := by ac_rfl
    have hpos : 0 < 3^a := Nat.pow_pos (by decide)
    have hsource : 12*2^k < h+k+5+8*2^k := by omega
    have htarget : 2*u+5 < 16*2^(k+d) := by omega
    have hleft := Nat.mul_lt_mul_of_pos_left hsource hpos
    have hright := Nat.mul_lt_mul_of_pos_left htarget (pow_pos_two a)
    rw [←heq] at hleft
    have hstrict : 3^a*(12*2^k) < 2^a*(16*2^(k+d)) := Nat.lt_trans hleft hright
    have hweak := Nat.mul_le_mul_right (4*2^k) hratio
    have hL : 3^a*(12*2^k) = (3*3^a)*(4*2^k) := by
      change 3^a*((3*4)*2^k) = _
      ac_rfl
    have hR : 2^a*(16*2^(k+d)) = (4*2^(a+d))*(4*2^k) := by
      rw [Nat.pow_add,Nat.pow_add]
      change 2^a*((4*4)*(2^k*2^d)) = _
      ac_rfl
    rw [hL,hR] at hstrict
    omega

theorem even_deficit_doubles (h u k : Nat) (he : Edge h u k 0)
    (hu : Band u k) : 8*2^k+k-h = 2*(8*2^k+k-u) := by
  rcases he with ⟨hl,hh,he⟩
  rcases hu with ⟨ul,uh⟩
  simp at he
  omega

theorem same_level_parent_unique (h h' u k : Nat)
    (e : Edge h u k 0) (e' : Edge h' u k 0) : h=h' := by
  have h1 := e.2.2
  have h2 := e'.2.2
  simp at h1 h2
  omega

#print axioms valuation_le_twice_jump
#print axioms even_deficit_doubles
#print axioms same_level_parent_unique
end CascadeLevelWindow
