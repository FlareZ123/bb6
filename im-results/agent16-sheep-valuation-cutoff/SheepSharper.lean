import Std

namespace SheepSharper

/-- The odd signed residue in a hypothetical generic first-even predecessor
    of a power of two, at hidden odd-block length h and source valuation a. -/
def K (h a : Nat) : Nat := 3^h * (2*a-3) + 2^(h+1)

private theorem gap_lift_three (h a : Nat) (ha : 29 ≤ a)
    (hk : K h a < 2^a) : K (h+3) (a+5) < 2^(a+5) := by
  have hc : 27*(2*(a+5)-3) ≤ 32*(2*a-3) := by omega
  have hm := Nat.mul_le_mul_left (3^h) hc
  have hp : 2^(h+3+1) = 2^(h+1)*8 := by
    have he : h+3+1=(h+1)+3 := by omega
    rw [he, Nat.pow_add]
  have hh : 3^(h+3)=3^h*27 := by rw [Nat.pow_add]
  have ha5 : 2^(a+5)=2^a*32 := by rw [Nat.pow_add]
  have hle : K (h+3) (a+5) ≤ 32*K h a := by
    unfold K
    rw [hh,hp]
    calc
      (3^h*27)*(2*(a+5)-3)+2^(h+1)*8
          ≤ (3^h*(32*(2*a-3))) + 2^(h+1)*32 := by
              have hleft : (3^h*27)*(2*(a+5)-3) ≤ 3^h*(32*(2*a-3)) := by
                calc
                  (3^h*27)*(2*(a+5)-3) = 3^h*(27*(2*(a+5)-3)) := by ac_rfl
                  _ ≤ 3^h*(32*(2*a-3)) := hm
              omega
      _ = 32*(3^h*(2*a-3)+2^(h+1)) := by
          simp only [Nat.mul_add]
          ac_rfl
  calc
    K (h+3) (a+5) ≤ 32*K h a := hle
    _ < 32*2^a := Nat.mul_lt_mul_of_pos_left hk (by decide)
    _ = 2^(a+5) := by rw [ha5]; ac_rfl

private theorem gap_lift_val (h a : Nat) (ha : 3 ≤ a)
    (hk : K h a < 2^a) : K h (a+1) < 2^(a+1) := by
  have hc : 2 ≤ 2*a-3 := by omega
  have hm := Nat.mul_le_mul_left (3^h) hc
  have htwo : 2*3^h ≤ K h a := by
    unfold K
    calc
      2*3^h = 3^h*2 := Nat.mul_comm _ _
      _ ≤ 3^h*(2*a-3) := hm
      _ ≤ 3^h*(2*a-3)+2^(h+1) := Nat.le_add_right _ _
  have heq : K h (a+1) = K h a+2*3^h := by
    unfold K
    have hc' : 2*(a+1)-3=(2*a-3)+2 := by omega
    rw [hc',Nat.mul_add]
    omega
  calc
    K h (a+1) = K h a+2*3^h := heq
    _ ≤ K h a+K h a := by omega
    _ < 2^a+2^a := by omega
    _ = 2^(a+1) := by rw [Nat.pow_succ]; omega

private theorem base_gap (r : Nat) (hr : r < 3) :
    K (15+r) (30+2*r) < 2^(30+2*r) := by
  have hd : r=0 ∨ r=1 ∨ r=2 := by omega
  rcases hd with h|h|h <;> subst r <;> decide

private theorem sequence_gap (r q : Nat) (hr : r < 3) :
    K (15+r+3*q) (30+2*r+5*q) < 2^(30+2*r+5*q) := by
  induction q with
  | zero => simpa using base_gap r hr
  | succ q ih =>
      have hl := gap_lift_three (15+r+3*q) (30+2*r+5*q)
        (by omega) ih
      have hh : 15+r+3*(q+1)=(15+r+3*q)+3 := by omega
      have ha : 30+2*r+5*(q+1)=(30+2*r+5*q)+5 := by omega
      rw [hh,ha]
      exact hl

private theorem gap_above (h a : Nat) (ha : 3 ≤ a)
    (hk : K h a < 2^a) (d : Nat) :
    K h (a+d) < 2^(a+d) := by
  induction d with
  | zero => simpa using hk
  | succ d ih =>
      have hnext := gap_lift_val h (a+d) (by omega) ih
      simpa [Nat.add_assoc] using hnext

/-- The tightened bound for hidden odd-block lengths h>=15. -/
def cutoff (h : Nat) : Nat :=
  30 + 2*((h-15)%3) + 5*((h-15)/3)

/-- Uniform odd-residue gap with asymptotic slope 5/3 rather than 2. -/
theorem val_gap (h a : Nat) (hh : 15 ≤ h) (ha : cutoff h ≤ a) :
    1 < K h a ∧ K h a < 2^a := by
  let r := (h-15)%3
  let q := (h-15)/3
  let b := 30+2*r+5*q
  have hr : r < 3 := by dsimp [r]; exact Nat.mod_lt _ (by decide)
  have he : h=15+r+3*q := by
    dsimp [r,q]
    have hdiv := Nat.mod_add_div (h-15) 3
    omega
  have hseq : K h b < 2^b := by
    rw [he]
    exact sequence_gap r q hr
  have hzero : 3 ≤ b := by dsimp [b]; omega
  have hbase : b ≤ a := by
    dsimp [b,r,q]
    exact ha
  have heqa : a=b+(a-b) := by omega
  have hhigh : K h a < 2^a := by
    rw [heqa]
    exact gap_above h b hzero hseq (a-b)
  have hl : 1 < K h a := by
    unfold K
    have hpow : 0 < 3^h := Nat.pow_pos (by decide)
    have hc : 2 ≤ 2*a-3 := by omega
    have hmul := Nat.mul_le_mul_left (3^h) hc
    have hm2 : 2 ≤ 3^h*2 := by omega
    have hm3 : 2 ≤ 3^h*(2*a-3) := Nat.le_trans hm2 hmul
    calc
      1 < 2 := by decide
      _ ≤ 3^h*(2*a-3) := hm3
      _ ≤ 3^h*(2*a-3)+2^(h+1) := Nat.le_add_right _ _
  exact ⟨hl,hhigh⟩

private theorem gap_lift_five (h a : Nat) (ha : 152 ≤ a)
    (hk : K h a < 2^a) : K (h+5) (a+8) < 2^(a+8) := by
  have hc : 243*(2*(a+8)-3) ≤ 256*(2*a-3) := by omega
  have hm := Nat.mul_le_mul_left (3^h) hc
  have hp : 2^(h+5+1) = 2^(h+1)*32 := by
    have he : h+5+1=(h+1)+5 := by omega
    rw [he, Nat.pow_add]
  have hh : 3^(h+5)=3^h*243 := by rw [Nat.pow_add]
  have ha8 : 2^(a+8)=2^a*256 := by rw [Nat.pow_add]
  have hle : K (h+5) (a+8) ≤ 256*K h a := by
    unfold K
    rw [hh,hp]
    calc
      (3^h*243)*(2*(a+8)-3)+2^(h+1)*32
          ≤ (3^h*(256*(2*a-3))) + 2^(h+1)*256 := by
              have hleft : (3^h*243)*(2*(a+8)-3) ≤ 3^h*(256*(2*a-3)) := by
                calc
                  (3^h*243)*(2*(a+8)-3) = 3^h*(243*(2*(a+8)-3)) := by ac_rfl
                  _ ≤ 3^h*(256*(2*a-3)) := hm
              omega
      _ = 256*(3^h*(2*a-3)+2^(h+1)) := by
          simp only [Nat.mul_add]
          ac_rfl
  calc
    K (h+5) (a+8) ≤ 256*K h a := hle
    _ < 256*2^a := Nat.mul_lt_mul_of_pos_left hk (by decide)
    _ = 2^(a+8) := by rw [ha8]; ac_rfl

private theorem base_gap_five (r : Nat) (hr : r < 5) :
    K (100+r) (168+2*r) < 2^(168+2*r) := by
  have hd : r=0 ∨ r=1 ∨ r=2 ∨ r=3 ∨ r=4 := by omega
  rcases hd with h|h|h|h|h <;> subst r <;> decide

private theorem sequence_gap_five (r q : Nat) (hr : r < 5) :
    K (100+r+5*q) (168+2*r+8*q) < 2^(168+2*r+8*q) := by
  induction q with
  | zero => simpa using base_gap_five r hr
  | succ q ih =>
      have hl := gap_lift_five (100+r+5*q) (168+2*r+8*q)
        (by omega) ih
      have hh : 100+r+5*(q+1)=(100+r+5*q)+5 := by omega
      have ha : 168+2*r+8*(q+1)=(168+2*r+8*q)+8 := by omega
      rw [hh,ha]
      exact hl

/-- Asymptotic slope 8/5 above h=100: no generic power-parent
    can have source valuation at or above this explicit threshold. -/
def cutoffFive (h : Nat) : Nat :=
  168 + 2*((h-100)%5) + 8*((h-100)/5)

theorem val_gap_five (h a : Nat) (hh : 100 ≤ h) (ha : cutoffFive h ≤ a) :
    1 < K h a ∧ K h a < 2^a := by
  let r := (h-100)%5
  let q := (h-100)/5
  let b := 168+2*r+8*q
  have hr : r < 5 := by dsimp [r]; exact Nat.mod_lt _ (by decide)
  have he : h=100+r+5*q := by
    dsimp [r,q]
    have hdiv := Nat.mod_add_div (h-100) 5
    omega
  have hseq : K h b < 2^b := by
    rw [he]
    exact sequence_gap_five r q hr
  have hzero : 3 ≤ b := by dsimp [b]; omega
  have hbase : b ≤ a := by
    dsimp [b,r,q]
    exact ha
  have heqa : a=b+(a-b) := by omega
  have hhigh : K h a < 2^a := by
    rw [heqa]
    exact gap_above h b hzero hseq (a-b)
  have hl : 1 < K h a := by
    unfold K
    have hpow : 0 < 3^h := Nat.pow_pos (by decide)
    have hc : 2 ≤ 2*a-3 := by omega
    have hmul := Nat.mul_le_mul_left (3^h) hc
    have hm2 : 2 ≤ 3^h*2 := by omega
    have hm3 : 2 ≤ 3^h*(2*a-3) := Nat.le_trans hm2 hmul
    calc
      1 < 2 := by decide
      _ ≤ 3^h*(2*a-3) := hm3
      _ ≤ 3^h*(2*a-3)+2^(h+1) := Nat.le_add_right _ _
  exact ⟨hl,hhigh⟩

#print axioms val_gap_five

#print axioms val_gap

#print axioms sequence_gap

#print axioms gap_lift_val

#print axioms gap_lift_three

end SheepSharper
