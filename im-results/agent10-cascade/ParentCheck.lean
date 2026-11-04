import ResetParentStrict

namespace CascadeResetInverse

private def N (u:Nat) := Nat.log2 (2*u+6)+1

private def evenCheck (h u k:Nat) : Bool :=
  decide (6*2^k-1≤u ∧ u≤8*2^k-3 ∧ 2*u=8*2^k+h+k)

private def oddCheck (h u k t:Nat) : Bool :=
  let d := (2*u+5)/(3^(t+1))
  decide (d%2=1 ∧ 6*2^k+1≤2^t*d ∧ 2^t*d≤8*2^k-1 ∧
    2*u+5=3^(t+1)*d ∧ 2*(2^t*d)=8*2^k+h+k+5)

def parentCheck (h u:Nat) : Bool :=
  (List.range (N u)).any (fun k => evenCheck h u k ||
    (List.range (N u)).any (oddCheck h u k))

private theorem pow_small (u k : Nat) (hk : 2^k ≤ 2*u+6) : k < N u := by
  have hn : 2*u+6 ≠ 0 := by omega
  have hlog : k ≤ Nat.log2 (2*u+6) := (Nat.le_log2 hn).mpr hk
  dsimp [N]
  omega

private theorem odd_factor_div (u t d : Nat)
    (hout : 2*u+5=3^(t+1)*d) :
    (2*u+5)/(3^(t+1))=d := by
  rw [hout]
  exact Nat.mul_div_cancel_left d (Nat.pow_pos (by decide))

private theorem three_base (t : Nat) : 2^t ≤ 3^(t+1) := by
  induction t with
  | zero => decide
  | succ t ih =>
    rw [Nat.pow_succ, Nat.pow_succ]
    omega

theorem parentCheck_complete (h u : Nat) (hp:ResetParent h u) :
    parentCheck h u=true := by
  rcases hp with ⟨k,⟨hlo,hhi⟩,heq⟩ | ⟨k,t,d,hd,⟨hlo,hhi⟩,hout,hq⟩
  · have pp : 1≤2^k := Nat.one_le_pow k 2 (by decide)
    have hkb : 2^k ≤ 2*u+6 := by omega
    apply List.any_eq_true.mpr
    refine ⟨k,List.mem_range.mpr (pow_small u k hkb),?_⟩
    simpa only [Bool.or_eq_true] using (Or.inl (show evenCheck h u k = true by simp [evenCheck,hlo,hhi,heq]))
  · have hd1 : 1≤d := by omega
    have ht : 2^t≤3^(t+1) := three_base t
    have htd := Nat.mul_le_mul_right d ht
    have hqbound : 2^t*d ≤ 2*u+5 := by omega
    have hkbound : 2^k ≤2*u+6 := by omega
    have htbound : 2^t ≤2*u+6 := by
      have hh := Nat.mul_le_mul_left (2^t) hd1
      omega
    have hdiv := odd_factor_div u t d hout
    apply List.any_eq_true.mpr
    refine ⟨k,List.mem_range.mpr (pow_small u k hkbound),?_⟩
    have ho : (List.range (N u)).any (oddCheck h u k) = true := by
      apply List.any_eq_true.mpr
      refine ⟨t,List.mem_range.mpr (pow_small u t htbound),?_⟩
      change decide (((2*u+5)/(3^(t+1)))%2=1 ∧
        6*2^k+1≤2^t*((2*u+5)/(3^(t+1))) ∧
        2^t*((2*u+5)/(3^(t+1)))≤8*2^k-1 ∧
        2*u+5=3^(t+1)*((2*u+5)/(3^(t+1))) ∧
        2*(2^t*((2*u+5)/(3^(t+1))))=8*2^k+h+k+5) = true
      rw [hdiv]
      exact decide_eq_true ⟨hd,hlo,hhi,hout,hq⟩
    simpa only [Bool.or_eq_true] using (Or.inr ho : evenCheck h u k=true ∨ (List.range (N u)).any (oddCheck h u k)=true)

theorem parentCheck_sound (h u : Nat) (hp:parentCheck h u=true) :
    ResetParent h u := by
  obtain ⟨k,hkm,hcases⟩ := List.any_eq_true.mp hp
  have hcases' : evenCheck h u k=true ∨ (List.range (N u)).any (oddCheck h u k)=true := by
    simpa only [Bool.or_eq_true] using hcases
  rcases hcases' with heven | hodd
  · have he : 6*2^k-1≤u ∧ u≤8*2^k-3 ∧ 2*u=8*2^k+h+k := by
      exact of_decide_eq_true (show decide _ = true from heven)
    exact Or.inl ⟨k,⟨he.1,he.2.1⟩,he.2.2⟩
  · obtain ⟨t,htm,hyes⟩ := List.any_eq_true.mp hodd
    let d := (2*u+5)/(3^(t+1))
    have he : d%2=1 ∧ 6*2^k+1≤2^t*d ∧ 2^t*d≤8*2^k-1 ∧
      2*u+5=3^(t+1)*d ∧ 2*(2^t*d)=8*2^k+h+k+5 := by
      exact of_decide_eq_true (show decide _ = true from hyes)
    exact Or.inr ⟨k,t,d,he.1,⟨he.2.1,he.2.2.1⟩,he.2.2.2.1,he.2.2.2.2⟩

theorem parentCheck_iff (h u:Nat) : parentCheck h u=true ↔ ResetParent h u :=
  ⟨parentCheck_sound h u, parentCheck_complete h u⟩

#print axioms parentCheck_iff
end CascadeResetInverse
