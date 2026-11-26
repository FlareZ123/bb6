import ReverseLagBlocks
import ReverseBlockDigitWeight

namespace BB6.Agent9ReverseBlock

open BB6.Agent45ReverseBlock
open BB6.Agent45.DelayedCarry
open BB6.Agent45WeightedDigitGap

/-- The modular first-jump condition used by prefix_parallel.cpp.
    The per-bit shifts sum to q*B + digitWeight k B. -/
def JumpMember (F k Y c : Nat) : Prop :=
  c < F-k ∧
  ∃ B, B < 2^k ∧
    c % 2^k =
      (Y % 2^k + 2^k - (((F-k)*B + digitWeight k B) % 2^k)) % 2^k

/-- Solve a modular subtraction using only the canonical remainders. -/
theorem mod_sub_residue (M a b y : Nat)
    (hM : 0 < M) (ha : a < M) (hb : b < M) (hy : y < M)
    (h : (a+b) % M = y) :
    a = (y+M-b) % M := by
  have hlt : a+b < M*2 := by omega
  have hq : (a+b)/M < 2 :=
    (Nat.div_lt_iff_lt_mul hM).2 (by simpa [Nat.mul_comm] using hlt)
  have hdiv := Nat.div_add_mod (a+b) M
  have hcases : (a+b)/M = 0 ∨ (a+b)/M = 1 := by omega
  rcases hcases with h0 | h1
  · have hab : a+b=y := by
      rw [h0] at hdiv
      omega
    have heq : y+M-b=M+a := by omega
    rw [heq]
    simp [Nat.add_mod, Nat.mod_eq_of_lt ha]
  · have hab : M+y=a+b := by
      rw [h1] at hdiv
      omega
    have heq : y+M-b=a := by omega
    rw [heq, Nat.mod_eq_of_lt ha]

/-- Every genuine fitted reverse walk is retained by the modular residue
    jump. This is the no-false-negative direction needed by the prefix-only
    algorithm; spurious residues are harmless. -/
theorem walk_mem_jump (F z : Nat) (ys : List Nat) (c : Nat)
    (h : Walk F z ys c) :
    JumpMember F ys.length (digits ys) c := by
  let k := ys.length
  let q := F-k
  let X := 2^k*z+digits ys
  have hc : c < q := by simpa [q,k] using walk_bound h
  obtain ⟨B,hB,he⟩ := eq_of_walk h
  have hF : q+k=F := by dsimp [q,k]; omega
  have he0 : X+corr k B=F*B+c := by simpa [X] using he
  have he' : X+corr k B=(q+k)*B+c := by
    calc
      X+corr k B = F*B+c := he0
      _ = (q+k)*B+c := by rw [← hF]
  have hvalid : (q+k)*B ≤ X+corr k B := by rw [he']; omega
  have hrem := candidate_remainder_eq q k X B hB hvalid
  have hcarry : c = X-q*B-digitWeight k B := by
    calc
      c = X+corr k B-(q+k)*B := by rw [he']; omega
      _ = X-q*B-digitWeight k B := hrem
  have hcorr := corr_le_mul k B hB
  have hprod : (q+k)*B=q*B+k*B := Nat.add_mul q k B
  have hqB : q*B ≤ X := by
    rw [hprod] at hvalid
    omega
  have hD : digitWeight k B ≤ X-q*B := by omega
  have hsum : c+(q*B+digitWeight k B)=X := by
    calc
      c+(q*B+digitWeight k B) =
          (X-q*B-digitWeight k B)+(q*B+digitWeight k B) := by rw [hcarry]
      _ = (X-q*B-digitWeight k B+digitWeight k B)+q*B := by omega
      _ = (X-q*B)+q*B := by rw [Nat.sub_add_cancel hD]
      _ = X := Nat.sub_add_cancel hqB
  have hdiv : 2^k ∣ 2^k*z := ⟨z,rfl⟩
  have hzmod : (2^k*z)%2^k=0 := Nat.dvd_iff_mod_eq_zero.mp hdiv
  have hXmod : X%2^k=digits ys%2^k := by
    dsimp [X]
    rw [Nat.add_mod,hzmod]
    simp
  let S := q*B+digitWeight k B
  have hsumEq : c+S=X := by simpa [S] using hsum
  have hsumMod : ((c%2^k)+(S%2^k))%2^k=digits ys%2^k := by
    calc
      ((c%2^k)+(S%2^k))%2^k = (c+S)%2^k := by rw [← Nat.add_mod]
      _ = X%2^k := by rw [hsumEq]
      _ = digits ys%2^k := hXmod
  have hM : 0<2^k := Nat.two_pow_pos _
  have ha : c%2^k<2^k := Nat.mod_lt _ hM
  have hb : S%2^k<2^k := Nat.mod_lt _ hM
  have hy : digits ys%2^k<2^k := Nat.mod_lt _ hM
  have hres := mod_sub_residue (2^k) (c%2^k) (S%2^k)
    (digits ys%2^k) hM ha hb hy hsumMod
  refine ⟨by simpa [q,k] using hc,B,hB,?_⟩
  simpa [q,k,S] using hres

#print axioms mod_sub_residue
#print axioms walk_mem_jump

end BB6.Agent9ReverseBlock
