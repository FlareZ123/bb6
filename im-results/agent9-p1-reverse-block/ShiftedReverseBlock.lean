import ReverseBlock
import WeightedDigitGap
import JumpResidueCore

namespace BB6.Agent9ShiftedReverse
open BB6.Agent45ReverseBlock
open BB6.Agent45WeightedDigitGap (le_corr corr_le_mul digitWeight)
open BB6.Agent9JumpResidue (corr_extend_zero corr_extend_one)

/-- Removing the unit coefficient of every bit halves the worst-case range. -/
theorem corr_shift_bound (k B : Nat) (hB : B < 2^k) :
    corr k B + k + 1 ≤ B + 2^k := by
  induction k generalizing B with
  | zero =>
    have h : B = 0 := by simpa using hB
    simp [h,corr]
  | succ k ih =>
    have h : B/2 < 2^k := by rw [Nat.pow_succ] at hB; omega
    have hh := ih (B/2) h
    rcases (show B%2=0 ∨ B%2=1 by omega) with h0|h1
    · simp only [corr,h0,Nat.mul_zero,Nat.add_zero,Nat.pow_succ]
      omega
    · simp only [corr,h1,Nat.mul_one,Nat.pow_succ]
      omega

/-- The same two-candidate search now fits 2^k ≤ F-1. -/
theorem shifted_word_near (F k X B a : Nat) (hk : 0<k)
    (hfit : 2^k ≤ F-1) (hB : B<2^k) (ha : a<F-k)
    (he : X+corr k B=F*B+a) :
    X/(F-1) ≤ B ∧ B ≤ X/(F-1)+1 := by
  let G := F-1
  have hG : 0<G := by have := Nat.two_pow_pos k; omega
  have hc := le_corr k B hB
  have hbound := corr_shift_bound k B hB
  have hF : F=G+1 := by dsimp [G] at *; omega
  have hprod : F*B=G*B+B := by rw [hF,Nat.add_mul,Nat.one_mul]
  rw [hprod] at he
  have hfit' : 2^k ≤ G := hfit
  have ha' : a<G := by omega
  have hlo : X<G*(B+1) := by rw [Nat.mul_add,Nat.mul_one]; omega
  have hhi : G*B<X+G := by omega
  have hdiv := Nat.div_add_mod X G
  have hrem := Nat.mod_lt X hG
  have htop : X+G<G*(X/G+2) := by rw [Nat.mul_add]; omega
  have hmul : G*B<G*(X/G+2) := Nat.lt_trans hhi htop
  have hl := (Nat.div_lt_iff_lt_mul hG).2 (by simpa [Nat.mul_comm] using hlo)
  have hh := Nat.lt_of_mul_lt_mul_left hmul
  change X/G≤B ∧ B≤X/G+1
  omega

def shiftedFast (F k X : Nat) : Option Nat :=
  match candidate F k X (X/(F-1)) with
  | some a => some a
  | none => candidate F k X (X/(F-1)+1)

theorem shiftedFast_iff (F k X a : Nat) (hk : 0<k)
    (hfit : 2^k≤F-1) :
    shiftedFast F k X=some a ↔
      ∃ B, B<2^k ∧ a<F-k ∧ X+corr k B=F*B+a := by
  constructor
  · intro h
    unfold shiftedFast at h
    split at h <;> rename_i he
    · simp only [Option.some.injEq] at h
      subst a
      exact ⟨_,(candidate_iff _ _ _ _ _).1 he⟩
    · exact ⟨_,(candidate_iff _ _ _ _ _).1 h⟩
  · rintro ⟨B,hB,ha,he⟩
    have hn := shifted_word_near F k X B a hk hfit hB ha he
    have hc := (candidate_iff F k X B a).2 ⟨hB,ha,he⟩
    by_cases h0 : B=X/(F-1)
    · rw [h0] at hc
      simp [shiftedFast,hc]
    · have h1 : B=X/(F-1)+1 := by omega
      rw [h1] at hc
      cases hp : candidate F k X (X/(F-1)) with
      | none => simp [shiftedFast,hp,hc]
      | some a' =>
        have heq := (candidate_unique F k X _ _ a' a hp hc).1
        omega

/-- Twice the excess of the lowest set bit of B+1 over one, truncated at k. -/
def carryGap : Nat → Nat → Nat
  | 0,_ => 0
  | k+1,B => if B%2=0 then 0 else 2*carryGap k (B/2)+2

theorem corr_adjacent_gap (k B : Nat) :
    corr k B+k=corr k (B+1)+carryGap k B := by
  induction k generalizing B with
  | zero => simp [corr,carryGap]
  | succ k ih =>
    by_cases h : B%2=0
    · have h1 : (B+1)%2=1 := by omega
      have h2 : (B+1)/2=B/2 := by omega
      simp only [corr,carryGap,h,h1,h2,if_pos,Nat.mul_zero,Nat.add_zero,Nat.mul_one]
    · have h0 : B%2=1 := by omega
      have h1 : (B+1)%2=0 := by omega
      have h2 : (B+1)/2=B/2+1 := by omega
      have hi := ih (B/2)
      simp only [corr,carryGap,h,h0,h1,h2,if_neg,Nat.mul_zero,Nat.add_zero,Nat.mul_one]
      simp at *
      omega

theorem weight_adjacent (q k B : Nat) (hB : B+1<2^k) :
    q*(B+1)+digitWeight k (B+1) =
      q*B+digitWeight k B+q+carryGap k B := by
  have h0 := corr_le_mul k B (by omega : B<2^k)
  have h1 := corr_le_mul k (B+1) hB
  have h := corr_adjacent_gap k B
  unfold digitWeight
  simp only [Nat.mul_add,Nat.mul_one] at *
  omega

def Valid (q k X a : Nat) : Prop :=
  ∃ B, B<2^k ∧ a<q ∧ X+corr k B=(q+k)*B+a

/-- A top selected bit is determined by a single exact comparison. -/
theorem valid_split (q k X a : Nat) :
    Valid q (k+1) X a ↔
      if X<(q+k)*2^k then Valid q k X a
      else Valid q k (X-(q+k)*2^k) a := by
  let H := 2^k
  let W := (q+k)*H
  change Valid q (k+1) X a ↔ if X<W then Valid q k X a else Valid q k (X-W) a
  constructor
  · rintro ⟨B,hB,ha,he⟩
    by_cases hlow : B<H
    · have hc := le_corr (k+1) B hB
      have heq := corr_extend_zero k B hlow
      have hprod : (q+(k+1))*B=(q+k)*B+B := by
        rw [show q+(k+1)=q+k+1 by omega,Nat.add_mul,Nat.one_mul]
      rw [hprod,heq] at he
      have hb : (q+k)*(B+1)≤W := Nat.mul_le_mul_left _ (by omega)
      rw [Nat.mul_add,Nat.mul_one] at hb
      have hx : X<W := by omega
      rw [if_pos hx]
      exact ⟨B,hlow,ha,by omega⟩
    · let L := B-H
      have hL : L<2^k := by dsimp [L,H] at *; rw [Nat.pow_succ] at hB; omega
      have hb : B=L+2^k := by dsimp [L,H] at *; omega
      rw [hb,corr_extend_one k L hL,corr_extend_zero k L hL] at he
      have hp : (q+(k+1))*(L+2^k)=(q+k)*L+L+W+2^k := by
        dsimp [W,H]
        rw [show q+(k+1)=q+k+1 by omega,Nat.mul_add]
        simp only [Nat.add_mul,Nat.one_mul]
        ac_rfl
      rw [hp] at he
      have hcorr := corr_le_mul k L hL
      have hmul : k*L≤(q+k)*L := Nat.mul_le_mul_right _ (by omega)
      have hx : W≤X := by omega
      rw [if_neg (by omega : ¬ X<W)]
      exact ⟨L,hL,ha,by omega⟩
  · by_cases hx : X<W
    · rw [if_pos hx]
      rintro ⟨B,hB,ha,he⟩
      refine ⟨B,by rw [Nat.pow_succ]; omega,ha,?_⟩
      rw [corr_extend_zero k B hB,show q+(k+1)=q+k+1 by omega,Nat.add_mul,Nat.one_mul]
      omega
    · rw [if_neg hx]
      rintro ⟨L,hL,ha,he⟩
      refine ⟨L+2^k,by rw [Nat.pow_succ]; omega,ha,?_⟩
      rw [corr_extend_one k L hL,corr_extend_zero k L hL]
      have hp : (q+(k+1))*(L+2^k)=(q+k)*L+L+W+2^k := by
        dsimp [W,H]
        rw [show q+(k+1)=q+k+1 by omega,Nat.mul_add]
        simp only [Nat.add_mul,Nat.one_mul]
        ac_rfl
      rw [hp]
      omega

def greedyFast (q r : Nat) : Nat → Nat → Option Nat
  | 0,X => shiftedFast (q+r) r X
  | t+1,X =>
    let W := (q+(r+t))*2^(r+t)
    if X<W then greedyFast q r t X else greedyFast q r t (X-W)

theorem greedyFast_iff (q r t X a : Nat) (hr : 0<r)
    (hfit : 2^r≤q+r-1) :
    greedyFast q r t X=some a ↔ Valid q (r+t) X a := by
  induction t generalizing X with
  | zero =>
    simpa [greedyFast,Valid,Nat.add_sub_cancel] using
      shiftedFast_iff (q+r) r X a hr hfit
  | succ t ih =>
    rw [show r+(t+1)=r+t+1 by omega,valid_split]
    simp only [greedyFast]
    by_cases h : X<(q+(r+t))*2^(r+t)
    · simp only [if_pos h]
      exact ih X
    · simp only [if_neg h]
      exact ih _

theorem greedyFast_iff_walk (q r t z a : Nat) (ys : List Nat)
    (hlen : ys.length=r+t) (hr : 0<r) (hfit : 2^r≤q+r-1)
    (hys : ∀ y∈ys, y≤1) :
    greedyFast q r t (2^ys.length*z+digits ys)=some a ↔
      Walk (q+ys.length) z ys a := by
  rw [greedyFast_iff q r t _ a hr hfit]
  constructor
  · rintro ⟨B,hB,ha,he⟩
    rw [←hlen] at hB he
    exact walk_of_eq _ _ _ _ _ hys hB (by simpa using ha) he
  · intro hw
    obtain ⟨B,hB,he⟩ := eq_of_walk hw
    have ha := walk_bound hw
    rw [hlen] at hB he
    exact ⟨B,hB,by simpa using ha,by simpa only [hlen] using he⟩

#print axioms corr_shift_bound
#print axioms shifted_word_near
#print axioms shiftedFast_iff
#print axioms corr_adjacent_gap
#print axioms weight_adjacent
#print axioms valid_split
#print axioms greedyFast_iff
#print axioms greedyFast_iff_walk
end BB6.Agent9ShiftedReverse
