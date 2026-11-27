import BB429ResonanceEven

namespace BB429.CoarseExit

set_option maxHeartbeats 20000000

/-- Quantitative low-order error bounds for an arbitrary ordinary-block
    prefix.  Starting with zero U-error and V-error y, the V-error grows
    between 18 and 42 per block.  The U-error is trapped between two
    multiples of the base-four branch word.  These bounds deliberately
    forget the detailed branch word and retain only its Cantor integer. -/
theorem phase_error_bounds
    (P r a y : Int) (n : Nat)
    (U V : Nat → Int) (e ph : Nat → Bool)
    (hU : U 0 = a*P) (hV : V 0 = r*P+y)
    (hs : PhaseBlocks U V e ph n) :
    ∀ i, i≤n →
      y+18*(i:Int) ≤ V i-r*P ∧
      V i-r*P ≤ y+42*(i:Int) ∧
      (-2*(y+42*(i:Int))+6)*word4 e i ≤
        U i-lead r a e i*P ∧
      U i-lead r a e i*P ≤
        (-2*y+54)*word4 e i := by
  intro i hi
  induction i with
  | zero =>
      simp [hU,hV,lead,word4]
  | succ i ih =>
      have hp := ih (by omega)
      obtain ⟨hph,hu,hv⟩ := hs i (by omega)
      simp only [lead,word4,hu,hv]
      cases he : e i <;> cases hh : ph i <;>
        simp [he,hh] at hp ⊢ <;> grind +ring

/-- A base-four 0/1 word whose first temporal digit is true has the
    expected leading-place lower bound. -/
theorem word4_first_true (e : Nat → Bool) (i : Nat)
    (hi : 1≤i) (h0 : e 0=true) :
    (4:Int)^(i-1) ≤ word4 e i := by
  induction i with
  | zero => omega
  | succ i ih =>
      by_cases hz : i=0
      · subst i
        simp [word4,h0]
      · have hi' : 1≤i := by omega
        have hh := ih hi' h0
        simp only [word4,Int.pow_succ]
        have hb : 0≤(if e i then (1:Int) else 0) := by
          cases e i <;> simp
        have heq : (i+1-1)=i := by omega
        rw [heq]
        have hm := Int.mul_le_mul_of_nonneg_left hh (by decide : (0:Int)≤4)
        omega

/-- A coarse exponential fact used to turn a minimal resonance word into
    strong scale separation. -/
theorem pow4_ge_500_index (i : Nat) (hi : 7≤i) :
    500*i ≤ 4^(i-1) := by
  obtain ⟨k,rfl⟩ : ∃ k, i=7+k := ⟨i-7,by omega⟩
  induction k with
  | zero => decide
  | succ k ih =>
      rw [show 7+(k+1)-1=(7+k-1)+1 by omega,Nat.pow_succ]
      have hpos : 1≤7+k := by omega
      omega

#print axioms phase_error_bounds
#print axioms word4_first_true
#print axioms pow4_ge_500_index

end BB429.CoarseExit
