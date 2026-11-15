import CountedLBinDec
import Lean.Elab.Tactic.Omega

open BB6Coverage.Agent48Champion
namespace BB6Coverage.Agent42CountedLBinDec

theorem sweptRightB_preserve_left (n : Nat) (T : Int → Bool) (h x : Int)
    (hx : x < h) : sweptRightB n T h x = T x := by
  induction n generalizing T h with
  | zero => rfl
  | succ n ih =>
    have hx' : x < h+3 := by omega
    have htail := ih (afterRightB3 T h) (h+3) hx'
    have hn0 : x ≠ h := by omega
    have hn1 : x ≠ h+1 := by omega
    have hn2 : x ≠ h+2 := by omega
    simpa [sweptRightB, afterRightB3, hn0, hn1, hn2] using htail

theorem sweptRightB_preserve_right (n : Nat) (T : Int → Bool) (h x : Int)
    (hx : x ≥ h+3*(n:Int)) : sweptRightB n T h x = T x := by
  induction n generalizing T h with
  | zero => rfl
  | succ n ih =>
    have hx' : x ≥ (h+3)+3*(n:Int) := by omega
    have htail := ih (afterRightB3 T h) (h+3) hx'
    have hn0 : x ≠ h := by omega
    have hn1 : x ≠ h+1 := by omega
    have hn2 : x ≠ h+2 := by omega
    simpa [sweptRightB, afterRightB3, hn0, hn1, hn2] using htail

theorem sweptRightB_block (n : Nat) (T : Int → Bool) (h : Int) (i : Nat)
    (hi : i<n) :
    sweptRightB n T h (h+3*(i:Int)) = false ∧
    sweptRightB n T h (h+3*(i:Int)+1) = false ∧
    sweptRightB n T h (h+3*(i:Int)+2) = true := by
  induction n generalizing T h i with
  | zero => omega
  | succ n ih =>
    cases i with
    | zero =>
      have p0 := sweptRightB_preserve_left n (afterRightB3 T h) (h+3) h (by omega)
      have p1 := sweptRightB_preserve_left n (afterRightB3 T h) (h+3) (h+1) (by omega)
      have p2 := sweptRightB_preserve_left n (afterRightB3 T h) (h+3) (h+2) (by omega)
      have hn20 : h+2 ≠ h := by omega
      have hn21 : h+2 ≠ h+1 := by omega
      constructor
      · simpa [sweptRightB, afterRightB3, p0]
      constructor
      · simpa [sweptRightB, afterRightB3, p1]
      · simpa [sweptRightB, afterRightB3, p2, hn20, hn21]
    | succ j =>
      have hj : j<n := by omega
      have hv := ih (afterRightB3 T h) (h+3) j hj
      have e0 : h+3*((j+1:Int)) = h+3+3*(j:Int) := by omega
      have e1 : h+3*((j+1:Int))+1 = h+3+3*(j:Int)+1 := by omega
      have e2 : h+3*((j+1:Int))+2 = h+3+3*(j:Int)+2 := by omega
      constructor
      · simpa [sweptRightB, e0] using hv.1
      constructor
      · simpa [sweptRightB, e1] using hv.2.1
      · simpa [sweptRightB, e2] using hv.2.2

theorem HComposedTape_preserve_right (n : Nat) (T : Int → Bool) (h x : Int)
    (hx : x ≥ h+2) : HComposedTape n T h x = T x := by
  let h' : Int := h-(3*n:Int)
  have hleft := sweptLeft_preserve_right (3*n) T h x (by omega)
  have hmid : afterDZero4 (sweptLeft (3*n) T h) h' x = T x := by
    simp [afterDZero4, hleft]
    omega
  have hright := sweptRightB_preserve_right n
    (afterDZero4 (sweptLeft (3*n) T h) h') (h'+2) x (by omega)
  change sweptRightB n (afterDZero4 (sweptLeft (3*n) T h) h') (h'+2) x = T x
  rw [hright]
  exact hmid

theorem HComposedTape_preserve_left (n : Nat) (T : Int → Bool) (h x : Int)
    (hx : x ≤ h-(3*n:Int)-3) : HComposedTape n T h x = T x := by
  let h' : Int := h-(3*n:Int)
  have hleft := sweptLeft_preserve_left (3*n) T h x (by omega)
  have hmid : afterDZero4 (sweptLeft (3*n) T h) h' x = T x := by
    simp [afterDZero4, hleft]
    omega
  have hright := sweptRightB_preserve_left n
    (afterDZero4 (sweptLeft (3*n) T h) h') (h'+2) x (by omega)
  change sweptRightB n (afterDZero4 (sweptLeft (3*n) T h) h') (h'+2) x = T x
  rw [hright]
  exact hmid

-- Extensional tape description of the LInc target: nearest-first stream
-- [1] ++ d0^n ++ d1, with both exterior contexts unchanged.
def HOutputShape (n : Nat) (T U : Int → Bool) (h : Int) : Prop :=
  U (h+1) = true ∧
  (∀ j : Nat, j<n → U (h-3*(j:Int)) = false ∧
    U (h-3*(j:Int)-1) = false ∧ U (h-3*(j:Int)-2) = true) ∧
  U (h-(3*n:Int)) = true ∧
  U (h-(3*n:Int)-1) = true ∧
  U (h-(3*n:Int)-2) = true ∧
  (∀ x : Int, x ≥ h+2 → U x = T x) ∧
  (∀ x : Int, x ≤ h-(3*n:Int)-3 → U x = T x)

theorem HComposedTape_has_shape (n : Nat) (T : Int → Bool) (h : Int)
    (hon : leftOnes T h (3*n)) (hr : T (h+1) = false)
    (hd0a : T (h-(3*n:Int)) = false)
    (hd0b : T (h-(3*n:Int)-1) = false)
    (hd0c : T (h-(3*n:Int)-2) = true) :
    HOutputShape n T (HComposedTape n T h) h := by
  let h' : Int := h-(3*n:Int)
  let s : Int := h'+2
  let base : Int → Bool := afterDZero4 (sweptLeft (3*n) T h) h'
  have hbase0 : sweptLeft (3*n) T h (h'-1) = false := by
    rw [sweptLeft_preserve_left (3*n) T h (h'-1) (by dsimp [h']; omega)]
    simpa [h'] using hd0b
  have hbase1 : sweptLeft (3*n) T h h' = false := by
    rw [sweptLeft_preserve_left (3*n) T h h' (by dsimp [h']; omega)]
    simpa [h'] using hd0a
  have hbase2 : sweptLeft (3*n) T h (h'+1) = false := by
    simpa [h'] using sweptLeft_zero_right (3*n) T h hr
  have hright : rightOnes (sweptLeft (3*n) T h) s n := by
    simpa [s,h'] using sweptLeft_rightOnes n T h hon hr
  have hprefix : HComposedTape n T h (h+1) = true := by
    cases n with
    | zero => simp [HComposedTape, sweptRightB, afterDZero4]
    | succ n =>
      have hb := sweptRightB_block (n+1) base s n (by omega)
      have heq : s+3*(n:Int)+2 = h+1 := by dsimp [s,h']; omega
      change sweptRightB (n+1) base s (h+1) = true
      rw [← heq]
      exact hb.2.2
  have hblocks : ∀ j : Nat, j<n →
      HComposedTape n T h (h-3*(j:Int)) = false ∧
      HComposedTape n T h (h-3*(j:Int)-1) = false ∧
      HComposedTape n T h (h-3*(j:Int)-2) = true := by
    intro j hj
    let i : Nat := n-j-1
    have hi : i<n := by dsimp [i]; omega
    have hblock := sweptRightB_block n base s i hi
    have e0 : h-3*(j:Int) = s+3*(i:Int)+1 := by dsimp [i,s,h']; omega
    have e1 : h-3*(j:Int)-1 = s+3*(i:Int) := by dsimp [i,s,h']; omega
    have e2 : h-3*(j:Int)-2 = s+3*(i:Int)-1 := by dsimp [i,s,h']; omega
    constructor
    · change sweptRightB n base s (h-3*(j:Int)) = false
      rw [e0]
      exact hblock.2.1
    constructor
    · change sweptRightB n base s (h-3*(j:Int)-1) = false
      rw [e1]
      exact hblock.1
    · by_cases hi0 : i=0
      · have hp := sweptRightB_preserve_left n base s (s-1) (by omega)
        have hs : s-1 = h'+1 := by dsimp [s]; omega
        have hv : base (s-1) = true := by
          rw [hs]
          simp [base,afterDZero4]
        change sweptRightB n base s (h-3*(j:Int)-2) = true
        rw [e2, hi0]
        simpa using hp.trans hv
      · have ipos : 1 ≤ i := by omega
        let k : Nat := i-1
        have hk : k<n := by dsimp [k]; omega
        have hprev := sweptRightB_block n base s k hk
        have eprev : h-3*(j:Int)-2 = s+3*(k:Int)+2 := by
          dsimp [k,i,s,h']; omega
        change sweptRightB n base s (h-3*(j:Int)-2) = true
        rw [eprev]
        exact hprev.2.2
  have hd1a : HComposedTape n T h h' = true := by
    have hp := sweptRightB_preserve_left n base s h' (by dsimp [s]; omega)
    have hv : base h' = true := by simp [base,afterDZero4,h']
    change sweptRightB n base s h' = true
    exact hp.trans hv
  have hd1b : HComposedTape n T h (h'-1) = true := by
    have hp := sweptRightB_preserve_left n base s (h'-1) (by dsimp [s]; omega)
    have hv : base (h'-1) = true := by simp [base,afterDZero4,h']
    change sweptRightB n base s (h'-1) = true
    exact hp.trans hv
  have hd1c : HComposedTape n T h (h'-2) = true := by
    have hl := sweptLeft_preserve_left (3*n) T h (h'-2) (by dsimp [h']; omega)
    have hm : afterDZero4 (sweptLeft (3*n) T h) h' (h'-2) = true := by
      have heq : afterDZero4 (sweptLeft (3*n) T h) h' (h'-2) =
          sweptLeft (3*n) T h (h'-2) := by
        have e0 : h'-2 ≠ h'-1 := by omega
        have e1 : h'-2 ≠ h' := by omega
        have e2 : h'-2 ≠ h'+1 := by omega
        simp [afterDZero4,e0,e1,e2]
      rw [heq, hl]
      simpa [h'] using hd0c
    have hp := sweptRightB_preserve_left n base s (h'-2) (by dsimp [s]; omega)
    change sweptRightB n base s (h'-2) = true
    exact hp.trans hm
  refine ⟨hprefix, hblocks, hd1a, hd1b, hd1c, ?_, ?_⟩
  · intro x hx
    exact HComposedTape_preserve_right n T h x hx
  · intro x hx
    exact HComposedTape_preserve_left n T h x hx

-- Exact counted form of the source-level LInc H-hypothesis.
theorem counted_LInc_H_exact (n : Nat) (T : Int → Bool) (h : Int)
    (hon : leftOnes T h (3*n)) (hr : T (h+1) = false)
    (hd0a : T (h-(3*n:Int)) = false)
    (hd0b : T (h-(3*n:Int)-1) = false)
    (hd0c : T (h-(3*n:Int)-2) = true) :
    run tm2 (12*n+4) ⟨3,h,T⟩ = some ⟨1,h+2,HComposedTape n T h⟩ ∧
      HOutputShape n T (HComposedTape n T h) h := by
  constructor
  · exact counted_LBinDec_H n T h hon hr hd0a hd0b
  · exact HComposedTape_has_shape n T h hon hr hd0a hd0b hd0c

end BB6Coverage.Agent42CountedLBinDec