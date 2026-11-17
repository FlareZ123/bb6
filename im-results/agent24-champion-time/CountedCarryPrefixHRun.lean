import CountedCarryPrefix
import CountedCarryLeftOutput
import CountedLBinDecShape
import Lean.Elab.Tactic.Omega

namespace BB6Coverage.Agent24CountedLBinDec

open BB6Coverage
open BB6Coverage.Agent48Champion
open BB6Coverage.Agent3CarryLeftOutput
open BB6Coverage.Agent42CountedLBinDec

set_option maxHeartbeats 1000000

/-- A raw-step chain determines the corresponding counted run. -/
private theorem run_of_rawSteps (m : Machine) :
    ∀ (n : Nat) (f : Nat → Config),
      (∀ i, i < n → rawStep m (f i) = some (f (i+1))) →
      run m n (f 0) = some (f n) := by
  intro n
  induction n with
  | zero =>
      intro f hs
      simp [run]
  | succ n ih =>
      intro f hs
      have hprev : run m n (f 0) = some (f n) :=
        ih f (fun i hi => hs i (by omega))
      rw [run, hprev]
      simp [hs n (by omega)]

private def putAt (T : Int → Bool) (p : Int) (v : Bool) : Int → Bool :=
  fun x => if x = p then v else T x

private def b11T1 (T : Int → Bool) (h : Int) := putAt T (h+2) false
private def b11T2 (T : Int → Bool) (h : Int) := putAt (b11T1 T h) (h+3) false
private def b11T3 (T : Int → Bool) (h : Int) := putAt (b11T2 T h) (h+4) true
private def b11T4 (T : Int → Bool) (h : Int) := putAt (b11T3 T h) (h+5) true
private def b11T5 (T : Int → Bool) (h : Int) := putAt (b11T4 T h) (h+4) false
private def b11T6 (T : Int → Bool) (h : Int) := putAt (b11T5 T h) (h+3) false
private def b11T7 (T : Int → Bool) (h : Int) := putAt (b11T6 T h) (h+2) true
private def b11T8 (T : Int → Bool) (h : Int) := putAt (b11T7 T h) (h+3) true
private def b11T9 (T : Int → Bool) (h : Int) := putAt (b11T8 T h) (h+4) true
private def b11T10 (T : Int → Bool) (h : Int) := putAt (b11T9 T h) (h+5) false
private def b11T11 (T : Int → Bool) (h : Int) := putAt (b11T10 T h) (h+6) true

private theorem l11 : tm2 ((1 : Fin 6), true) = some ⟨false,true,5⟩ := by rfl
private theorem l51 : tm2 ((5 : Fin 6), true) = some ⟨false,true,3⟩ := by rfl
private theorem l31 : tm2 ((3 : Fin 6), true) = some ⟨true,true,1⟩ := by rfl
private theorem l10 : tm2 ((1 : Fin 6), false) = some ⟨true,false,2⟩ := by rfl
private theorem l21 : tm2 ((2 : Fin 6), true) = some ⟨false,false,3⟩ := by rfl
private theorem l30 : tm2 ((3 : Fin 6), false) = some ⟨false,false,2⟩ := by rfl
private theorem l20 : tm2 ((2 : Fin 6), false) = some ⟨true,true,4⟩ := by rfl
private theorem l40 : tm2 ((4 : Fin 6), false) = some ⟨true,true,0⟩ := by rfl
private theorem l00 : tm2 ((0 : Fin 6), false) = some ⟨true,true,1⟩ := by rfl
private theorem l50 : tm2 ((5 : Fin 6), false) = some ⟨true,true,4⟩ := by rfl

private theorem step0 (T : Int → Bool) (h : Int) (h2 : T (h+2)=true) :
    rawStep tm2 ⟨1,h+2,T⟩ = some ⟨5,h+3,b11T1 T h⟩ := by
  simp [rawStep,readSlot,applyMove,b11T1,h2,l11]
  constructor
  · omega
  · funext x
    by_cases hx : x = h+2 <;> simp [putAt,hx]

private theorem step1 (T : Int → Bool) (h : Int) (h3 : T (h+3)=true) :
    rawStep tm2 ⟨5,h+3,b11T1 T h⟩ = some ⟨3,h+4,b11T2 T h⟩ := by
  have hread : b11T1 T h (h+3)=true := by
    simp [b11T1,putAt,show h+3 ≠ h+2 by omega,h3]
  simp [rawStep,readSlot,applyMove,b11T2,hread,l51]
  constructor
  · omega
  · funext x
    by_cases hx : x = h+3 <;> simp [b11T2,b11T1,putAt,hx]

private theorem step2 (T : Int → Bool) (h : Int) (h4 : T (h+4)=true) :
    rawStep tm2 ⟨3,h+4,b11T2 T h⟩ = some ⟨1,h+5,b11T3 T h⟩ := by
  have hread : b11T2 T h (h+4)=true := by
    simp [b11T2,b11T1,putAt,show h+4 ≠ h+3 by omega,
      show h+4 ≠ h+2 by omega,h4]
  simp [rawStep,readSlot,applyMove,b11T3,hread,l31]
  constructor
  · omega
  · funext x
    by_cases hx : x = h+4 <;> simp [b11T3,b11T2,b11T1,putAt,hx]

private theorem step3 (T : Int → Bool) (h : Int) (h5 : T (h+5)=false) :
    rawStep tm2 ⟨1,h+5,b11T3 T h⟩ = some ⟨2,h+4,b11T4 T h⟩ := by
  have hread : b11T3 T h (h+5)=false := by
    simp [b11T3,b11T2,b11T1,putAt,
      show h+5 ≠ h+4 by omega, show h+5 ≠ h+3 by omega,
      show h+5 ≠ h+2 by omega,h5]
  simp [rawStep,readSlot,applyMove,b11T4,hread,l10]
  constructor
  · omega
  · funext x
    by_cases hx : x = h+5 <;> simp [b11T4,b11T3,b11T2,b11T1,putAt,hx]

private theorem step4 (T : Int → Bool) (h : Int) :
    rawStep tm2 ⟨2,h+4,b11T4 T h⟩ = some ⟨3,h+3,b11T5 T h⟩ := by
  have hread : b11T4 T h (h+4)=true := by
    simp [b11T4,b11T3,b11T2,b11T1,putAt,
      show h+4 ≠ h+5 by omega, show h+4 ≠ h+3 by omega,
      show h+4 ≠ h+2 by omega]
  simp [rawStep,readSlot,applyMove,b11T5,hread,l21]
  constructor
  · omega
  · funext x
    by_cases hx : x = h+4 <;> simp [b11T5,b11T4,b11T3,b11T2,b11T1,putAt,hx]

private theorem step5 (T : Int → Bool) (h : Int) :
    rawStep tm2 ⟨3,h+3,b11T5 T h⟩ = some ⟨2,h+2,b11T6 T h⟩ := by
  have hread : b11T5 T h (h+3)=false := by
    simp [b11T5,b11T4,b11T3,b11T2,b11T1,putAt,
      show h+3 ≠ h+4 by omega, show h+3 ≠ h+5 by omega,
      show h+3 ≠ h+2 by omega]
  simp [rawStep,readSlot,applyMove,b11T6,hread,l30]
  constructor
  · omega
  · funext x
    by_cases hx : x = h+3 <;> simp [b11T6,b11T5,b11T4,b11T3,b11T2,b11T1,putAt,hx]

private theorem step6 (T : Int → Bool) (h : Int) :
    rawStep tm2 ⟨2,h+2,b11T6 T h⟩ = some ⟨4,h+3,b11T7 T h⟩ := by
  have hread : b11T6 T h (h+2)=false := by
    simp [b11T6,b11T5,b11T4,b11T3,b11T2,b11T1,putAt,
      show h+2 ≠ h+3 by omega, show h+2 ≠ h+4 by omega,
      show h+2 ≠ h+5 by omega]
  simp [rawStep,readSlot,applyMove,b11T7,hread,l20]
  constructor
  · omega
  · funext x
    by_cases hx : x = h+2 <;> simp [b11T7,b11T6,b11T5,b11T4,b11T3,b11T2,b11T1,putAt,hx]

private theorem step7 (T : Int → Bool) (h : Int) :
    rawStep tm2 ⟨4,h+3,b11T7 T h⟩ = some ⟨0,h+4,b11T8 T h⟩ := by
  have hread : b11T7 T h (h+3)=false := by
    simp [b11T7,b11T6,b11T5,b11T4,b11T3,b11T2,b11T1,putAt,
      show h+3 ≠ h+2 by omega, show h+3 ≠ h+4 by omega,
      show h+3 ≠ h+5 by omega]
  simp [rawStep,readSlot,applyMove,b11T8,hread,l40]
  constructor
  · omega
  · funext x
    by_cases hx : x = h+3 <;> simp [b11T8,b11T7,b11T6,b11T5,b11T4,b11T3,b11T2,b11T1,putAt,hx]

private theorem step8 (T : Int → Bool) (h : Int) :
    rawStep tm2 ⟨0,h+4,b11T8 T h⟩ = some ⟨1,h+5,b11T9 T h⟩ := by
  have hread : b11T8 T h (h+4)=false := by
    simp [b11T8,b11T7,b11T6,b11T5,b11T4,b11T3,b11T2,b11T1,putAt,
      show h+4 ≠ h+3 by omega, show h+4 ≠ h+2 by omega,
      show h+4 ≠ h+5 by omega]
  simp [rawStep,readSlot,applyMove,b11T9,hread,l00]
  constructor
  · omega
  · funext x
    by_cases hx : x = h+4 <;> simp [b11T9,b11T8,b11T7,b11T6,b11T5,b11T4,b11T3,b11T2,b11T1,putAt,hx]

private theorem step9 (T : Int → Bool) (h : Int) :
    rawStep tm2 ⟨1,h+5,b11T9 T h⟩ = some ⟨5,h+6,b11T10 T h⟩ := by
  have hread : b11T9 T h (h+5)=true := by
    simp [b11T9,b11T8,b11T7,b11T6,b11T5,b11T4,b11T3,b11T2,b11T1,putAt,
      show h+5 ≠ h+4 by omega, show h+5 ≠ h+3 by omega,
      show h+5 ≠ h+2 by omega]
  simp [rawStep,readSlot,applyMove,b11T10,hread,l11]
  constructor
  · omega
  · funext x
    by_cases hx : x = h+5 <;> simp [b11T10,b11T9,b11T8,b11T7,b11T6,b11T5,b11T4,b11T3,b11T2,b11T1,putAt,hx]

private theorem step10 (T : Int → Bool) (h : Int) (h6 : T (h+6)=false) :
    rawStep tm2 ⟨5,h+6,b11T10 T h⟩ = some ⟨4,h+7,b11T11 T h⟩ := by
  have hread : b11T10 T h (h+6)=false := by
    simp [b11T10,b11T9,b11T8,b11T7,b11T6,b11T5,b11T4,b11T3,b11T2,b11T1,putAt,
      show h+6 ≠ h+5 by omega, show h+6 ≠ h+4 by omega,
      show h+6 ≠ h+3 by omega, show h+6 ≠ h+2 by omega,h6]
  simp [rawStep,readSlot,applyMove,b11T11,hread,l50]
  constructor
  · omega
  · funext x
    by_cases hx : x = h+6 <;> simp [b11T11,b11T10,b11T9,b11T8,b11T7,b11T6,b11T5,b11T4,b11T3,b11T2,b11T1,putAt,hx]

private def b11Config (T : Int → Bool) (h : Int) : Nat → Config
  | 0 => ⟨1,h+2,T⟩
  | 1 => ⟨5,h+3,b11T1 T h⟩
  | 2 => ⟨3,h+4,b11T2 T h⟩
  | 3 => ⟨1,h+5,b11T3 T h⟩
  | 4 => ⟨2,h+4,b11T4 T h⟩
  | 5 => ⟨3,h+3,b11T5 T h⟩
  | 6 => ⟨2,h+2,b11T6 T h⟩
  | 7 => ⟨4,h+3,b11T7 T h⟩
  | 8 => ⟨0,h+4,b11T8 T h⟩
  | 9 => ⟨1,h+5,b11T9 T h⟩
  | 10 => ⟨5,h+6,b11T10 T h⟩
  | _ => ⟨4,h+7,b11T11 T h⟩

private theorem b11_step (T : Int → Bool) (h : Int)
    (h2 : T (h+2)=true) (h3 : T (h+3)=true)
    (h4 : T (h+4)=true) (h5 : T (h+5)=false)
    (h6 : T (h+6)=false) :
    ∀ i, i < 11 → rawStep tm2 (b11Config T h i) = some (b11Config T h (i+1)) := by
  intro i hi
  have hcases : i=0 ∨ i=1 ∨ i=2 ∨ i=3 ∨ i=4 ∨ i=5 ∨
      i=6 ∨ i=7 ∨ i=8 ∨ i=9 ∨ i=10 := by omega
  rcases hcases with h0 | h1 | h2' | h3' | h4' | h5' | h6' | h7 | h8 | h9 | h10
  · subst i; simpa [b11Config] using step0 T h h2
  · subst i; simpa [b11Config] using step1 T h h3
  · subst i; simpa [b11Config] using step2 T h h4
  · subst i; simpa [b11Config] using step3 T h h5
  · subst i; simpa [b11Config] using step4 T h
  · subst i; simpa [b11Config] using step5 T h
  · subst i; simpa [b11Config] using step6 T h
  · subst i; simpa [b11Config] using step7 T h
  · subst i; simpa [b11Config] using step8 T h
  · subst i; simpa [b11Config] using step9 T h
  · subst i; simpa [b11Config] using step10 T h h6

/-- The fixed eleven-move bridge after the counted H-run. -/
private theorem counted_B_to_E_11 (T : Int → Bool) (h : Int)
    (h2 : T (h+2)=true) (h3 : T (h+3)=true)
    (h4 : T (h+4)=true) (h5 : T (h+5)=false)
    (h6 : T (h+6)=false) :
    run tm2 11 ⟨1,h+2,T⟩ = some ⟨4,h+7,b11T11 T h⟩ := by
  have hrun := run_of_rawSteps tm2 11 (b11Config T h)
    (b11_step T h h2 h3 h4 h5 h6)
  simpa [b11Config] using hrun

private theorem b11T11_preserve_before2 (T : Int → Bool) (h x : Int)
    (hx : x ≤ h+1) : b11T11 T h x = T x := by
  simp [b11T11,b11T10,b11T9,b11T8,b11T7,b11T6,b11T5,
    b11T4,b11T3,b11T2,b11T1,putAt,
    show x ≠ h+2 by omega, show x ≠ h+3 by omega,
    show x ≠ h+4 by omega, show x ≠ h+5 by omega,
    show x ≠ h+6 by omega]

private theorem b11T11_preserve_right (T : Int → Bool) (h x : Int)
    (hx : h+7 ≤ x) : b11T11 T h x = T x := by
  simp [b11T11,b11T10,b11T9,b11T8,b11T7,b11T6,b11T5,
    b11T4,b11T3,b11T2,b11T1,putAt,
    show x ≠ h+2 by omega, show x ≠ h+3 by omega,
    show x ≠ h+4 by omega, show x ≠ h+5 by omega,
    show x ≠ h+6 by omega]

private theorem b11T11_h2 (T : Int → Bool) (h : Int) :
    b11T11 T h (h+2) = true := by
  simp [b11T11,b11T10,b11T9,b11T8,b11T7,b11T6,b11T5,
    b11T4,b11T3,b11T2,b11T1,putAt] <;> omega

private theorem b11T11_h3 (T : Int → Bool) (h : Int) :
    b11T11 T h (h+3) = true := by
  simp [b11T11,b11T10,b11T9,b11T8,b11T7,b11T6,b11T5,
    b11T4,b11T3,b11T2,b11T1,putAt] <;> omega

private theorem b11T11_h4 (T : Int → Bool) (h : Int) :
    b11T11 T h (h+4) = true := by
  simp [b11T11,b11T10,b11T9,b11T8,b11T7,b11T6,b11T5,
    b11T4,b11T3,b11T2,b11T1,putAt] <;> omega

private theorem b11T11_h5 (T : Int → Bool) (h : Int) :
    b11T11 T h (h+5) = false := by
  simp [b11T11,b11T10,b11T9,b11T8,b11T7,b11T6,b11T5,
    b11T4,b11T3,b11T2,b11T1,putAt] <;> omega

private theorem b11T11_h6 (T : Int → Bool) (h : Int) :
    b11T11 T h (h+6) = true := by
  simp [b11T11,b11T10,b11T9,b11T8,b11T7,b11T6,b11T5,
    b11T4,b11T3,b11T2,b11T1,putAt] <;> omega

/-- The exact left-output word of the counted LInc H-run.  The interior
three-cell blocks are d0, the boundary is d1, and the exterior is untouched. -/
theorem HOutputShape_leftOutput (r : Nat) (T U : Int → Bool)
    (hshape : HOutputShape r T U 0) :
    ∀ x : Int, x ≤ 0 → U x = carryLeftOutputBit r T x := by
  rcases hshape with ⟨_, hblocks, hbase0, hbase1, hbase2, _, hkeepL⟩
  intro x hx
  by_cases hfar : x < -3*(r:Int)-2
  · have hleft : x ≤ 0 - 3*(r:Int)-3 := by omega
    have hkeep := hkeepL x hleft
    simp [carryLeftOutputBit, hfar, hkeep]
  · by_cases hbase : x ≤ -3*(r:Int)
    · have hcases : x = 0 - 3*(r:Int) ∨
        x = 0 - 3*(r:Int)-1 ∨ x = 0 - 3*(r:Int)-2 := by omega
      rcases hcases with h0 | h1 | h2
      · rw [h0]
        have hnotfar : ¬ (-(3*(r:Int)) < -3*(r:Int)-2) := by omega
        have hle : -(3*(r:Int)) ≤ -3*(r:Int) := by omega
        simpa [carryLeftOutputBit, Int.zero_sub, hnotfar, hle] using hbase0
      · rw [h1]
        have hnotfar : ¬ (-(3*(r:Int))-1 < -3*(r:Int)-2) := by omega
        have hle : -(3*(r:Int))-1 ≤ -3*(r:Int) := by omega
        simpa [carryLeftOutputBit, Int.zero_sub, hnotfar, hle] using hbase1
      · rw [h2]
        have hnotfar : ¬ (-(3*(r:Int))-2 < -3*(r:Int)-2) := by omega
        have hle : -(3*(r:Int))-2 ≤ -3*(r:Int) := by omega
        simpa [carryLeftOutputBit, Int.zero_sub, hnotfar, hle] using hbase2
    · have hgt : -3*(r:Int) < x := by omega
      let i : Nat := Int.toNat (-x)
      have hnonneg : 0 ≤ -x := by omega
      have hi : (i:Int) = -x := by
        dsimp [i]
        exact Int.toNat_of_nonneg hnonneg
      have hilt : i < 3*r := by omega
      let j : Nat := i / 3
      have hdiv : i % 3 + 3*j = i := by
        dsimp [j]
        omega
      have hmodlt : i % 3 < 3 := Nat.mod_lt i (by omega)
      have hjlt : j < r := by
        dsimp [j]
        omega
      have hrem : i % 3 = 0 ∨ i % 3 = 1 ∨ i % 3 = 2 := by omega
      rcases hrem with hrem0 | hrem1 | hrem2
      · have hdivI : (i % 3 : Int) + 3*(j:Int) = (i:Int) := by
          exact_mod_cast hdiv
        have hremI : (i % 3 : Int) = 0 := by exact_mod_cast hrem0
        have hxEq : x = -(3*(j:Int)) := by omega
        have hnotfar : ¬ (-(3*(j:Int)) < -3*(r:Int)-2) := by omega
        have hnotbase : ¬ (-(3*(j:Int)) ≤ -3*(r:Int)) := by omega
        have hmod : (-(3*(j:Int))) % 3 = 0 := by omega
        have hval : U (-(3*(j:Int))) = false := by
          simpa [Int.zero_sub] using (hblocks j hjlt).1
        rw [hxEq]
        simp [carryLeftOutputBit, hnotfar, hnotbase, hmod, hval]
      · have hdivI : (i % 3 : Int) + 3*(j:Int) = (i:Int) := by
          exact_mod_cast hdiv
        have hremI : (i % 3 : Int) = 1 := by exact_mod_cast hrem1
        have hxEq : x = -(3*(j:Int))-1 := by omega
        have hnotfar : ¬ (-(3*(j:Int))-1 < -3*(r:Int)-2) := by omega
        have hnotbase : ¬ (-(3*(j:Int))-1 ≤ -3*(r:Int)) := by omega
        have hmod : (-(3*(j:Int))-1) % 3 = 2 := by omega
        have hval : U (-(3*(j:Int))-1) = false := by
          simpa [Int.zero_sub] using (hblocks j hjlt).2.1
        rw [hxEq]
        simp [carryLeftOutputBit, hnotfar, hnotbase, hmod, hval]
      · have hdivI : (i % 3 : Int) + 3*(j:Int) = (i:Int) := by
          exact_mod_cast hdiv
        have hremI : (i % 3 : Int) = 2 := by exact_mod_cast hrem2
        have hxEq : x = -(3*(j:Int))-2 := by omega
        have hnotfar : ¬ (-(3*(j:Int))-2 < -3*(r:Int)-2) := by omega
        have hnotbase : ¬ (-(3*(j:Int))-2 ≤ -3*(r:Int)) := by omega
        have hmod : (-(3*(j:Int))-2) % 3 = 1 := by omega
        have hval : U (-(3*(j:Int))-2) = true := by
          simpa [Int.zero_sub] using (hblocks j hjlt).2.2
        rw [hxEq]
        simp [carryLeftOutputBit, hnotfar, hnotbase, hmod, hval]

end BB6Coverage.Agent24CountedLBinDec

namespace BB6Coverage.Agent48Champion

open BB6Coverage
open BB6Coverage.Agent24CountedLBinDec
open BB6Coverage.Agent3CarryLeftOutput
open BB6Coverage.Agent42CountedLBinDec

set_option maxHeartbeats 1000000

/-- Uniform source-input carry prefix obtained from the exact counted LInc H-run.
Unlike the residue-class construction, this works for every r ≥ 0. -/
theorem carryPrefix_anyNonnegative_hRun (r : Nat) (T : Int → Bool)
    (hmatch : ∀ x, carryInputArea r x = true → T x = carryInputBit r x) :
    ∃ T' : Int → Bool,
      run tm2 (15+12*r) ⟨3,0,T⟩ = some ⟨4,7,T'⟩ ∧
      T' 1 = true ∧ T' 2 = true ∧ T' 3 = true ∧
      T' 4 = true ∧ T' 5 = false ∧ T' 6 = true ∧
      (∀ x, 6 < x → T' x = T x) ∧
      (∀ x, x ≤ 0 → T' x = carryLeftOutputBit r T x) := by
  have hleft : leftOnes T 0 (3*r) := by
    intro i hi
    simpa using carryInput_marked r T hmatch (-(i:Int))
      (Or.inl ⟨by omega,by omega⟩)
  have hright0 : T 1=false := by
    apply carryInput_unmarked r T hmatch 1
    · omega
    · omega
    · intro hbad
      rcases hbad with hbad | hbad | hbad | hbad | hbad <;> omega
  have hd0a : T (-(3*(r:Int)))=false := by
    apply carryInput_unmarked r T hmatch (-(3*(r:Int)))
    · omega
    · omega
    · intro hbad
      rcases hbad with hbad | hbad | hbad | hbad | hbad <;> omega
  have hd0b : T (-(3*(r:Int))-1)=false := by
    apply carryInput_unmarked r T hmatch (-(3*(r:Int))-1)
    · omega
    · omega
    · intro hbad
      rcases hbad with hbad | hbad | hbad | hbad | hbad <;> omega
  have hd0c : T (-(3*(r:Int))-2)=true := by
    have harea : carryInputArea r (-(3*(r:Int))-2)=true := by
      simp [carryInputArea] <;> omega
    have hbit : carryInputBit r (-(3*(r:Int))-2)=true := by
      simp [carryInputBit]
    rw [hmatch _ harea,hbit]
  have h2 : T 2=true := carryInput_marked r T hmatch 2 (Or.inr (Or.inl rfl))
  have h3 : T 3=true := carryInput_marked r T hmatch 3 (Or.inr (Or.inr (Or.inl rfl)))
  have h4 : T 4=true := carryInput_marked r T hmatch 4 (Or.inr (Or.inr (Or.inr rfl)))
  have h5 : T 5=false := by
    apply carryInput_unmarked r T hmatch 5
    · omega
    · omega
    · intro hbad
      rcases hbad with hbad | hbad | hbad | hbad | hbad <;> omega
  have h6 : T 6=false := by
    apply carryInput_unmarked r T hmatch 6
    · omega
    · omega
    · intro hbad
      rcases hbad with hbad | hbad | hbad | hbad | hbad <;> omega
  have hExact := counted_LInc_H_exact r T 0 hleft hright0
    (by simpa using hd0a) (by simpa using hd0b) (by simpa using hd0c)
  let U : Int → Bool := HComposedTape r T 0
  have hHrun : run tm2 (12*r+4) ⟨3,0,T⟩ = some ⟨1,2,U⟩ := by
    simpa [U] using hExact.1
  have hshape : HOutputShape r T U 0 := by
    simpa [U] using hExact.2
  rcases hshape with ⟨hU1,hblocks,hbase0,hbase1,hbase2,hkeepR,hkeepL⟩
  have hshape' : HOutputShape r T U 0 :=
    ⟨hU1,hblocks,hbase0,hbase1,hbase2,hkeepR,hkeepL⟩
  have hU2 : U 2=true := by rw [hkeepR 2 (by omega)]; exact h2
  have hU3 : U 3=true := by rw [hkeepR 3 (by omega)]; exact h3
  have hU4 : U 4=true := by rw [hkeepR 4 (by omega)]; exact h4
  have hU5 : U 5=false := by rw [hkeepR 5 (by omega)]; exact h5
  have hU6 : U 6=false := by rw [hkeepR 6 (by omega)]; exact h6
  have hBridge := counted_B_to_E_11 U 0 hU2 hU3 hU4 hU5 hU6
  let T' : Int → Bool := b11T11 U 0
  have hcost : 15+12*r = (12*r+4)+11 := by omega
  have hrun : run tm2 (15+12*r) ⟨3,0,T⟩ = some ⟨4,7,T'⟩ := by
    rw [hcost,run_append,hHrun]
    simpa [T'] using hBridge
  have h1 : T' 1=true := by
    dsimp [T']
    rw [b11T11_preserve_before2 U 0 1 (by omega)]
    exact hU1
  have h2' : T' 2=true := by simpa [T'] using b11T11_h2 U 0
  have h3' : T' 3=true := by simpa [T'] using b11T11_h3 U 0
  have h4' : T' 4=true := by simpa [T'] using b11T11_h4 U 0
  have h5' : T' 5=false := by simpa [T'] using b11T11_h5 U 0
  have h6' : T' 6=true := by simpa [T'] using b11T11_h6 U 0
  have hout : ∀ x, 6<x → T' x=T x := by
    intro x hx
    dsimp [T']
    calc
      b11T11 U 0 x = U x := b11T11_preserve_right U 0 x (by omega)
      _ = T x := hkeepR x (by omega)
  have hleftU := HOutputShape_leftOutput r T U hshape'
  have hleft : ∀ x, x ≤ 0 → T' x = carryLeftOutputBit r T x := by
    intro x hx
    dsimp [T']
    calc
      b11T11 U 0 x = U x := b11T11_preserve_before2 U 0 x (by omega)
      _ = carryLeftOutputBit r T x := hleftU x hx
  exact ⟨T',hrun,h1,h2',h3',h4',h5',h6',hout,hleft⟩

#print axioms carryPrefix_anyNonnegative_hRun

end BB6Coverage.Agent48Champion
