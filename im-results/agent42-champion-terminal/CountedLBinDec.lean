import CountedSweep
import Lean.Elab.Tactic.Omega

open BB6Coverage.Agent48Champion
namespace BB6Coverage.Agent42CountedLBinDec

-- B/F/D is the rightward rotation of the D/B/F three-cell sweep.
def afterRightB3 (T : Int → Bool) (h : Int) : Int → Bool :=
  fun x => if x=h || x=h+1 then false else if x=h+2 then true else T x

private theorem lookup11_B : tm2 ((1 : Fin 6), true) = some ⟨false,true,5⟩ := by rfl
private theorem lookup51_B : tm2 ((5 : Fin 6), true) = some ⟨false,true,3⟩ := by rfl
private theorem lookup31_B : tm2 ((3 : Fin 6), true) = some ⟨true,true,1⟩ := by rfl

theorem counted_three_right_B (T : Int → Bool) (h : Int)
    (h0 : T h = true) (h1 : T (h+1) = true) (h2 : T (h+2) = true) :
    run tm2 3 ⟨1,h,T⟩ = some ⟨1,h+3,afterRightB3 T h⟩ := by
  have neq1 : h+1 ≠ h := by omega
  have neq2 : h+2 ≠ h := by omega
  have neq3 : h+2 ≠ h+1 := by omega
  have hh : h+1+1=h+2 := by omega
  have neh1 : h≠h+1 := by omega
  have neh2 : h≠h+2 := by omega
  simp [run,rawStep,readSlot,applyMove,h0,h1,h2,hh,
    lookup11_B,lookup51_B,lookup31_B,neq1,neq2,neq3]
  constructor
  · omega
  · funext x
    by_cases hx1 : x=h+1 <;> by_cases hx2 : x=h+2 <;>
      by_cases hx0 : x=h <;>
      simp [afterRightB3,hx1,hx2,hx0,h0,neh1,neh2] <;> omega

def sweptRightB : Nat → (Int → Bool) → Int → (Int → Bool)
  | 0,T,_ => T
  | n+1,T,h => sweptRightB n (afterRightB3 T h) (h+3)

private theorem rightOnesB_tail (T : Int → Bool) (h : Int) (n : Nat)
    (hon : rightOnes T h (n+1)) :
    rightOnes (afterRightB3 T h) (h+3) n := by
  intro i hi
  obtain ⟨a,b,c⟩ := hon (i+1) (by omega)
  have e0 : h+3+3*(i:Int) = h+3*((i+1:Int)) := by omega
  have e1 : h+3+3*(i:Int)+1 = h+3*((i+1:Int))+1 := by omega
  have e2 : h+3+3*(i:Int)+2 = h+3*((i+1:Int))+2 := by omega
  have n00 : h+3*((i+1:Int)) ≠ h := by omega
  have n01 : h+3*((i+1:Int)) ≠ h+1 := by omega
  have n02 : h+3*((i+1:Int)) ≠ h+2 := by omega
  have n10 : h+3*((i+1:Int))+1 ≠ h := by omega
  have n11 : h+3*((i+1:Int))+1 ≠ h+1 := by omega
  have n12 : h+3*((i+1:Int))+1 ≠ h+2 := by omega
  have n20 : h+3*((i+1:Int))+2 ≠ h := by omega
  have n21 : h+3*((i+1:Int))+2 ≠ h+1 := by omega
  have n22 : h+3*((i+1:Int))+2 ≠ h+2 := by omega
  constructor
  · rw [e0]
    simpa [afterRightB3, n00, n01, n02] using a
  constructor
  · rw [e1]
    simpa [afterRightB3, n10, n11, n12] using b
  · rw [e2]
    simpa [afterRightB3, n20, n21, n22] using c

theorem counted_right_sweep_B (n : Nat) (T : Int → Bool) (h : Int)
    (hon : rightOnes T h n) :
    run tm2 (3*n) ⟨1,h,T⟩ =
      some ⟨1,h+3*(n:Int),sweptRightB n T h⟩ := by
  induction n generalizing T h with
  | zero => simp [run,sweptRightB]
  | succ n ih =>
    obtain ⟨h0raw,h1raw,h2raw⟩ := hon 0 (by omega)
    have h0 : T h = true := by simpa using h0raw
    have h1 : T (h+1) = true := by simpa using h1raw
    have h2 : T (h+2) = true := by simpa using h2raw
    have hstep := counted_three_right_B T h h0 h1 h2
    have hon' := rightOnesB_tail T h n hon
    have htail := ih (afterRightB3 T h) (h+3) hon'
    have hnum : 3*(n+1) = 3+3*n := by omega
    rw [hnum,run_append,hstep]
    simp only [Option.bind_some]
    rw [htail]
    have hhead : h+3+3*(n:Int) = h+3*((n+1:Int)) := by omega
    simpa [sweptRightB,hhead]

-- Four-step D/C/E/A bridge between the two sweeps.
def afterDZero4 (T : Int → Bool) (h : Int) : Int → Bool :=
  fun x => if x=h-1 || x=h || x=h+1 then true else T x

private theorem lookup30 : tm2 ((3 : Fin 6), false) = some ⟨false,false,2⟩ := by rfl
private theorem lookup20 : tm2 ((2 : Fin 6), false) = some ⟨true,true,4⟩ := by rfl
private theorem lookup40 : tm2 ((4 : Fin 6), false) = some ⟨true,true,0⟩ := by rfl
private theorem lookup00 : tm2 ((0 : Fin 6), false) = some ⟨true,true,1⟩ := by rfl

theorem D_zero_bridge (T : Int → Bool) (h : Int)
    (h0 : T (h-1) = false) (h1 : T h = false) (h2 : T (h+1) = false) :
    run tm2 4 ⟨3,h,T⟩ = some ⟨1,h+2,afterDZero4 T h⟩ := by
  have e01 : h-1 ≠ h := by omega
  have e01' : h ≠ h-1 := by omega
  have e02 : h+1 ≠ h := by omega
  have e12 : h+1 ≠ h-1 := by omega
  have hleft : h + (-1) = h-1 := by omega
  have hback : h-1+1=h := by omega
  have hforward : h+1+(-1)=h := by omega
  simp [run,rawStep,readSlot,applyMove,h0,h1,h2,e01,e01',e02,e12,hleft,hback,hforward,
    lookup30,lookup20,lookup40,lookup00]
  constructor
  · omega
  · funext x
    by_cases hx0 : x=h-1 <;> by_cases hx1 : x=h <;> by_cases hx2 : x=h+1 <;>
      simp [afterDZero4,hx0,hx1,hx2] <;> omega

theorem rightOnes_afterDZero4 (T : Int → Bool) (h : Int) (n : Nat)
    (hon : rightOnes T (h+2) n) :
    rightOnes (afterDZero4 T h) (h+2) n := by
  intro i hi
  obtain ⟨a,b,c⟩ := hon i hi
  have x0 : h+2+3*(i:Int) ≠ h-1 := by omega
  have x1 : h+2+3*(i:Int) ≠ h := by omega
  have x2 : h+2+3*(i:Int) ≠ h+1 := by omega
  have y0 : h+2+3*(i:Int)+1 ≠ h-1 := by omega
  have y1 : h+2+3*(i:Int)+1 ≠ h := by omega
  have y2 : h+2+3*(i:Int)+1 ≠ h+1 := by omega
  have z0 : h+2+3*(i:Int)+2 ≠ h-1 := by omega
  have z1 : h+2+3*(i:Int)+2 ≠ h := by omega
  have z2 : h+2+3*(i:Int)+2 ≠ h+1 := by omega
  constructor
  · simpa [afterDZero4,x0,x1,x2] using a
  constructor
  · simpa [afterDZero4,y0,y1,y2] using b
  · simpa [afterDZero4,z0,z1,z2] using c

-- Composed exact run. The remaining tape-pattern obligations are explicit inputs.
def HComposedTape (n : Nat) (T : Int → Bool) (h : Int) : Int → Bool :=
  sweptRightB n
    (afterDZero4 (sweptLeft (3*n) T h) (h-(3*n:Int)))
    (h-(3*n:Int)+2)

theorem counted_LBinDec_H_composed (n : Nat) (T : Int → Bool) (h : Int)
    (hon : leftOnes T h (3*n)) (hr : T (h+1) = false)
    (hbase0 : sweptLeft (3*n) T h (h-(3*n:Int)-1) = false)
    (hbase1 : sweptLeft (3*n) T h (h-(3*n:Int)) = false)
    (hbase2 : sweptLeft (3*n) T h (h-(3*n:Int)+1) = false)
    (hright : rightOnes (sweptLeft (3*n) T h) (h-(3*n:Int)+2) n) :
    run tm2 (12*n+4) ⟨3,h,T⟩ = some ⟨1,h+2,HComposedTape n T h⟩ := by
  let h' : Int := h-(3*n:Int)
  have hleft := counted_left_sweep (3*n) T h hon hr
  have hbase := D_zero_bridge (sweptLeft (3*n) T h) h' hbase0 hbase1 hbase2
  have hbase' : run tm2 4 ⟨3,h-(↑(3*n):Int),sweptLeft (3*n) T h⟩ =
      some ⟨1,h-(↑(3*n):Int)+2,afterDZero4 (sweptLeft (3*n) T h) (h-(↑(3*n):Int))⟩ := by
    simpa [h', Int.natCast_mul] using hbase
  have hright' : rightOnes (afterDZero4 (sweptLeft (3*n) T h) (h-(↑(3*n):Int)))
      (h-(↑(3*n):Int)+2) n := by
    have hh := rightOnes_afterDZero4 (sweptLeft (3*n) T h) (h-(↑(3*n):Int)) n hright
    simpa [Int.natCast_mul] using hh
  have hrightRun := counted_right_sweep_B n
    (afterDZero4 (sweptLeft (3*n) T h) (h-(↑(3*n):Int))) (h-(↑(3*n):Int)+2) hright'
  have htime : 12*n+4 = (3*(3*n)+4)+3*n := by omega
  rw [htime, run_append (m:=tm2) (c:=⟨3,h,T⟩) (a:=3*(3*n)+4) (b:=3*n)]
  rw [run_append (m:=tm2) (c:=⟨3,h,T⟩) (a:=3*(3*n)) (b:=4), hleft]
  simp only [Option.bind_some]
  rw [hbase']
  simp only [Option.bind_some]
  rw [hrightRun]
  congr 2 <;> simp [HComposedTape, Int.natCast_mul] <;> omega

-- The left sweep does not alter cells strictly beyond its right boundary.
theorem sweptLeft_preserve_right (n : Nat) (T : Int → Bool) (h x : Int)
    (hx : x > h+1) : sweptLeft n T h x = T x := by
  induction n generalizing T h with
  | zero => simp [sweptLeft]
  | succ n ih =>
    have hx' : x > (h-1)+1 := by omega
    have htail := ih (holeThree T h) (h-1) hx'
    have hn0 : x ≠ h := by omega
    have hn1 : x ≠ h+1 := by omega
    simpa [sweptLeft, htail, holeThree, hn0, hn1]

-- The left sweep does not alter cells at or left of its final head position.
theorem sweptLeft_preserve_left (n : Nat) (T : Int → Bool) (h x : Int)
    (hx : x ≤ h-(n:Int)) : sweptLeft n T h x = T x := by
  induction n generalizing T h with
  | zero => rfl
  | succ n ih =>
    have hx' : x ≤ (h-1)-(n:Int) := by omega
    have htail := ih (holeThree T h) (h-1) hx'
    have hn0 : x ≠ h := by omega
    have hn1 : x ≠ h+1 := by omega
    simpa [sweptLeft, htail, holeThree, hn0, hn1]

-- The initial zero at h+1 is shifted to the right-neighbor of the final head.
theorem sweptLeft_zero_right (n : Nat) (T : Int → Bool) (h : Int)
    (hr : T (h+1) = false) :
    sweptLeft n T h (h-(n:Int)+1) = false := by
  induction n generalizing T h with
  | zero => simpa [sweptLeft] using hr
  | succ n ih =>
    have hr' : holeThree T h ((h-1)+1) = false := by
      have hne : h ≠ h+1 := by omega
      simp [holeThree, show (h-1)+1=h by omega, hne]
    have htail := ih (holeThree T h) (h-1) hr'
    have hcoord : (h-1)-(n:Int)+1 = h-(n+1:Int)+1 := by omega
    simpa [sweptLeft, hcoord] using htail

-- A contiguous run of n ones is shifted one cell right by the left sweep.
theorem sweptLeft_shifted_ones (n : Nat) (T : Int → Bool) (h : Int)
    (hon : leftOnes T h n) (hr : T (h+1) = false) :
    ∀ i : Nat, i<n → sweptLeft n T h (h-(n:Int)+2+(i:Int)) = true := by
  induction n generalizing T h with
  | zero => intro i hi; omega
  | succ n ih =>
    have hon' : leftOnes (holeThree T h) (h-1) n := leftOnes_tail T h n hon
    have hr' : holeThree T h ((h-1)+1) = false := by
      have hne : h ≠ h+1 := by omega
      simp [holeThree, show (h-1)+1=h by omega, hne]
    have htail := ih (holeThree T h) (h-1) hon' hr'
    intro i hi
    by_cases hlast : i=n
    · subst i
      have hpres := sweptLeft_preserve_right n (holeThree T h) (h-1) (h+1) (by omega)
      have hval : holeThree T h (h+1) = true := by simp [holeThree]
      have hcoord : h-(n+1:Int)+2+(n:Int) = h+1 := by omega
      simpa [sweptLeft, hcoord, hpres, hval]
    · have hi' : i<n := by omega
      have hcoord : h-(n+1:Int)+2+(i:Int) = (h-1)-(n:Int)+2+(i:Int) := by omega
      have hv := htail i hi'
      simpa [sweptLeft, hcoord] using hv

-- Group the shifted run into n consecutive three-one blocks.
theorem sweptLeft_rightOnes (n : Nat) (T : Int → Bool) (h : Int)
    (hon : leftOnes T h (3*n)) (hr : T (h+1) = false) :
    rightOnes (sweptLeft (3*n) T h) (h-(3*n:Int)+2) n := by
  intro i hi
  have h0 := sweptLeft_shifted_ones (3*n) T h hon hr (3*i) (by omega)
  have h1 := sweptLeft_shifted_ones (3*n) T h hon hr (3*i+1) (by omega)
  have h2 := sweptLeft_shifted_ones (3*n) T h hon hr (3*i+2) (by omega)
  have e0 : h-(3*n:Int)+2+(3*i:Int) = h-(3*n:Int)+2+3*(i:Int) := by omega
  have e1 : h-(3*n:Int)+2+((3*i+1:Int)) = h-(3*n:Int)+2+3*(i:Int)+1 := by omega
  have e2 : h-(3*n:Int)+2+((3*i+2:Int)) = h-(3*n:Int)+2+3*(i:Int)+2 := by omega
  constructor
  · simpa [e0] using h0
  constructor
  · simpa [e1] using h1
  · simpa [e2] using h2

-- The full arbitrary-context H-run, with only the d0 boundary hypotheses exposed.
theorem counted_LBinDec_H (n : Nat) (T : Int → Bool) (h : Int)
    (hon : leftOnes T h (3*n)) (hr : T (h+1) = false)
    (hd0a : T (h-(3*n:Int)) = false)
    (hd0b : T (h-(3*n:Int)-1) = false) :
    run tm2 (12*n+4) ⟨3,h,T⟩ = some ⟨1,h+2,HComposedTape n T h⟩ := by
  have hbase0 : sweptLeft (3*n) T h (h-(3*n:Int)-1) = false := by
    rw [sweptLeft_preserve_left (3*n) T h (h-(3*n:Int)-1) (by omega)]
    exact hd0b
  have hbase1 : sweptLeft (3*n) T h (h-(3*n:Int)) = false := by
    rw [sweptLeft_preserve_left (3*n) T h (h-(3*n:Int)) (by omega)]
    exact hd0a
  have hbase2 : sweptLeft (3*n) T h (h-(3*n:Int)+1) = false :=
    sweptLeft_zero_right (3*n) T h hr
  have hright : rightOnes (sweptLeft (3*n) T h) (h-(3*n:Int)+2) n :=
    sweptLeft_rightOnes n T h hon hr
  exact counted_LBinDec_H_composed n T h hon hr hbase0 hbase1 hbase2 hright

end BB6Coverage.Agent42CountedLBinDec