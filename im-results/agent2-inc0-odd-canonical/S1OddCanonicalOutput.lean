import S1Encoder
import CountedOddUnary
import Lean.Elab.Tactic.Omega

namespace BB6Coverage.Agent2OddCanonical

open BB6Coverage
open BB6Coverage.Agent8S1Encoder
open BB6Coverage.Agent48Champion

set_option maxHeartbeats 3000000

private theorem sideBit_append_before (xs ys : List Bool) (i : Nat)
    (hi : i < xs.length) :
    sideBit (xs ++ ys) i = sideBit xs i := by
  induction xs generalizing i with
  | nil => simp at hi
  | cons a xs ih =>
      cases i with
      | zero => rfl
      | succ i =>
          have hi' : i < xs.length := by
            simp only [List.length_cons] at hi
            omega
          simpa [sideBit] using ih i hi'

private theorem sideBit_append_after (xs ys : List Bool) (i : Nat)
    (hi : xs.length ≤ i) :
    sideBit (xs ++ ys) i = sideBit ys (i-xs.length) := by
  induction xs generalizing i with
  | nil => simp
  | cons a xs ih =>
      cases i with
      | zero => simp at hi
      | succ i =>
          have hi' : xs.length ≤ i := by
            simp only [List.length_cons] at hi
            omega
          simpa [sideBit] using ih i hi'

/-- Exact zero-padded lookup in a repeated source digit block. -/
theorem sideBit_d1pow_formula (n i : Nat) :
    sideBit (d1pow n) i = decide (i < 3*n) := by
  induction n generalizing i with
  | zero => simp [d1pow, sideBit]
  | succ n ih =>
      cases i with
      | zero => simp [d1pow, d1, sideBit]
      | succ i =>
          cases i with
          | zero =>
              have h : 1 < 3*(n+1) := by omega
              simp [d1pow, d1, sideBit, h]
          | succ i =>
              cases i with
              | zero =>
                  have h : 2 < 3*(n+1) := by omega
                  simp [d1pow, d1, sideBit, h]
              | succ i =>
                  change sideBit (d1pow n) i = decide (i+3 < 3*(n+1))
                  rw [ih]
                  have h : (i < 3*n) ↔ (i+3 < 3*(n+1)) := by omega
                  simp [h]

/-- The encoded right side is exactly the six-cell guard followed by
3(b+1) marked cells, with zero padding after the block. -/
theorem sideBit_s1PhysicalRight (b i : Nat) :
    sideBit (s1PhysicalRight b) i =
      if i < 6 then
        sideBit ([false,true,true,true,false,false] : List Bool) i
      else decide (i-6 < 3*(b+1)) := by
  rw [s1PhysicalRight_source]
  by_cases hi : i < 6
  · have h := sideBit_append_before
      ([false,true,true,true,false,false] : List Bool)
      (d1pow (b+1)) i (by simpa using hi)
    rw [h]
    simp [hi]
  · have hlen : ([false,true,true,true,false,false] : List Bool).length = 6 := by rfl
    have hi6 : 6 ≤ i := Nat.le_of_not_gt hi
    have hguard : ([false,true,true,true,false,false] : List Bool).length ≤ i := by
      rw [hlen]
      exact hi6
    have h := sideBit_append_after
      ([false,true,true,true,false,false] : List Bool)
      (d1pow (b+1)) i hguard
    rw [h, sideBit_d1pow_formula]
    simp [hi]

/-- Closed tape update for the original odd-counter sweep.  The
prefix frame is untouched outside its six-cell area; the E-zero bridge
marks the three new rightmost cells, and the final left sweep clears
cell 6 while moving the zero one place right. -/
theorem finalSweepTape_formula (c : Nat) (T : Int → Bool)
    (hone : ∀ i : Nat, i < 3*(c+1) → T (7+(i:Int)) = true) :
    finalSweepTape c T =
      (fun x =>
        if x = 6 then false
        else if x = rightStop c+1 then true
        else if x = rightStop c then true
        else if x = rightStop c+2 then true
        else prefixTape T x) := by
  have hn : 5+3*c = (4+3*c)+1 := by omega
  have hon := middle_ones T c hone
  have hr := middle_zero_right T c
  have hs := swept_closed (4+3*c) (middleTape c T) (rightStop c)
    (by simpa [hn] using hon) hr
  have hpos : rightStop c - (4+3*c:Int) = 6 := by
    unfold rightStop
    omega
  have hpos' : rightStop c - ↑(4+3*c) = 6 := by
    rw [Int.natCast_add, Int.natCast_mul]
    exact hpos
  funext x
  change sweptLeft (5+3*c) (middleTape c T) (rightStop c) x = _
  rw [hn]
  have hsx := congrFun hs x
  rw [hpos'] at hsx
  rw [hsx]
  by_cases hx6 : x = 6
  · simp [hx6]
  · by_cases hx1 : x = rightStop c+1
    · simp [hx6,hx1]
    · simp [hx6,hx1,middleTape,afterEZero]

/-- On the S1 right side, the counter block ends exactly at rightStop b. -/
theorem s1Config_right_bit_formula
    (L n m a z b : Nat) (h y : Int) (hy : 7 ≤ y) :
    (s1Config L n m a z b h).tape (h+y) =
      decide (y < rightStop b) := by
  let i : Nat := (y-1).toNat
  have hi : (i:Int) = y-1 := by
    dsimp [i]
    exact Int.toNat_of_nonneg (by omega)
  have hcoord : h+1+(i:Int) = h+y := by omega
  have hcell := s1Config_right_cell L n m a z b h i
  rw [hcoord] at hcell
  have htail := sideBit_append_after
    ([false,true,true,true,false,false] : List Bool)
    (d1pow (b+1)) i (by dsimp [i]; omega)
  rw [s1PhysicalRight_source, htail, sideBit_d1pow_formula] at hcell
  have hindex : (i-6 < 3*(b+1)) ↔ y < rightStop b := by
    have hi' : (i:Int) = y-1 := hi
    unfold rightStop
    omega
  simpa [hindex] using hcell

/-- The exact output tape of the odd-counter source macro is the next
S1 configuration: d0 is replaced by d1 on the left, and the right
counter grows from b+1 to b+2. -/
theorem oddCounterOutput_s1Successor
    (L n m len q b : Nat) (h : Int) (hq : q < 2^len) :
    let P : Int → Bool :=
      fun x => (s1Config L n m (len+1) (2*q+1) b h).tape (h+x)
    ∀ y : Int,
      (oddCounterOutput b P).tape y =
        (s1Config L n m (len+1) (2*q) (b+1) h).tape (h+y) := by
  dsimp
  let P : Int → Bool :=
    fun x => (s1Config L n m (len+1) (2*q+1) b h).tape (h+x)
  let rest : List Bool :=
    binDec len q ++ markerWord m ++ d0 ++ binDec L n ++ lh
  have hsrcList :
      s1LeftFacing L n m (len+1) (2*q+1) = d0 ++ rest := by
    unfold s1LeftFacing rest
    rw [binDec_odd len q hq]
    simp [List.append_assoc]
  have htgtList :
      s1LeftFacing L n m (len+1) (2*q) = d1 ++ rest := by
    unfold s1LeftFacing rest
    rw [binDec_even len q hq]
    simp [List.append_assoc]
  have hone : ∀ i : Nat, i < 3*(b+1) → P (7+(i:Int)) = true := by
    intro i hi
    have hcell := s1Config_right_cell L n m (len+1) (2*q+1) b h (6+i)
    have hcoord : h+1+((6+i:Nat):Int) = h+7+(i:Int) := by omega
    rw [hcoord] at hcell
    have hguardLen : ([false,true,true,true,false,false] : List Bool).length = 6 := by rfl
    have hguardAfter : ([false,true,true,true,false,false] : List Bool).length ≤ 6+i := by
      rw [hguardLen]
      omega
    have htail := sideBit_append_after
      ([false,true,true,true,false,false] : List Bool)
      (d1pow (b+1)) (6+i) hguardAfter
    have hidx : 6+i-([false,true,true,true,false,false] : List Bool).length = i := by
      rw [hguardLen]
      omega
    rw [s1PhysicalRight_source, htail, hidx, sideBit_d1pow_formula] at hcell
    have hbit : decide (i < 3*(b+1)) = true := by simp [hi]
    rw [hbit] at hcell
    simpa [P] using hcell
  have hfinal := finalSweepTape_formula b P hone
  have hstop : rightStop b = 10+3*b := rfl
  intro y
  by_cases hyNeg : y ≤ -2
  · have harea : tailArea y = false := by
      simp [tailArea]
      omega
    have hpre : prefixTape P y = P y := by
      have hp : prefArea y = false := by
        simp [prefArea]
        omega
      simp [prefixTape,frame,hp]
    have hfinaly : finalSweepTape b P y = P y := by
      have h6 : y ≠ 6 := by omega
      have h1 : y ≠ rightStop b+1 := by unfold rightStop; omega
      have h0 : y ≠ rightStop b := by unfold rightStop; omega
      have h2 : y ≠ rightStop b+2 := by unfold rightStop; omega
      have hv := congrFun hfinal y
      simp [h6,h1,h0,h2,hpre] at hv
      exact hv
    have hout : (oddCounterOutput b P).tape y = P y := by
      simp [oddCounterOutput,frame,tailArea,harea,hfinaly]
    let i : Nat := (-y).toNat
    have hi : (i:Int) = -y := by
      dsimp [i]
      exact Int.toNat_of_nonneg (by omega)
    have hcoord : h-(i:Int) = h+y := by omega
    have hsrc := s1Config_left_cell L n m (len+1) (2*q+1) b h i
    rw [hcoord,hsrcList] at hsrc
    have htgt := s1Config_left_cell L n m (len+1) (2*q) (b+1) h i
    rw [hcoord,htgtList] at htgt
    have hbit : sideBit (d0 ++ rest) i = sideBit (d1 ++ rest) i := by
      by_cases hi2 : i=2
      · subst i
        have hd0 : sideBit d0 2 = true := by simp [sideBit,d0]
        have hd1 : sideBit d1 2 = true := by simp [sideBit,d1]
        rw [sideBit_append_before d0 rest 2 (by simp [d0])]
        rw [sideBit_append_before d1 rest 2 (by simp [d1])]
        rw [hd0,hd1]
      · have hi3 : 3 ≤ i := by omega
        rw [sideBit_append_after d0 rest i (by simp [d0]; omega)]
        rw [sideBit_append_after d1 rest i (by simp [d1]; omega)]
        simp [d0,d1]
    have hP : P y = sideBit (d0 ++ rest) i := by
      simpa [P] using hsrc
    have htarget : (s1Config L n m (len+1) (2*q) (b+1) h).tape (h+y) = P y := by
      rw [htgt,hP]
      exact hbit.symm
    rw [hout,htarget]
  · by_cases hyNeg1 : y = -1
    · have harea : tailArea y = true := by simp [tailArea,hyNeg1]
      have hout : (oddCounterOutput b P).tape y = true := by
        simp [oddCounterOutput,frame,tailArea,harea,embed,tailFinal,hyNeg1]
      have hcoord : h-(1:Nat) = h+y := by omega
      have htgt := s1Config_left_cell L n m (len+1) (2*q) (b+1) h 1
      rw [hcoord,htgtList] at htgt
      have htarget : (s1Config L n m (len+1) (2*q) (b+1) h).tape (h+y) = true := by
        simpa [sideBit,d1] using htgt
      rw [hout,htarget]
    · by_cases hy0 : y = 0
      · have harea : tailArea y = true := by simp [tailArea,hy0]
        have hout : (oddCounterOutput b P).tape y = true := by
          simp [oddCounterOutput,frame,tailArea,harea,embed,tailFinal,hy0]
        have htgt := s1Config_left_cell L n m (len+1) (2*q) (b+1) h 0
        rw [htgtList] at htgt
        have htarget : (s1Config L n m (len+1) (2*q) (b+1) h).tape (h+y) = true := by
          simpa [hy0,sideBit,d1] using htgt
        rw [hout,htarget]
      · by_cases hySmall : 1 ≤ y ∧ y ≤ 6
        · have hcases : y=1 ∨ y=2 ∨ y=3 ∨ y=4 ∨ y=5 ∨ y=6 := by omega
          rcases hcases with h1 | h2 | h3 | h4 | h5 | h6
          · subst y
            have hout : (oddCounterOutput b P).tape 1 = false := by
              simp [oddCounterOutput,frame,tailArea,embed,tailFinal]
            have htgt := s1Config_right_cell L n m (len+1) (2*q) (b+1) h 0
            have hcoord : h+1+(0:Nat) = h+1 := by omega
            rw [hcoord,s1PhysicalRight_source] at htgt
            have hside : sideBit
                (([false,true,true,true,false,false] : List Bool) ++ d1pow (b+2)) 0 = false := by
              rfl
            rw [hside] at htgt
            simpa using hout.trans htgt.symm
          · subst y
            have hout : (oddCounterOutput b P).tape 2 = true := by
              simp [oddCounterOutput,frame,tailArea,embed,tailFinal]
            have htgt := s1Config_right_cell L n m (len+1) (2*q) (b+1) h 1
            have hcoord : h+1+(1:Nat) = h+2 := by omega
            rw [hcoord,s1PhysicalRight_source] at htgt
            have hside : sideBit
                (([false,true,true,true,false,false] : List Bool) ++ d1pow (b+2)) 1 = true := by
              rfl
            rw [hside] at htgt
            simpa using hout.trans htgt.symm
          · subst y
            have hout : (oddCounterOutput b P).tape 3 = true := by
              simp [oddCounterOutput,frame,tailArea,embed,tailFinal]
            have htgt := s1Config_right_cell L n m (len+1) (2*q) (b+1) h 2
            have hcoord : h+1+(2:Nat) = h+3 := by omega
            rw [hcoord,s1PhysicalRight_source] at htgt
            have hside : sideBit
                (([false,true,true,true,false,false] : List Bool) ++ d1pow (b+2)) 2 = true := by
              rfl
            rw [hside] at htgt
            simpa using hout.trans htgt.symm
          · subst y
            have hout : (oddCounterOutput b P).tape 4 = true := by
              simp [oddCounterOutput,frame,tailArea,embed,tailFinal]
            have htgt := s1Config_right_cell L n m (len+1) (2*q) (b+1) h 3
            have hcoord : h+1+(3:Nat) = h+4 := by omega
            rw [hcoord,s1PhysicalRight_source] at htgt
            have hside : sideBit
                (([false,true,true,true,false,false] : List Bool) ++ d1pow (b+2)) 3 = true := by
              rfl
            rw [hside] at htgt
            simpa using hout.trans htgt.symm
          · subst y
            have hout : (oddCounterOutput b P).tape 5 = false := by
              simp [oddCounterOutput,frame,tailArea,embed,tailFinal]
            have htgt := s1Config_right_cell L n m (len+1) (2*q) (b+1) h 4
            have hcoord : h+1+(4:Nat) = h+5 := by omega
            rw [hcoord,s1PhysicalRight_source] at htgt
            have hside : sideBit
                (([false,true,true,true,false,false] : List Bool) ++ d1pow (b+2)) 4 = false := by
              rfl
            rw [hside] at htgt
            simpa using hout.trans htgt.symm
          · subst y
            have hout : (oddCounterOutput b P).tape 6 = false := by
              simp [oddCounterOutput,frame,tailArea,embed,tailFinal]
            have htgt := s1Config_right_cell L n m (len+1) (2*q) (b+1) h 5
            have hcoord : h+1+(5:Nat) = h+6 := by omega
            rw [hcoord,s1PhysicalRight_source] at htgt
            have hside : sideBit
                (([false,true,true,true,false,false] : List Bool) ++ d1pow (b+2)) 5 = false := by
              rfl
            rw [hside] at htgt
            simpa using hout.trans htgt.symm
        · have hy7 : 7 ≤ y := by omega
          have harea : tailArea y = false := by
            simp [tailArea]
            omega
          have hpre : prefixTape P y = P y :=
            prefixTape_external P y (by omega)
          have hfinaly := congrFun hfinal y
          have hPbit : P y = decide (y < rightStop b) := by
            simpa [P] using
              s1Config_right_bit_formula L n m (len+1) (2*q+1) b h y hy7
          have hout : (oddCounterOutput b P).tape y =
              decide (y < rightStop (b+1)) := by
            simp [oddCounterOutput,frame,tailArea,harea,hpre] at *
            rw [hfinaly]
            simp [hpre,hPbit]
            have hstop : rightStop (b+1) = rightStop b + 3 := by
              simp only [rightStop, Int.natCast_add]
              omega
            have hcut :
                (if y = rightStop b+1 then true
                 else if y = rightStop b then true
                 else if y = rightStop b+2 then true
                 else decide (y < rightStop b)) =
                decide (y < rightStop (b+1)) := by
              by_cases hs1 : y = rightStop b+1
              · have hineq : rightStop b+1 < rightStop b+3 := by omega
                simp [hs1,hstop,hineq]
              · by_cases hs0 : y = rightStop b
                · have hineq : rightStop b < rightStop b+3 := by omega
                  simp [hs0,hstop,hineq]
                · by_cases hs2 : y = rightStop b+2
                  · have hineq : rightStop b+2 < rightStop b+3 := by omega
                    simp [hs2,hstop,hineq]
                  · have hiff : (y < rightStop b) ↔ (y < rightStop (b+1)) := by
                      rw [hstop]
                      omega
                    simp [hs1,hs0,hs2,hiff]
            exact hcut
          have htarget := s1Config_right_bit_formula
            L n m (len+1) (2*q) (b+1) h y hy7
          rw [hout,htarget]

#print axioms sideBit_append_before
#print axioms sideBit_append_after
#print axioms sideBit_d1pow_formula
#print axioms sideBit_s1PhysicalRight
#print axioms s1Config_right_bit_formula
#print axioms finalSweepTape_formula
#print axioms oddCounterOutput_s1Successor

end BB6Coverage.Agent2OddCanonical
