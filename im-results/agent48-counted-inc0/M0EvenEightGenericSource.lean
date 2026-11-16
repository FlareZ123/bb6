import M0EvenEightQ4Prefix
import Q4RightEndpoint
import S1CountedDrain
import Lean.Elab.Tactic.Omega

/-!
# Generic marker-0, n=8q counted source increment

This closes the q4 endpoint for every odd quotient q.  The proof uses the
63-step finite bridge, the 3a-cell left sweep, the 3(a-1)-cell E-scan,
the shared q4 suffix, and the already formalized all-valuation S1 drain.
All statements are about the original TM63 transition table and an arbitrary
blank-exterior S1 configuration.
-/

namespace BB6Coverage.Agent48M0EvenEightGenericSource

open BB6Coverage
open BB6Coverage.Agent48Champion
open BB6Coverage.Agent8S1Encoder
open BB6Coverage.Agent8CountedReset
open BB6Coverage.Agent6Q4Prefix
open BB6Coverage.Agent8Q4Suffix
open BB6Coverage.Agent24Q4Endpoint
open BB6Coverage.Agent48M0EvenEightQ4Bridge
open BB6Coverage.Agent48M0EvenEightQ4Prefix
open BB6Coverage.Agent48CountedInc0

set_option maxHeartbeats 3000000

private theorem sideBit_false_after_length_local
    (xs : List Bool) (i : Nat) (hi : xs.length ≤ i) :
    sideBit xs i = false := by
  induction xs generalizing i with
  | nil =>
      simp [sideBit]
  | cons x xs ih =>
      cases i with
      | zero =>
          simp at hi
      | succ i =>
          have hi' : xs.length ≤ i := by simp at hi; omega
          simpa [sideBit] using ih i hi'

private theorem m0EvenEightQ4CutTape_eq_swept
    (L q a b : Nat) (h x : Int)
    (hout : m0EvenEightInside
      (x-(h-((3*a : Nat) : Int))) = false) :
    m0EvenEightQ4CutTape L q a b h x =
      sweptLeft (3*a) (s1Config L (8*q) 0 a 0 b h).tape h x := by
  let T := (s1Config L (8*q) 0 a 0 b h).tape
  let N := 3*a
  let T1 := sweptLeft N T h
  have hf := frameAt_tape_outside T1 (h-(N:Int))
    m0EvenEightInside m0EvenEightBridgeEnd x hout
  simpa [m0EvenEightQ4CutTape,T,N,T1] using hf

private theorem m0EvenEightQ4CutTape_eq_end_inside
    (L q a b : Nat) (h x : Int)
    (hin : m0EvenEightInside
      (x-(h-((3*a : Nat) : Int))) = true) :
    m0EvenEightQ4CutTape L q a b h x =
      decide ((x-(h-((3*a : Nat) : Int))) ∈
        m0EvenEightBridgeEnd.marked) := by
  let T := (s1Config L (8*q) 0 a 0 b h).tape
  let N := 3*a
  let T1 := sweptLeft N T h
  have hf := frameAt_tape_inside T1 (h-(N:Int))
    m0EvenEightInside m0EvenEightBridgeEnd x hin
  simpa [m0EvenEightQ4CutTape,T,N,T1] using hf

private theorem m0EvenEightQ4CutTape_eq_source_right
    (L q a b : Nat) (h x : Int)
    (ha : 0 < a) (hx : h+2 ≤ x) :
    m0EvenEightQ4CutTape L q a b h x =
      (s1Config L (8*q) 0 a 0 b h).tape x := by
  let T := (s1Config L (8*q) 0 a 0 b h).tape
  have hgt : 3 < x-(h-((3*a : Nat) : Int)) := by omega
  have hnot : ¬(-15 ≤ x-(h-((3*a : Nat) : Int)) ∧
      x-(h-((3*a : Nat) : Int)) ≤ 3) := by omega
  have hout : m0EvenEightInside
      (x-(h-((3*a : Nat) : Int))) = false := by
    change decide (-15 ≤ x-(h-((3*a : Nat) : Int)) ∧
      x-(h-((3*a : Nat) : Int)) ≤ 3) = false
    exact decide_eq_false_iff_not.mpr hnot
  have hcut := m0EvenEightQ4CutTape_eq_swept L q a b h x hout
  have hpres := sweptLeft_preserves_right (3*a) T h x (by omega)
  simpa [T] using hcut.trans hpres

private theorem m0EvenEightQ4CutTape_sourceRightCell
    (L q a b : Nat) (h : Int) (j : Nat)
    (ha : 0 < a) (hj : 1 ≤ j) :
    m0EvenEightQ4CutTape L q a b h (h+1+(j:Int)) =
      sideBit (s1PhysicalRight b) j := by
  have hx : h+2 ≤ h+1+(j:Int) := by omega
  rw [m0EvenEightQ4CutTape_eq_source_right L q a b h
    (h+1+(j:Int)) ha hx]
  exact s1Config_right_cell L (8*q) 0 a 0 b h j

private theorem m0EvenEightQ4CutTape_head_true
    (L q a b : Nat) (h : Int) (ha : 0 < a) :
    m0EvenEightQ4CutTape L q a b h h = true := by
  let T := (s1Config L (8*q) 0 a 0 b h).tape
  by_cases ha1 : a = 1
  · subst a
    have hcoord : h-(h-((3*1:Nat):Int)) = 3 := by omega
    have hin : m0EvenEightInside
        (h-(h-((3*1:Nat):Int))) = true := by
      rw [hcoord]
      decide
    rw [m0EvenEightQ4CutTape_eq_end_inside L q 1 b h h hin]
    rw [hcoord]
    simp [m0EvenEightBridgeEnd]
  · have ha2 : 2 ≤ a := by omega
    have hcoord : h-(h-((3*a:Nat):Int)) = (3*a:Int) := by omega
    have hout : m0EvenEightInside
        (h-(h-((3*a:Nat):Int))) = false := by
      rw [hcoord]
      change decide (-15 ≤ (3*a:Int) ∧ (3*a:Int) ≤ 3) = false
      apply decide_eq_false_iff_not.mpr
      omega
    rw [m0EvenEightQ4CutTape_eq_swept L q a b h h hout]
    have hN : (3*a-2)+2 = 3*a := by omega
    rw [← hN]
    exact sweptLeft_head (3*a-2) T h

private theorem m0EvenEightQ4CutTape_plus1_true
    (L q a b : Nat) (h : Int) (ha : 0 < a) :
    m0EvenEightQ4CutTape L q a b h (h+1) = true := by
  let T := (s1Config L (8*q) 0 a 0 b h).tape
  have hcoord :
      (h+1)-(h-((3*a:Nat):Int)) = (3*a:Int)+1 := by omega
  have hout : m0EvenEightInside
      ((h+1)-(h-((3*a:Nat):Int))) = false := by
    rw [hcoord]
    change decide (-15 ≤ (3*a:Int)+1 ∧ (3*a:Int)+1 ≤ 3) = false
    apply decide_eq_false_iff_not.mpr
    omega
  rw [m0EvenEightQ4CutTape_eq_swept L q a b h (h+1) hout]
  have hN : (3*a-1)+1 = 3*a := by omega
  rw [← hN]
  exact sweptLeft_plus1 (3*a-1) T h

private theorem m0EvenEightQ4LeftPrefix_last
    (a : Nat) (ha : 0 < a) :
    sideBit ([true] ++ d1pow (a-1)) (3*a-3) = true := by
  by_cases ha1 : a = 1
  · subst a
    simp [sideBit]
  · have ha2 : 2 ≤ a := by omega
    rw [sideBit_append_right [true] (d1pow (a-1)) (3*a-3)
      (by simp; omega)]
    have hidx : 3*a-3-1 = 3*a-4 := by omega
    rw [hidx]
    exact sideBit_d1pow_true (a-1) (3*a-4) (by omega)

private theorem m0EvenEightQ4LeftPrefix_allTrue
    (a i : Nat) (ha : 0 < a) (hi : i < 3*a-2) :
    sideBit ([true] ++ d1pow (a-1)) i = true := by
  by_cases hi0 : i = 0
  · subst i
    simp [sideBit]
  · rw [sideBit_append_right [true] (d1pow (a-1)) i
      (by simp; omega)]
    exact sideBit_d1pow_true (a-1) (i-1) (by omega)

private theorem m0EvenEightQ4LeftFacing_bridge_bit
    (L q a k : Nat) (ha : 0 < a) (hk : k ≤ 18) :
    sideBit (m0EvenEightQ4LeftFacing L q a) (3*a-3+k) =
      decide ((3-(k:Int)) ∈ m0EvenEightBridgeEnd.marked) := by
  let prefix := [true] ++ d1pow (a-1)
  let rest := markerWord 2 ++ d0 ++ d0 ++ d0 ++ d0 ++ d1 ++
    binDec (L-4) (q/2) ++ lh
  have hsplit : m0EvenEightQ4LeftFacing L q a = prefix ++ rest := by
    simp [m0EvenEightQ4LeftFacing,prefix,rest,List.append_assoc]
  have hlen : prefix.length = 3*a-2 := by
    simp [prefix,d1pow_length]
    omega
  by_cases hk0 : k = 0
  · subst k
    rw [hsplit]
    have hbefore : 3*a-3 < prefix.length := by rw [hlen]; omega
    rw [sideBit_append_left prefix rest (3*a-3) hbefore]
    rw [m0EvenEightQ4LeftPrefix_last a ha]
    simp [m0EvenEightBridgeEnd]
  · have hkpos : 1 ≤ k := by omega
    rw [hsplit]
    have hafter : prefix.length ≤ 3*a-3+k := by rw [hlen]; omega
    rw [sideBit_append_right prefix rest (3*a-3+k) hafter]
    have hidx : 3*a-3+k-prefix.length = k-1 := by rw [hlen]; omega
    rw [hidx]
    have hc :
        k=1 ∨ k=2 ∨ k=3 ∨ k=4 ∨ k=5 ∨ k=6 ∨
        k=7 ∨ k=8 ∨ k=9 ∨ k=10 ∨ k=11 ∨ k=12 ∨
        k=13 ∨ k=14 ∨ k=15 ∨ k=16 ∨ k=17 ∨ k=18 := by omega
    rcases hc with h1 | h2 | h3 | h4 | h5 | h6 | h7 | h8 | h9 |
      h10 | h11 | h12 | h13 | h14 | h15 | h16 | h17 | h18 <;>
      subst k <;>
      simp [prefix,rest,markerWord,d0,d1,sideBit,m0EvenEightBridgeEnd]

private theorem m0EvenEightQ4_target_tail_equiv
    (L q a i : Nat) (hL : 4 ≤ L) (hqodd : q % 2 = 1)
    (hbound : 8*q < 2^L) (ha : 0 < a)
    (hi : 3*a+16 ≤ i) :
    sideBit (s1LeftFacing L (8*q) 0 a 0) i =
      sideBit (m0EvenEightQ4LeftFacing L q a) i := by
  let tail := [true] ++ binDec (L-4) (q/2) ++ lh
  let sourcePrefix := d1pow a ++ markerWord 0 ++ d0 ++
    d1 ++ d1 ++ d1 ++ [false,false]
  let targetPrefix := [true] ++ d1pow (a-1) ++ markerWord 2 ++
    d0 ++ d0 ++ d0 ++ d0 ++ [true,true]
  have hface :
      s1LeftFacing L (8*q) 0 a 0 =
        d1pow a ++ m0EvenEightSourceLeftSuffix L q := by
    simp [s1LeftFacing,m0EvenEightSourceLeftSuffix,
      m0EvenEight_binDec_residue8 L q hL hqodd hbound,
      List.append_assoc]
  have hsource :
      s1LeftFacing L (8*q) 0 a 0 = sourcePrefix ++ tail := by
    rw [hface]
    simp [m0EvenEightSourceLeftSuffix,sourcePrefix,tail,
      markerWord,d0,d1,List.append_assoc]
  have htarget :
      m0EvenEightQ4LeftFacing L q a = targetPrefix ++ tail := by
    simp [m0EvenEightQ4LeftFacing,targetPrefix,tail,
      markerWord,d0,d1,List.append_assoc]
  have hlenSource : sourcePrefix.length = 3*a+16 := by
    simp [sourcePrefix,d1pow_length,markerWord,d0,d1]
    omega
  have hlenTarget : targetPrefix.length = 3*a+16 := by
    simp [targetPrefix,d1pow_length,markerWord,d0,d1]
    omega
  rw [hsource,htarget]
  rw [sideBit_append_right sourcePrefix tail i
    (by rw [hlenSource]; omega)]
  rw [sideBit_append_right targetPrefix tail i
    (by rw [hlenTarget]; omega)]
  rw [hlenSource,hlenTarget]

private theorem m0EvenEightQ4LeftFacing_prefix_true
    (L q a i : Nat) (ha : 0 < a) (hi : i < 3*a-2) :
    sideBit (m0EvenEightQ4LeftFacing L q a) i = true := by
  let prefix := [true] ++ d1pow (a-1)
  let rest := markerWord 2 ++ d0 ++ d0 ++ d0 ++ d0 ++ d1 ++
    binDec (L-4) (q/2) ++ lh
  have hsplit : m0EvenEightQ4LeftFacing L q a = prefix ++ rest := by
    simp [m0EvenEightQ4LeftFacing,prefix,rest,List.append_assoc]
  have hlen : prefix.length = 3*a-2 := by
    simp [prefix,d1pow_length]
    omega
  rw [hsplit]
  rw [sideBit_append_left prefix rest i (by rw [hlen]; omega)]
  exact m0EvenEightQ4LeftPrefix_allTrue a i ha hi

 /-- Full left-facing stream at the q4 cut, including the unbounded source tail. -/
theorem m0EvenEight_q4_prefix_leftFacing
    (L q a b : Nat) (h : Int)
    (hL : 4 ≤ L) (hqodd : q % 2 = 1)
    (hbound : 8*q < 2^L) (ha : 0 < a) :
    ∀ i : Nat,
      m0EvenEightQ4CutTape L q a b h (h-(i:Int)) =
        sideBit (m0EvenEightQ4LeftFacing L q a) i := by
  intro i
  let T := (s1Config L (8*q) 0 a 0 b h).tape
  by_cases hsmall : i < 3*a-3
  · have hgt : 3 < (h-(i:Int))-(h-((3*a:Nat):Int)) := by omega
    have hnot : ¬(-15 ≤ (h-(i:Int))-(h-((3*a:Nat):Int)) ∧
        (h-(i:Int))-(h-((3*a:Nat):Int)) ≤ 3) := by omega
    have hout : m0EvenEightInside
        ((h-(i:Int))-(h-((3*a:Nat):Int))) = false := by
      change decide (-15 ≤ (h-(i:Int))-(h-((3*a:Nat):Int)) ∧
        (h-(i:Int))-(h-((3*a:Nat):Int)) ≤ 3) = false
      exact decide_eq_false_iff_not.mpr hnot
    rw [m0EvenEightQ4CutTape_eq_swept L q a b h
      (h-(i:Int)) hout]
    have hblock := sweptLeft_block (3*a) i T h (by omega)
    rw [hblock]
    exact m0EvenEightQ4LeftFacing_prefix_true L q a i ha (by omega)
  · by_cases hmid : i ≤ 3*a+15
    · let k := i-(3*a-3)
      have hk : k ≤ 18 := by dsimp [k]; omega
      have hcoord :
          (h-(i:Int))-(h-((3*a:Nat):Int)) = 3-(k:Int) := by
        dsimp [k]
        omega
      have hineq : -15 ≤ 3-(k:Int) ∧ 3-(k:Int) ≤ 3 := by omega
      have hin : m0EvenEightInside
          ((h-(i:Int))-(h-((3*a:Nat):Int))) = true := by
        rw [hcoord]
        change decide (-15 ≤ 3-(k:Int) ∧ 3-(k:Int) ≤ 3) = true
        simp [hineq]
      rw [m0EvenEightQ4CutTape_eq_end_inside L q a b h
        (h-(i:Int)) hin]
      rw [hcoord]
      exact m0EvenEightQ4LeftFacing_bridge_bit L q a k ha hk
    · have htail : 3*a+16 ≤ i := by omega
      have hout : m0EvenEightInside
          ((h-(i:Int))-(h-((3*a:Nat):Int))) = false := by
        have hcoord :
            (h-(i:Int))-(h-((3*a:Nat):Int)) = (3*a:Int)-(i:Int) := by omega
        rw [hcoord]
        change decide (-15 ≤ (3*a:Int)-(i:Int) ∧
          (3*a:Int)-(i:Int) ≤ 3) = false
        apply decide_eq_false_iff_not.mpr
        omega
      rw [m0EvenEightQ4CutTape_eq_swept L q a b h
        (h-(i:Int)) hout]
      have hpres := sweptLeft_preserves_left (3*a) T h
        (h-(i:Int)) (by omega)
      rw [hpres]
      rw [s1Config_left_cell L (8*q) 0 a 0 b h i]
      exact m0EvenEightQ4_target_tail_equiv L q a i
        hL hqodd hbound ha htail

/-- The entire right-facing q4 guard, not merely its five blank tail cells. -/
theorem m0EvenEight_q4_prefix_rightShape
    (L q a b : Nat) (h : Int)
    (hL : 4 ≤ L) (hqodd : q % 2 = 1)
    (hbound : 8*q < 2^L) (ha : 0 < a) :
    q4RightShape (m0EvenEightQ4CutTape L q a b h) h b := by
  refine ⟨?_,?_,?_,?_,?_⟩
  · intro i hi
    have hc : i=0 ∨ i=1 ∨ i=2 ∨ i=3 ∨ i=4 := by omega
    rcases hc with h0 | h1 | h2 | h3 | h4
    · subst i
      exact m0EvenEightQ4CutTape_head_true L q a b h ha
    · subst i
      exact m0EvenEightQ4CutTape_plus1_true L q a b h ha
    · subst i
      have hcell := m0EvenEightQ4CutTape_sourceRightCell
        L q a b h 1 ha (by omega)
      have hcoord : h+1+(1:Int) = h+2 := by omega
      simpa [hcoord,s1PhysicalRight,s0PhysicalRight,s0RightFacing,sideBit] using hcell
    · subst i
      have hcell := m0EvenEightQ4CutTape_sourceRightCell
        L q a b h 2 ha (by omega)
      have hcoord : h+1+(2:Int) = h+3 := by omega
      simpa [hcoord,s1PhysicalRight,s0PhysicalRight,s0RightFacing,sideBit] using hcell
    · subst i
      have hcell := m0EvenEightQ4CutTape_sourceRightCell
        L q a b h 3 ha (by omega)
      have hcoord : h+1+(3:Int) = h+4 := by omega
      simpa [hcoord,s1PhysicalRight,s0PhysicalRight,s0RightFacing,sideBit] using hcell
  · have hcell := m0EvenEightQ4CutTape_sourceRightCell
      L q a b h 4 ha (by omega)
    have hcoord : h+1+(4:Int) = h+5 := by omega
    simpa [hcoord,s1PhysicalRight,s0PhysicalRight,s0RightFacing,sideBit] using hcell
  · have hcell := m0EvenEightQ4CutTape_sourceRightCell
      L q a b h 5 ha (by omega)
    have hcoord : h+1+(5:Int) = h+6 := by omega
    simpa [hcoord,s1PhysicalRight,s0PhysicalRight,s0RightFacing,sideBit] using hcell
  · intro i hi
    have hcell := m0EvenEightQ4CutTape_sourceRightCell
      L q a b h (6+i) ha (by omega)
    have hcoord :
        h+7+(i:Int) = h+1+((6+i:Int)) := by push_cast; omega
    have hside : sideBit (s1PhysicalRight b) (6+i) = true := by
      simp only [s1PhysicalRight,s0PhysicalRight,s0RightFacing]
      rw [sideBit_append_right [false,true,true,true,false,false]
        (d1pow (b+1)) (6+i) (by simp)]
      have hidx : 6+i-6 = i := by omega
      rw [hidx]
      exact sideBit_d1pow_true (b+1) i (by omega)
    rw [← hcoord,hside] at hcell
    exact hcell
  · intro i hi
    have j : Nat := 9+3*b+i
    have hcell := m0EvenEightQ4CutTape_sourceRightCell
      L q a b h j ha (by dsimp [j]; omega)
    have hcoord :
        h+10+(3*b:Int)+(i:Int) = h+1+((j:Int)) := by
      dsimp [j]
      push_cast
      omega
    have hlen : (s1PhysicalRight b).length = 9+3*b := by
      simp [s1PhysicalRight,s0PhysicalRight,s0RightFacing,d1pow_length]
    have hfalse := sideBit_false_after_length_local
      (s1PhysicalRight b) j (by rw [hlen]; dsimp [j]; omega)
    rw [← hcoord,hfalse] at hcell
    exact hcell

/-- The full infinite blank tail required by the generic q4 suffix. -/
theorem m0EvenEight_q4_prefix_far_tail
    (L q a b : Nat) (h : Int)
    (hL : 4 ≤ L) (hqodd : q % 2 = 1)
    (hbound : 8*q < 2^L) (ha : 0 < a) :
    ∀ i : Nat, 9+3*b ≤ i →
      m0EvenEightQ4CutTape L q a b h (h+1+(i:Int)) = false := by
  intro i hi
  have hcell := m0EvenEightQ4CutTape_sourceRightCell
    L q a b h i ha (by omega)
  have hlen : (s1PhysicalRight b).length = 9+3*b := by
    simp [s1PhysicalRight,s0PhysicalRight,s0RightFacing,d1pow_length]
  have hfalse := sideBit_false_after_length_local
    (s1PhysicalRight b) i (by rw [hlen]; exact hi)
  rw [hfalse] at hcell
  exact hcell

private theorem m0EvenEight_v2_mul_odd
    (q : Nat) (hqodd : q % 2 = 1) :
    v2 (8*q) = 3 := by
  have hqv : v2 q = 0 := v2_of_odd q (by omega)
  have hdiv2 : (2*q)/2 = q := by omega
  have hdiv4 : (4*q)/2 = 2*q := by omega
  have hdiv8 : (8*q)/2 = 4*q := by omega
  have h2 : v2 (2*q) = 1+v2 q := by
    rw [v2_of_even (2*q) (by omega) (by omega), hdiv2]
  have h4 : v2 (4*q) = 1+v2 (2*q) := by
    rw [v2_of_even (4*q) (by omega) (by omega), hdiv4]
  have h8 : v2 (8*q) = 1+v2 (4*q) := by
    rw [v2_of_even (8*q) (by omega) (by omega), hdiv8]
  rw [h8,h4,h2,hqv]
  omega

private theorem m0EvenEight_resetPrefixCost
    (q a b : Nat) (hqodd : q % 2 = 1) :
    resetPrefixCost 0 (8*q) a b = (60+12*a)+(39+3*b) := by
  rw [resetPrefixCost,m0EvenEight_v2_mul_odd q hqodd]
  omega

private theorem m0EvenEight_drainPolynomial_lower_bound
    (b : Nat) :
    12*b+48 ≤ 6*4^b+42*2^b := by
  induction b with
  | zero =>
      norm_num
  | succ b ih =>
      simp only [Nat.pow_succ]
      have h4 : 0 < 4^b := Nat.pow_pos (a:=4) (n:=b) (by decide)
      have h2 : 0 < 2^b := Nat.pow_pos (a:=2) (n:=b) (by decide)
      omega

/-- Closed exact primitive-step cost for the generic m=0,n=8q row. -/
theorem m0EvenEight_proposedIncrementCost_closed
    (q a b : Nat) (hqodd : q % 2 = 1) :
    proposedIncrementCost 0 (8*q) a b =
      6*4^b + 42*2^b + 12*a - 9*b + 51 := by
  have hge := m0EvenEight_drainPolynomial_lower_bound b
  rw [proposedIncrementCost_decomp 0 (8*q) a b,
    m0EvenEight_resetPrefixCost q a b hqodd,
    drainCost_binary_closed b]
  omega

/-- Exact q4 prefix plus shared q4 suffix, before the S1 all-ones drain. -/
theorem m0EvenEight_q4_reset_prefix_source
    (L q a b : Nat) (h : Int)
    (hL : 4 ≤ L) (hqodd : q % 2 = 1)
    (hbound : 8*q < 2^L) (ha : 0 < a) :
    run tm2 (resetPrefixCost 0 (8*q) a b)
      (s1Config L (8*q) 0 a 0 b h) =
      some (s1Config L (8*q-1) 2 (a+b+1) (2^b-1) 0
        (h+5+(3*b:Int))) := by
  let Tq := m0EvenEightQ4CutTape L q a b h
  have hprefix0 := m0EvenEight_q4_prefix_run L q a b h
    hL hqodd hbound ha
  have hprefix :
      run tm2 (60+12*a) (s1Config L (8*q) 0 a 0 b h) =
        some ⟨4,h,Tq⟩ := by
    simpa [s1Config,s0Config,Tq] using hprefix0
  have hleft0 := m0EvenEight_q4_prefix_leftFacing
    L q a b h hL hqodd hbound ha
  have hleft :
      ∀ i : Nat, Tq (h-(i:Int)) =
        sideBit (m0EvenEightQ4LeftFacing L q a) i := by
    simpa [Tq] using hleft0
  have hshape0 := m0EvenEight_q4_prefix_rightShape
    L q a b h hL hqodd hbound ha
  have hshape : q4RightShape Tq h b := by
    simpa [Tq] using hshape0
  have htail0 := m0EvenEight_q4_prefix_far_tail
    L q a b h hL hqodd hbound ha
  have htail :
      ∀ i : Nat, 9+3*b ≤ i → Tq (h+1+(i:Int)) = false := by
    simpa [Tq] using htail0
  have happend := m0EvenEightQ4SuffixTargetLeft
    L q a b hL hqodd hbound ha
  have hsuffix := q4_suffix_run_to_s1Config
    Tq h b L (8*q-1) 2 (a+b+1) (2^b-1)
    (m0EvenEightQ4LeftFacing L q a) hshape htail hleft happend
  have hcost := m0EvenEight_resetPrefixCost q a b hqodd
  rw [hcost,run_add,hprefix]
  simp only [Option.bind_some]
  simpa [Tq] using hsuffix

/-- The complete counted m=0,n=8q source increment for every odd q. -/
theorem m0EvenEight_counted_increment_source
    (L q a b : Nat) (h : Int)
    (hL : 4 ≤ L) (hqodd : q % 2 = 1)
    (hbound : 8*q < 2^L) (ha : 0 < a) :
    run tm2 (proposedIncrementCost 0 (8*q) a b)
      (s1Config L (8*q) 0 a 0 b h) =
      some (s1Config L (8*q-1) 2 (a+b+1) 0 (2^b-1)
        (h+5+(3*b:Int))) := by
  have hprefix := m0EvenEight_q4_reset_prefix_source
    L q a b h hL hqodd hbound ha
  have hdrain : 2^b-1 < 2^(a+b+1) := by
    have h := resetDrainBound a b 0 ha
    simpa [resetDelta] using h
  have hrun := s1Config_reset_prefix_then_counted_drain
    L (8*q-1) 2 (a+b+1) b (h+5+(3*b:Int))
    (s1Config L (8*q) 0 a 0 b h)
    (resetPrefixCost 0 (8*q) a b) hprefix hdrain
  simpa [proposedIncrementCost_decomp] using hrun

#print axioms m0EvenEight_q4_prefix_leftFacing
#print axioms m0EvenEight_q4_prefix_rightShape
#print axioms m0EvenEight_q4_prefix_far_tail
#print axioms m0EvenEight_proposedIncrementCost_closed
#print axioms m0EvenEight_q4_reset_prefix_source
#print axioms m0EvenEight_counted_increment_source

end BB6Coverage.Agent48M0EvenEightGenericSource
