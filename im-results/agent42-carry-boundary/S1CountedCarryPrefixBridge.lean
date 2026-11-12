import CountedCarryPrefixGeneral
import S1Encoder
import Lean.Elab.Tactic.Omega

namespace BB6Coverage.Agent42CarryPrefixBridge

open BB6Coverage
open BB6Coverage.Agent8S1Encoder
open BB6Coverage.Agent48Champion

set_option maxHeartbeats 1000000

private theorem sideBit_append_before (xs ys : List Bool) (i : Nat)
    (hi : i < xs.length) :
    sideBit (xs ++ ys) i = sideBit xs i := by
  induction xs generalizing i with
  | nil =>
      simp at hi
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

private theorem sideBit_d1pow_true (r i : Nat) (hi : i < 3*r) :
    sideBit (d1pow r) i = true := by
  induction r generalizing i with
  | zero => omega
  | succ r ih =>
      by_cases hsmall : i < 3
      · have hcases : i=0 ∨ i=1 ∨ i=2 := by omega
        rcases hcases with h0 | h1 | h2
        · subst i
          simp [d1pow, d1, sideBit]
        · subst i
          simp [d1pow, d1, sideBit]
        · subst i
          simp [d1pow, d1, sideBit]
      · have hlarge : 3 ≤ i := by omega
        have hi' : i-3 < 3*r := by omega
        have heq : i = (i-3)+3 := by omega
        rw [heq]
        simpa [d1pow, d1, sideBit] using ih (i-3) hi'

/-- The source S1 left boundary has exactly the carry-input suffix
100 111^r immediately before the D head. -/
private theorem s1CarryInput_left
    (L n m len q r b : Nat) (h : Int) (hq : q < 2^len)
    (x : Int) (hlo : -(3*(r:Int))-2 ≤ x) (hhi : x ≤ 0) :
    (s1Config L n m (len+1+r) ((2*q+1)*2^r) b h).tape (h+x) =
      carryInputBit r x := by
  let rest : List Bool :=
    binDec len q ++ markerWord m ++ d0 ++ binDec L n ++ lh
  let i : Nat := Int.toNat (-x)
  have hix : (i:Int) = -x := by
    dsimp [i]
    omega
  have hcoord : h-(i:Int) = h+x := by omega
  have hcell := s1Config_left_carryCells L n m len q r b h i hq
  have hcell' :
      (s1Config L n m (len+1+r) ((2*q+1)*2^r) b h).tape (h+x) =
        sideBit (d1pow r ++ (d0 ++ rest)) i := by
    rw [hcoord] at hcell
    simpa [rest,List.append_assoc] using hcell
  have hibound : i ≤ 3*r+2 := by
    have hi : (i:Int) = -x := hix
    omega
  by_cases hsmall : i < 3*r
  · have happ := sideBit_append_before (d1pow r) (d0 ++ rest) i (by
      simpa [d1pow_length] using hsmall)
    rw [happ, sideBit_d1pow_true r i hsmall] at hcell'
    have hbit : carryInputBit r x = true := by
      have hxrange : -(3*(r:Int))+1 ≤ x ∧ x ≤ 0 := by
        have hi : (i:Int) = -x := hix
        omega
      simp [carryInputBit, hxrange]
    simpa [hbit] using hcell'
  · have hlarge : 3*r ≤ i := by omega
    have happ := sideBit_append_after (d1pow r) (d0 ++ rest) i (by
      simpa [d1pow_length] using hlarge)
    rw [happ] at hcell'
    have hcell'' :
        (s1Config L n m (len+1+r) ((2*q+1)*2^r) b h).tape (h+x) =
          sideBit (d0 ++ rest) (i-3*r) := by
      simpa [d1pow_length] using hcell'
    have hcases : i-3*r=0 ∨ i-3*r=1 ∨ i-3*r=2 := by omega
    rcases hcases with h0 | h1 | h2
    · have hx : x = -(3*(r:Int)) := by
        have hi : (i:Int) = -x := hix
        omega
      rw [h0,hx] at hcell''
      have hbit : carryInputBit r (-(3*(r:Int))) = false := by
        simp [carryInputBit] <;> omega
      simpa [d0,sideBit,hbit] using hcell''
    · have hx : x = -(3*(r:Int))-1 := by
        have hi : (i:Int) = -x := hix
        omega
      rw [h1,hx] at hcell''
      have hbit : carryInputBit r (-(3*(r:Int))-1) = false := by
        simp [carryInputBit] <;> omega
      simpa [d0,sideBit,hbit] using hcell''
    · have hx : x = -(3*(r:Int))-2 := by
        have hi : (i:Int) = -x := hix
        omega
      rw [h2,hx] at hcell''
      have hbit : carryInputBit r (-(3*(r:Int))-2) = true := by
        simp [carryInputBit]
      simpa [d0,sideBit,hbit] using hcell''

/-- The source S1 right boundary is 0 111 00; the unary counter
starts beyond the six-cell carry window and remains unrestricted. -/
private theorem s1CarryInput_right
    (L n m len q r b : Nat) (h : Int) (hq : q < 2^len)
    (x : Int) (hx0 : 0 < x) (hx6 : x ≤ 6) :
    (s1Config L n m (len+1+r) ((2*q+1)*2^r) b h).tape (h+x) =
      carryInputBit r x := by
  let i : Nat := Int.toNat (x-1)
  have hix : (i:Int) = x-1 := by
    dsimp [i]
    omega
  have hcoord : h+1+(i:Int) = h+x := by omega
  have hcell := s1Config_right_cell L n m (len+1+r)
    ((2*q+1)*2^r) b h i
  have hcell' :
      (s1Config L n m (len+1+r) ((2*q+1)*2^r) b h).tape (h+x) =
        sideBit (s1PhysicalRight b) i := by
    rw [hcoord] at hcell
    simpa using hcell
  have hibound : i ≤ 5 := by
    have hi : (i:Int) = x-1 := hix
    omega
  have hcases : i=0 ∨ i=1 ∨ i=2 ∨ i=3 ∨ i=4 ∨ i=5 := by omega
  have hvalue : sideBit (s1PhysicalRight b) i = carryInputBit r x := by
    rcases hcases with h0 | h1 | h2 | h3 | h4 | h5
    · have hx : x=1 := by omega
      rw [hx]
      have hneq : (1:Int) ≠ -(3*(r:Int))-2 := by omega
      have hbit : carryInputBit r 1 = false := by
        simp [carryInputBit,hneq]
      simpa [h0,s1PhysicalRight,s0PhysicalRight,s0RightFacing,sideBit,
        d1pow,hbit]
    · have hx : x=2 := by omega
      rw [hx]
      have hbit : carryInputBit r 2 = true := by simp [carryInputBit]
      simpa [h1,s1PhysicalRight,s0PhysicalRight,s0RightFacing,sideBit,
        d1pow,hbit]
    · have hx : x=3 := by omega
      rw [hx]
      have hbit : carryInputBit r 3 = true := by simp [carryInputBit]
      simpa [h2,s1PhysicalRight,s0PhysicalRight,s0RightFacing,sideBit,
        d1pow,hbit]
    · have hx : x=4 := by omega
      rw [hx]
      have hbit : carryInputBit r 4 = true := by simp [carryInputBit]
      simpa [h3,s1PhysicalRight,s0PhysicalRight,s0RightFacing,sideBit,
        d1pow,hbit]
    · have hx : x=5 := by omega
      rw [hx]
      have hneq : (5:Int) ≠ -(3*(r:Int))-2 := by omega
      have hbit : carryInputBit r 5 = false := by
        simp [carryInputBit,hneq]
      simpa [h4,s1PhysicalRight,s0PhysicalRight,s0RightFacing,sideBit,
        d1pow,hbit]
    · have hx : x=6 := by omega
      rw [hx]
      have hneq : (6:Int) ≠ -(3*(r:Int))-2 := by omega
      have hbit : carryInputBit r 6 = false := by
        simp [carryInputBit,hneq]
      simpa [h5,s1PhysicalRight,s0PhysicalRight,s0RightFacing,sideBit,
        d1pow,hbit]
  exact hcell'.trans hvalue

/-- Every valid even positive S1 counter admits the all-natural counted
carry prefix in the original TM63 run semantics. The result preserves
the first right-counter bit at the final E head and all further exterior
cells; it is a prefix theorem, not the complete Inc0 macro. -/
theorem s1Config_evenCounter_carryPrefix
    (L n m a z b : Nat) (h : Int)
    (hz : 0 < z) (hzlt : z < 2^a) (heven : z % 2 = 0) :
    ∃ q r len T',
      z = (2*q+1)*2^r ∧ a = len+1+r ∧ q < 2^len ∧ 0 < r ∧
      run tm2 (15+12*r) (s1Config L n m a z b h) =
        some ⟨(4 : Fin 6),h+7,T'⟩ ∧
      T' (h+1) = true ∧ T' (h+2) = true ∧
      T' (h+3) = true ∧ T' (h+4) = true ∧
      T' (h+5) = false ∧ T' (h+6) = true ∧
      (∀ x, h+6 < x → T' x = (s1Config L n m a z b h).tape x) := by
  obtain ⟨q,r,len,hfactor,ha,hq⟩ :=
    exists_odd_factor_bounded a z hz hzlt
  have hr : 0 < r := by
    by_cases hr0 : r=0
    · have hodd : z=2*q+1 := by
        calc
          z = (2*q+1)*2^r := hfactor
          _ = 2*q+1 := by simp [hr0]
      omega
    · omega
  let cfg := s1Config L n m a z b h
  have hcfg : cfg =
      s1Config L n m (len+1+r) ((2*q+1)*2^r) b h := by
    simp [cfg,ha,hfactor]
  let T : Int → Bool := fun x => cfg.tape (h+x)
  have hmatch : ∀ x, carryInputArea r x = true →
      T x = carryInputBit r x := by
    intro x hx
    have hbounds : -(3*(r:Int))-2 ≤ x ∧ x ≤ 6 := by
      simpa [carryInputArea] using hx
    by_cases hleft : x ≤ 0
    · have hv := s1CarryInput_left L n m len q r b h hq x hbounds.1 hleft
      rw [← hcfg] at hv
      simpa [T] using hv
    · have hright : 0 < x ∧ x ≤ 6 := by omega
      have hv := s1CarryInput_right L n m len q r b h hq x hright.1 hright.2
      rw [← hcfg] at hv
      simpa [T] using hv
  obtain ⟨Tout,hrun,ho1,ho2,ho3,ho4,ho5,ho6,hout⟩ :=
    carryPrefix_anyPositive r T hr hmatch
  have hstart : shiftConfig h ⟨(3 : Fin 6),0,T⟩ = cfg := by
    simp [shiftConfig,T,cfg,s1Config,s0Config,s0Tape,Int.add_sub_cancel_left]
  let Tfinal : Int → Bool := fun x => Tout (x-h)
  have hrunAbs : run tm2 (15+12*r) cfg =
      some ⟨(4 : Fin 6),h+7,Tfinal⟩ := by
    have hshift := shift_run h tm2 ⟨(3 : Fin 6),0,T⟩ (15+12*r)
    rw [hrun] at hshift
    simp only [Option.map] at hshift
    rw [hstart] at hshift
    have hshift' : run tm2 (15+12*r) cfg =
        some ⟨(4 : Fin 6),7+h,Tfinal⟩ := by
      simpa [shiftConfig,Tfinal] using hshift
    have hhead : (7:Int)+h = h+7 := by omega
    simpa [hhead] using hshift'
  refine ⟨q,r,len,Tfinal,hfactor,ha,hq,hr,hrunAbs,?_,?_,?_,?_,?_,?_,?_⟩
  · have hcoord : (h+1)-h=1 := by omega
    simpa [Tfinal,hcoord] using ho1
  · have hcoord : (h+2)-h=2 := by omega
    simpa [Tfinal,hcoord] using ho2
  · have hcoord : (h+3)-h=3 := by omega
    simpa [Tfinal,hcoord] using ho3
  · have hcoord : (h+4)-h=4 := by omega
    simpa [Tfinal,hcoord] using ho4
  · have hcoord : (h+5)-h=5 := by omega
    simpa [Tfinal,hcoord] using ho5
  · have hcoord : (h+6)-h=6 := by omega
    simpa [Tfinal,hcoord] using ho6
  · intro x hx
    have hy : 6 < x-h := by omega
    have hv := hout (x-h) hy
    have hT : T (x-h) = cfg.tape x := by
      dsimp [T]
      congr 1
      omega
    rw [hT] at hv
    simpa [Tfinal] using hv

#print axioms s1Config_evenCounter_carryPrefix

end BB6Coverage.Agent42CarryPrefixBridge
