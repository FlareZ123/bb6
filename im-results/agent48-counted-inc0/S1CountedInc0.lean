import S1CarryInc0
import S1OddCanonicalOutput
import Lean.Elab.Tactic.Omega

namespace BB6Coverage.Agent48CountedInc0

open BB6Coverage
open BB6Coverage.Agent8S1Encoder
open BB6Coverage.Agent48Champion
open BB6Coverage.Agent24ChampionTime
open BB6Coverage.Agent42CarryPrefixBridge
open BB6Coverage.Agent2OddCanonical

set_option maxHeartbeats 3000000

/-- The valuation-zero S1 input window is the physical odd-counter prefix:
the two cells immediately left of the head are blank, and the right guard
is 0 111 00. The encoded tail is arbitrary. -/
theorem s1Config_oddCounter_local
    (L n m len q b : Nat) (h : Int) (hq : q < 2^len)
    (x : Int) (hx : prefArea x = true) :
    (s1Config L n m (len+1) (2*q+1) b h).tape (h+x) =
      (embed prefBase).tape x := by
  have hbounds : -1 ≤ x ∧ x ≤ 6 := by
    simpa [prefArea] using hx
  have hcases : x = (-1:Int) ∨ x = 0 ∨ x = 1 ∨ x = 2 ∨
      x = 3 ∨ x = 4 ∨ x = 5 ∨ x = 6 := by omega
  rcases hcases with hneg | h0 | h1 | h2 | h3 | h4 | h5 | h6
  · subst x
    have hcell0 := s1Config_left_carryCells L n m len q 0 b h 1 hq
    have hcell :
        (s1Config L n m (len+1) (2*q+1) b h).tape (h-(1:Nat)) =
          sideBit (d1pow 0 ++ d0 ++ binDec len q ++ markerWord m ++
            d0 ++ binDec L n ++ lh) 1 := by
      simpa using hcell0
    have hcoord : h-(1:Nat) = h+(-1:Int) := by omega
    rw [hcoord] at hcell
    have hbit :
        sideBit (d1pow 0 ++ d0 ++ binDec len q ++
          markerWord m ++ d0 ++ binDec L n ++ lh) 1 = false := by
      simp [d1pow,d0,sideBit]
    rw [hbit] at hcell
    simpa [embed,prefBase] using hcell
  · subst x
    have hcell0 := s1Config_left_carryCells L n m len q 0 b h 0 hq
    have hcell :
        (s1Config L n m (len+1) (2*q+1) b h).tape (h-(0:Nat)) =
          sideBit (d1pow 0 ++ d0 ++ binDec len q ++ markerWord m ++
            d0 ++ binDec L n ++ lh) 0 := by
      simpa using hcell0
    have hcoord : h-(0:Nat) = h+0 := by omega
    rw [hcoord] at hcell
    have hbit :
        sideBit (d1pow 0 ++ d0 ++ binDec len q ++
          markerWord m ++ d0 ++ binDec L n ++ lh) 0 = false := by
      simp [d1pow,d0,sideBit]
    rw [hbit] at hcell
    simpa [embed,prefBase] using hcell
  · subst x
    have hcell := s1Config_right_cell L n m (len+1) (2*q+1) b h 0
    have hcoord : h+1+(0:Nat) = h+1 := by omega
    rw [hcoord] at hcell
    simpa [s1PhysicalRight,s0PhysicalRight,s0RightFacing,sideBit,
      embed,prefBase] using hcell
  · subst x
    have hcell := s1Config_right_cell L n m (len+1) (2*q+1) b h 1
    have hcoord : h+1+(1:Nat) = h+2 := by omega
    rw [hcoord] at hcell
    simpa [s1PhysicalRight,s0PhysicalRight,s0RightFacing,sideBit,
      embed,prefBase] using hcell
  · subst x
    have hcell := s1Config_right_cell L n m (len+1) (2*q+1) b h 2
    have hcoord : h+1+(2:Nat) = h+3 := by omega
    rw [hcoord] at hcell
    simpa [s1PhysicalRight,s0PhysicalRight,s0RightFacing,sideBit,
      embed,prefBase] using hcell
  · subst x
    have hcell := s1Config_right_cell L n m (len+1) (2*q+1) b h 3
    have hcoord : h+1+(3:Nat) = h+4 := by omega
    rw [hcoord] at hcell
    simpa [s1PhysicalRight,s0PhysicalRight,s0RightFacing,sideBit,
      embed,prefBase] using hcell
  · subst x
    have hcell := s1Config_right_cell L n m (len+1) (2*q+1) b h 4
    have hcoord : h+1+(4:Nat) = h+5 := by omega
    rw [hcoord] at hcell
    simpa [s1PhysicalRight,s0PhysicalRight,s0RightFacing,sideBit,
      embed,prefBase] using hcell
  · subst x
    have hcell := s1Config_right_cell L n m (len+1) (2*q+1) b h 5
    have hcoord : h+1+(5:Nat) = h+6 := by omega
    rw [hcoord] at hcell
    simpa [s1PhysicalRight,s0PhysicalRight,s0RightFacing,sideBit,
      embed,prefBase] using hcell

/-- Exact valuation-zero source S1 decrement. The original TM63 run
returns to D at the same head and its complete tape is the canonical
S1 encoding with binary counter 2q and unary counter b+1. -/
theorem s1Config_oddCounter_countedReturn_canonical
    (L n m len q b : Nat) (h : Int) (hq : q < 2^len) :
    run tm2 (48+12*b)
      (s1Config L n m (len+1) (2*q+1) b h) =
      some (s1Config L n m (len+1) (2*q) (b+1) h) := by
  let P : Int → Bool :=
    fun x => (s1Config L n m (len+1) (2*q+1) b h).tape (h+x)
  have hlocal : ∀ x, prefArea x = true →
      P x = (embed prefBase).tape x := by
    intro x hx
    exact s1Config_oddCounter_local L n m len q b h hq x hx
  have hframe : oddCounterInput P = (⟨(3 : Fin 6),0,P⟩ : Config) := by
    unfold oddCounterInput
    change (⟨(3 : Fin 6),0,
      fun x => if prefArea x then (embed prefBase).tape x else P x⟩ : Config) =
      ⟨(3 : Fin 6),0,P⟩
    congr 1
    funext x
    by_cases hx : prefArea x = true
    · have hv := hlocal x hx
      simp [hx,hv]
    · simp [hx]
  have hstart : shiftConfig h (oddCounterInput P) =
      s1Config L n m (len+1) (2*q+1) b h := by
    rw [hframe]
    change (⟨(3 : Fin 6),0+h,fun x => P (x-h)⟩ : Config) =
      ⟨(3 : Fin 6),h,
        (s1Config L n m (len+1) (2*q+1) b h).tape⟩
    have hhead : (0:Int)+h = h := by omega
    rw [hhead]
    congr 1
    funext x
    dsimp [P]
    congr 1
    omega
  have hone : ∀ i : Nat, i < 3*(b+1) → P (7+(i:Int)) = true := by
    intro i hi
    have hy : (7:Int)+(i:Int) ≥ 7 := by omega
    have hv := s1Config_right_bit_formula
      L n m (len+1) (2*q+1) b h (7+(i:Int)) hy
    have hlt : (7:Int)+(i:Int) < rightStop b := by
      unfold rightStop
      omega
    simpa [P,hlt] using hv
  have hzero0 : P (rightStop b) = false := by
    have hy : 7 ≤ rightStop b := by unfold rightStop; omega
    have hv := s1Config_right_bit_formula
      L n m (len+1) (2*q+1) b h (rightStop b) hy
    have hfalse : ¬ rightStop b < rightStop b := by omega
    simpa [P,hfalse] using hv
  have hzero1 : P (rightStop b+1) = false := by
    have hy : 7 ≤ rightStop b+1 := by unfold rightStop; omega
    have hv := s1Config_right_bit_formula
      L n m (len+1) (2*q+1) b h (rightStop b+1) hy
    have hfalse : ¬ rightStop b+1 < rightStop b := by
      unfold rightStop
      omega
    simpa [P,hfalse] using hv
  have hzero2 : P (rightStop b+2) = false := by
    have hy : 7 ≤ rightStop b+2 := by unfold rightStop; omega
    have hv := s1Config_right_bit_formula
      L n m (len+1) (2*q+1) b h (rightStop b+2) hy
    have hfalse : ¬ rightStop b+2 < rightStop b := by
      unfold rightStop
      omega
    simpa [P,hfalse] using hv
  have hrun := counted_odd_counter P b hone hzero0 hzero1 hzero2
  have hshift := shift_run h tm2 (oddCounterInput P) (48+12*b)
  rw [hrun] at hshift
  simp only [Option.map] at hshift
  rw [hstart] at hshift
  let Tpost : Int → Bool :=
    (oddCounterOutput b P).tape ∘ fun x => x-h
  have hrunAbs : run tm2 (48+12*b)
      (s1Config L n m (len+1) (2*q+1) b h) =
      some ⟨(3 : Fin 6),h,Tpost⟩ := by
    simpa [shiftConfig,Tpost,oddCounterOutput,frame,embed,tailFinal] using hshift
  have hcanonical : Tpost =
      (s1Config L n m (len+1) (2*q) (b+1) h).tape := by
    funext x
    dsimp [Tpost]
    have hv := oddCounterOutput_s1Successor L n m len q b h hq (x-h)
    have hcoord : h+(x-h) = x := by omega
    simpa [P,hcoord] using hv
  have hcfg : (⟨(3 : Fin 6),h,Tpost⟩ : Config) =
      s1Config L n m (len+1) (2*q) (b+1) h := by
    simp [s1Config,hcanonical]
  calc
    run tm2 (48+12*b)
        (s1Config L n m (len+1) (2*q+1) b h) =
      some ⟨(3 : Fin 6),h,Tpost⟩ := hrunAbs
    _ = some (s1Config L n m (len+1) (2*q) (b+1) h) := by
      rw [hcfg]

/-- Every positive odd bounded S1 counter has the canonical counted
decrement (z,b) ↦ (z-1,b+1), with the valuation-zero cost 48+12b. -/
theorem s1Config_counted_decrement_odd
    (L n m a z b : Nat) (h : Int)
    (hz : 0 < z) (hzlt : z < 2^a) (hodd : z % 2 = 1) :
    ∃ q len, z = 2*q+1 ∧ a = len+1 ∧ q < 2^len ∧
      run tm2 (48+12*b) (s1Config L n m a z b h) =
        some (s1Config L n m a (z-1) (b+1) h) := by
  obtain ⟨q,r,len,hfactor,ha,hq⟩ :=
    exists_odd_factor_bounded a z hz hzlt
  have hr : r = 0 := by
    cases r with
    | zero => rfl
    | succ r =>
        have hdivPow : 2 ∣ 2^(Nat.succ r) := by
          simp [Nat.pow_succ,Nat.mul_comm]
        have hdiv : 2 ∣ z := by
          rw [hfactor]
          exact dvd_mul_of_dvd_right hdivPow (2*q+1)
        have heven : z % 2 = 0 := Nat.mod_eq_zero_of_dvd hdiv
        omega
  have hfactor' : z = 2*q+1 := by simpa [hr] using hfactor
  have ha' : a = len+1 := by simpa [hr] using ha
  have hsub : z-1 = 2*q := by omega
  have hrun := s1Config_oddCounter_countedReturn_canonical
    L n m len q b h hq
  have hinput : s1Config L n m a z b h =
      s1Config L n m (len+1) (2*q+1) b h := by
    rw [ha',hfactor']
  have houtput : s1Config L n m a (z-1) (b+1) h =
      s1Config L n m (len+1) (2*q) (b+1) h := by
    rw [ha',hsub]
  refine ⟨q,len,hfactor',ha',hq,?_⟩
  simpa [hinput,houtput] using hrun

/-- Parity-complete source S1 decrement. For every positive bounded
counter z, the original TM63 performs the canonical transition
S1(z,b) ↦ S1(z-1,b+1) in exactly 48+12*v₂(z)+12b steps, where
z=(2q+1)2^r. The odd case is r=0; the even case composes the proved
positive-valuation source prefix and canonical suffix. -/
theorem s1Config_counted_decrement
    (L n m a z b : Nat) (h : Int)
    (hz : 0 < z) (hzlt : z < 2^a) :
    ∃ q r len, z = (2*q+1)*2^r ∧ a = len+1+r ∧ q < 2^len ∧
      run tm2 (48+12*r+12*b) (s1Config L n m a z b h) =
        some (s1Config L n m a (z-1) (b+1) h) := by
  obtain ⟨q,r,len,hfactor,ha,hq⟩ :=
    exists_odd_factor_bounded a z hz hzlt
  by_cases heven : z % 2 = 0
  · have hrpos : 0 < r := by
      by_contra hnot
      have hr0 : r = 0 := by omega
      have hodd : z % 2 = 1 := by
        rw [hfactor]
        simp [hr0]
      omega
    have hdec := s1Config_counted_decrement_allPositive
      L n m len q r b h hq hrpos
    have hinput : s1Config L n m a z b h =
        s1Config L n m (len+1+r) ((2*q+1)*2^r) b h := by
      rw [ha,hfactor]
    have houtput : s1Config L n m a (z-1) (b+1) h =
        s1Config L n m (len+1+r) (((2*q+1)*2^r)-1) (b+1) h := by
      rw [ha,hfactor]
    refine ⟨q,r,len,hfactor,ha,hq,?_⟩
    simpa [hinput,houtput] using hdec
  · have hodd : z % 2 = 1 := by omega
    have hr0 : r = 0 := by
      cases r with
      | zero => rfl
      | succ r =>
          have hdivPow : 2 ∣ 2^(Nat.succ r) := by
            simp [Nat.pow_succ,Nat.mul_comm]
          have hdiv : 2 ∣ z := by
            rw [hfactor]
            exact dvd_mul_of_dvd_right hdivPow (2*q+1)
          have heven' : z % 2 = 0 := Nat.mod_eq_zero_of_dvd hdiv
          omega
    have hfactor' : z = 2*q+1 := by simpa [hr0] using hfactor
    have ha' : a = len+1 := by simpa [hr0] using ha
    have hsub : z-1 = 2*q := by omega
    have hrun := s1Config_oddCounter_countedReturn_canonical
      L n m len q b h hq
    have hinput : s1Config L n m a z b h =
        s1Config L n m (len+1) (2*q+1) b h := by
      rw [ha',hfactor']
    have houtput : s1Config L n m a (z-1) (b+1) h =
        s1Config L n m (len+1) (2*q) (b+1) h := by
      rw [ha',hsub]
    refine ⟨q,r,len,hfactor,ha,hq,?_⟩
    simpa [hr0,hinput,houtput] using hrun

#print axioms s1Config_oddCounter_countedReturn_canonical
#print axioms s1Config_counted_decrement_odd
#print axioms s1Config_counted_decrement

end BB6Coverage.Agent48CountedInc0
