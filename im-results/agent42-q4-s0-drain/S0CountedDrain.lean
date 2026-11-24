import CountedSuffixOutput
import CountedReset
import CountedCarryPrefixHRun
import S1Encoder
import S1CarryOutputBridge
import Lean.Elab.Tactic.Omega

/-!
# Arbitrary-left-context S0 counted decrement and drain

This module generalizes the source-level S1 counted decrement to an
arbitrary S0 left context.  The local carry prefix is supplied by
carryPrefix_anyNonnegative_hRun; the existing S0 suffix composer closes
the remaining right-counter sweep.  The left-output identity is just
the exact BinDec adjacent-counter rewrite and leaves the arbitrary tail
unchanged.

This is an intermediate source theorem.  It is not an original-source
compile claim until the full dependency closure and axiom reports pass.
-/

namespace BB6Coverage.Agent42Q4S0Drain

open BB6Coverage
open BB6Coverage.Agent8S1Encoder
open BB6Coverage.Agent8CountedReset
open BB6Coverage.Agent48Champion
open BB6Coverage.Agent24ChampionTime
open BB6Coverage.Agent3CarryLeftOutput

set_option maxHeartbeats 4000000

private theorem config_ext_by_fields (c d : Config)
    (hstate : c.state = d.state) (hhead : c.head = d.head)
    (htape : c.tape = d.tape) : c = d := by
  cases c with
  | mk cs ch ct =>
    cases d with
    | mk ds dh dt =>
      cases hstate
      cases hhead
      cases htape
      rfl

/-- The local left input window is d1^r ++ d0, with the arbitrary S0
left context beginning only after the complete counter word. -/
private theorem s0SideBit_carryPrefixInput
    (r : Nat) (rest : List Bool) (i : Nat) (hi : i ≤ 3*r+2) :
    sideBit (d1pow r ++ d0 ++ rest) i =
      decide (i < 3*r ∨ i = 3*r+2) := by
  by_cases hlt : i < 3*r
  · have hones := sideBit_d1pow_true r i hlt
    simp only [List.append_assoc]
    rw [sideBit_append]
    simp [d1pow_length,hlt,hones]
  · have hc : i=3*r ∨ i=3*r+1 ∨ i=3*r+2 := by omega
    rcases hc with h0 | h1 | h2
    · subst i
      simp [sideBit_append,d1pow_length,d0,sideBit] <;> omega
    · subst i
      simp [sideBit_append,d1pow_length,d0,sideBit] <;> omega
    · subst i
      simp [sideBit_append,d1pow_length,d0,sideBit] <;> omega

/-- Every arbitrary-left-context S0 source configuration has the exact
local input window required by the uniform counted carry prefix. -/
theorem s0Config_carryInput_match
    (l : List Bool) (len q r b : Nat) (h : Int)
    (hq : q < 2^len) :
    ∀ x, carryInputArea r x = true →
      (s0Config l (len+1+r) ((2*q+1)*2^r) b h).tape (h+x) =
        carryInputBit r x := by
  intro x harea
  by_cases hx0 : x ≤ 0
  · let i : Nat := Int.toNat (-x)
    have hxEq : x = -(i:Int) := by
      dsimp [i]
      rw [Int.toNat_of_nonneg (by omega : 0 ≤ -x)]
      omega
    rw [hxEq] at harea ⊢
    have hbound : i ≤ 3*r+2 := by
      simp [carryInputArea] at harea
      omega
    have hsource :
        (s0Config l (len+1+r) ((2*q+1)*2^r) b h).tape
            (h-(i:Int)) =
          sideBit (d1pow r ++ d0 ++ binDec len q ++ l) i := by
      rw [s0Config_left_cell]
      simp only [s0LeftFacing]
      rw [binDec_carryPrefix len q r hq]
    have hside := s0SideBit_carryPrefixInput r
      (binDec len q ++ l) i hbound
    let P : Prop :=
      (-(i:Int) = -(3*(r:Int))-2 ∨
        (-(3*(r:Int))+1 ≤ -(i:Int) ∧ -(i:Int) ≤ 0) ∨
        -(i:Int)=2 ∨ -(i:Int)=3 ∨ -(i:Int)=4)
    have hprop : P ↔ (i < 3*r ∨ i = 3*r+2) := by
      dsimp [P]
      omega
    have hbit : carryInputBit r (-(i:Int)) =
        decide (i < 3*r ∨ i = 3*r+2) := by
      change decide P = decide (i < 3*r ∨ i = 3*r+2)
      by_cases hp : P
      · have hq : i < 3*r ∨ i = 3*r+2 := hprop.mp hp
        simp [hp,hq]
      · have hq : ¬ (i < 3*r ∨ i = 3*r+2) := by
          intro hq
          exact hp (hprop.mpr hq)
        simp [hp,hq]
    have hcoord : h + (-(i:Int)) = h-(i:Int) := by omega
    rw [hcoord,hsource]
    simpa only [List.append_assoc,hbit] using hside
  · let i : Nat := Int.toNat (x-1)
    have hxEq : x = 1+(i:Int) := by
      dsimp [i]
      rw [Int.toNat_of_nonneg (by omega : 0 ≤ x-1)]
      omega
    rw [hxEq] at harea
    have hbound : i ≤ 5 := by
      simp [carryInputArea] at harea
      omega
    have hsource :
        (s0Config l (len+1+r) ((2*q+1)*2^r) b h).tape
            (h+1+(i:Int)) = sideBit (s0RightFacing b) i :=
      s0Config_right_cell l (len+1+r) ((2*q+1)*2^r) b h i
    have hsideAll (j : Nat) (hj : j ≤ 5) :
        sideBit ([false,true,true,true,false,false] ++ d1pow (b+1)) j =
          carryInputBit r (1+(j:Int)) := by
      have hc : j=0 ∨ j=1 ∨ j=2 ∨ j=3 ∨ j=4 ∨ j=5 := by omega
      rcases hc with h0 | h1 | h2 | h3 | h4 | h5
      all_goals subst j <;> simp [sideBit,carryInputBit] <;> omega
    have hside := hsideAll i hbound
    rw [hxEq,show h+(1+(i:Int))=h+1+(i:Int) by omega,hsource]
    simpa [s0RightFacing] using hside

/-- The arbitrary-left-context S0 right suffix supplies the complete
right unary run required by the counted even suffix. -/
theorem s0Config_carryRightOnes
    (l : List Bool) (a z b : Nat) (h : Int) :
    ∀ i : Nat, i < 3*(b+1) →
      (s0Config l a z b h).tape (h+7+(i:Int)) = true := by
  intro i hi
  have hcoord : h+7+(i:Int) = h+1+((6+i:Nat):Int) := by omega
  rw [hcoord,s0Config_right_cell]
  have hside :
      sideBit ([false,true,true,true,false,false] ++ d1pow (b+1))
        (6+i) = true := by
    rw [sideBit_append]
    have hlen : ([false,true,true,true,false,false] : List Bool).length = 6 := by rfl
    have hnot : ¬ 6+i < 6 := by omega
    have hidx : 6+i-6 = i := by omega
    simp [hlen,hnot,hidx]
    exact sideBit_d1pow_true (b+1) i hi
  simpa [s0RightFacing] using hside

/-- The exact source left output for an arbitrary S0 tail.  The carry
prefix changes d1^r ++ d0 into d0^r ++ d1 and leaves the entire arbitrary
left context l unchanged. -/
theorem s0Config_decrement_leftOutput
    (l : List Bool) (len q r b : Nat) (h : Int)
    (hq : q < 2^len) :
    ∀ x : Int, x ≤ 0 →
      carryLeftOutputBit r
        (fun y =>
          (s0Config l (len+1+r) ((2*q+1)*2^r) b h).tape (h+y)) x =
      (s0Config l (len+1+r) (((2*q+1)*2^r)-1) (b+1) h).tape (h+x) := by
  intro x hx
  let i : Nat := Int.toNat (-x)
  have hxEq : x = -(i:Int) := by
    dsimp [i]
    rw [Int.toNat_of_nonneg (by omega : 0 ≤ -x)]
    omega
  rw [hxEq]
  have hin :
      (s0Config l (len+1+r) ((2*q+1)*2^r) b h).tape
          (h-(i:Int)) =
        sideBit (d1pow r ++ d0 ++ binDec len q ++ l) i := by
    rw [s0Config_left_cell]
    simp only [s0LeftFacing]
    rw [binDec_carryPrefix len q r hq]
  have hout :
      (s0Config l (len+1+r) (((2*q+1)*2^r)-1) (b+1) h).tape
          (h-(i:Int)) =
        sideBit (d0pow r ++ d1 ++ binDec len q ++ l) i := by
    rw [s0Config_left_cell]
    simp only [s0LeftFacing]
    rw [binDec_sub_one_carryPrefix len q r hq]
  have hcoord : h + (-(i:Int)) = h-(i:Int) := by omega
  by_cases hfar : 3*r+3 ≤ i
  · have hinTail :
        sideBit (d1pow r ++ d0 ++ binDec len q ++ l) i =
        sideBit (binDec len q ++ l) (i-(3*r+3)) := by
      simp only [List.append_assoc]
      rw [sideBit_append]
      simp only [d1pow_length]
      have hnot1 : ¬ i < 3*r := by omega
      simp [hnot1]
      rw [sideBit_append]
      have hlen0 : d0.length = 3 := by rfl
      simp only [hlen0]
      have hnot2 : ¬ i-3*r < 3 := by omega
      simp [hnot2] <;> congr 1 <;> omega
    have houtTail :
        sideBit (d0pow r ++ d1 ++ binDec len q ++ l) i =
        sideBit (binDec len q ++ l) (i-(3*r+3)) := by
      simp only [List.append_assoc]
      rw [sideBit_append]
      simp only [d0pow_length]
      have hnot1 : ¬ i < 3*r := by omega
      simp [hnot1]
      rw [sideBit_append]
      have hlen1 : d1.length = 3 := by rfl
      simp only [hlen1]
      have hnot2 : ¬ i-3*r < 3 := by omega
      simp [hnot2] <;> congr 1 <;> omega
    have hsame :
        (s0Config l (len+1+r) ((2*q+1)*2^r) b h).tape
            (h-(i:Int)) =
        (s0Config l (len+1+r) (((2*q+1)*2^r)-1) (b+1) h).tape
            (h-(i:Int)) := by
      calc
        _ = sideBit (d1pow r ++ d0 ++ binDec len q ++ l) i := hin
        _ = sideBit (binDec len q ++ l) (i-(3*r+3)) := hinTail
        _ = sideBit (d0pow r ++ d1 ++ binDec len q ++ l) i := houtTail.symm
        _ = _ := hout.symm
    have hbit :
        carryLeftOutputBit r
          (fun y =>
            (s0Config l (len+1+r) ((2*q+1)*2^r) b h).tape (h+y))
          (-(i:Int)) =
        (s0Config l (len+1+r) ((2*q+1)*2^r) b h).tape
          (h-(i:Int)) := by
      have hlt : (-(i:Int)) < -3*(r:Int)-2 := by omega
      simp [carryLeftOutputBit,hlt] <;> congr 1 <;> omega
    rw [hbit]
    simpa [hcoord] using hsame
  · have hnear : i < 3*r+3 := by omega
    by_cases hmiddle : 3*r ≤ i
    · have hside :
        sideBit (d0pow r ++ d1 ++ binDec len q ++ l) i = true := by
        simp only [List.append_assoc]
        rw [sideBit_append]
        simp only [d0pow_length]
        have hnot : ¬ i < 3*r := by omega
        simp [hnot]
        rw [sideBit_append]
        have hidx : i-3*r < 3 := by omega
        have hlenD1 : d1.length = 3 := by rfl
        have hd1 : sideBit d1 (i-3*r) = true := by
          simpa [d1pow] using sideBit_d1pow_true 1 (i-3*r) (by omega)
        simp [hlenD1,hidx,hd1]
      have hbit :
          carryLeftOutputBit r
            (fun y =>
              (s0Config l (len+1+r) ((2*q+1)*2^r) b h).tape (h+y))
            (-(i:Int)) = true := by
        have hnotfar : ¬ (-(i:Int) < -3*(r:Int)-2) := by omega
        have hle : (-(i:Int)) ≤ -3*(r:Int) := by omega
        simp [carryLeftOutputBit,hnotfar,hle]
      rw [hbit]
      rw [hcoord]
      rw [hout,hside]
    · have hsmall : i < 3*r := by omega
      have hside :
          sideBit (d0pow r ++ d1 ++ binDec len q ++ l) i =
            decide (i%3=2) := by
        simp only [List.append_assoc]
        rw [sideBit_append]
        simp only [d0pow_length]
        simp [hsmall,sideBit_d0pow_formula]
      have hbit :
          carryLeftOutputBit r
            (fun y =>
              (s0Config l (len+1+r) ((2*q+1)*2^r) b h).tape (h+y))
            (-(i:Int)) = decide (i%3=2) := by
        have hnotfar : ¬ (-(i:Int) < -3*(r:Int)-2) := by omega
        have hgt : ¬ (-(i:Int)) ≤ -3*(r:Int) := by omega
        have hmod : (-(i:Int)) % 3 = 1 ↔ i%3=2 := by omega
        simp [carryLeftOutputBit,hnotfar,hgt,hmod]
      rw [hbit]
      rw [hcoord]
      rw [hout,hside]

/-- Compose a relative-head carry-prefix witness with the exact arbitrary-l
S0 suffix. -/
theorem s0Config_counted_decrement_from_relative_prefix
    (l : List Bool) (len q r b : Nat) (h : Int)
    (hq : q < 2^len)
    (hprefix :
      ∃ T' : Int → Bool,
        run tm2 (15+12*r)
          ⟨3,0,fun x =>
            (s0Config l (len+1+r) ((2*q+1)*2^r) b h).tape (h+x)⟩ =
          some ⟨4,7,T'⟩ ∧
        T' 1 = true ∧ T' 2 = true ∧ T' 3 = true ∧
        T' 4 = true ∧ T' 5 = false ∧ T' 6 = true ∧
        (∀ x, 6 < x →
          T' x =
            (s0Config l (len+1+r) ((2*q+1)*2^r) b h).tape (h+x)) ∧
        (∀ x, x ≤ 0 →
          T' x = carryLeftOutputBit r
            (fun y =>
              (s0Config l (len+1+r) ((2*q+1)*2^r) b h).tape (h+y)) x)) :
    run tm2 (48+12*r+12*b)
      (s0Config l (len+1+r) ((2*q+1)*2^r) b h) =
      some (s0Config l (len+1+r) (((2*q+1)*2^r)-1) (b+1) h) := by
  let c0 := s0Config l (len+1+r) ((2*q+1)*2^r) b h
  let T : Int → Bool := fun x => c0.tape (h+x)
  rcases hprefix with
    ⟨T',hprun,h1,h2,h3,h4,h5,h6,hpreserve,hleft⟩
  let Tpre : Int → Bool := fun x => T' (x-h)
  have hstart : shiftConfig h ⟨3,0,T⟩ = c0 := by
    apply config_ext_by_fields
    · simp [shiftConfig,c0,s0Config]
    · simp [shiftConfig,c0,s0Config]
    · funext x
      change T (x-h) = c0.tape x
      dsimp [T]
      rw [show h+(x-h)=x by omega]
  have hshift := shift_run h tm2 ⟨3,0,T⟩ (15+12*r)
  rw [hprun] at hshift
  simp only [Option.map] at hshift
  rw [hstart] at hshift
  have hhead : (7:Int)+h = h+7 := by omega
  have hprefix0 : run tm2 (15+12*r) c0 =
      some ⟨4,h+7,Tpre⟩ := by
    simpa [shiftConfig,Tpre,hhead] using hshift
  have hcancel (x : Int) : h+x-h=x := by omega
  let P : Int → Bool := fun x => Tpre (h+x)
  have hP1 : P 1 = true := by simpa [P,Tpre,hcancel] using h1
  have hP2 : P 2 = true := by simpa [P,Tpre,hcancel] using h2
  have hP3 : P 3 = true := by simpa [P,Tpre,hcancel] using h3
  have hP4 : P 4 = true := by simpa [P,Tpre,hcancel] using h4
  have hP5 : P 5 = false := by simpa [P,Tpre,hcancel] using h5
  have hP6 : P 6 = true := by simpa [P,Tpre,hcancel] using h6
  have hpreserveP : ∀ x, 6 < x →
      P x = c0.tape (h+x) := by
    intro x hx
    simpa [P,Tpre,c0,hcancel] using hpreserve x hx
  have honeP : ∀ i : Nat, i < 3*(b+1) → P (7+(i:Int)) = true := by
    intro i hi
    rw [hpreserveP (7+(i:Int)) (by omega)]
    simpa [Int.add_assoc] using s0Config_carryRightOnes l (len+1+r) ((2*q+1)*2^r) b h i hi
  have hleftP : ∀ x, x ≤ 0 →
      P x =
        (s0Config l (len+1+r) (((2*q+1)*2^r)-1) (b+1) h).tape (h+x) := by
    intro x hx
    calc
      P x = T' x := by simp [P,Tpre,hcancel]
      _ = carryLeftOutputBit r
          (fun y => c0.tape (h+y)) x := by simpa [c0] using hleft x hx
      _ = (s0Config l (len+1+r) (((2*q+1)*2^r)-1) (b+1) h).tape (h+x) := by
        simpa [c0] using
          s0Config_decrement_leftOutput l len q r b h hq x hx
  apply BB6Coverage.Agent24ChampionTime.s0Config_counted_decrement_of_prefix
    l (len+1+r) ((2*q+1)*2^r) (((2*q+1)*2^r)-1) b r h Tpre
    hprefix0 hP1 hP2 hP3 hP4 hP5 hP6 _ hpreserveP hleftP
  intro i hi
  simpa [P,Int.add_assoc] using honeP i hi

/-- Uniform source-level S0 decrement for every 2-adic valuation r,
including r=0 and every arbitrary left context l. -/
theorem s0Config_counted_decrement_anyValuation_hRun
    (l : List Bool) (len q r b : Nat) (h : Int)
    (hq : q < 2^len) :
    run tm2 (48+12*r+12*b)
      (s0Config l (len+1+r) ((2*q+1)*2^r) b h) =
      some (s0Config l (len+1+r) (((2*q+1)*2^r)-1) (b+1) h) := by
  let c0 := s0Config l (len+1+r) ((2*q+1)*2^r) b h
  let T : Int → Bool := fun x => c0.tape (h+x)
  have hmatch : ∀ x, carryInputArea r x = true →
      T x = carryInputBit r x := by
    intro x hx
    simpa [T,c0] using s0Config_carryInput_match l len q r b h hq x hx
  obtain ⟨T',hrun,h1,h2,h3,h4,h5,h6,hpreserve,hleft⟩ :=
    BB6Coverage.Agent48Champion.carryPrefix_anyNonnegative_hRun r T hmatch
  have hprefix :
      ∃ T' : Int → Bool,
        run tm2 (15+12*r)
          ⟨3,0,fun x =>
            (s0Config l (len+1+r) ((2*q+1)*2^r) b h).tape (h+x)⟩ =
          some ⟨4,7,T'⟩ ∧
        T' 1 = true ∧ T' 2 = true ∧ T' 3 = true ∧
        T' 4 = true ∧ T' 5 = false ∧ T' 6 = true ∧
        (∀ x, 6 < x →
          T' x =
            (s0Config l (len+1+r) ((2*q+1)*2^r) b h).tape (h+x)) ∧
        (∀ x, x ≤ 0 →
          T' x = carryLeftOutputBit r
            (fun y =>
              (s0Config l (len+1+r) ((2*q+1)*2^r) b h).tape (h+y)) x) := by
    refine ⟨T',?_,h1,h2,h3,h4,h5,h6,?_,?_⟩
    · simpa [T,c0] using hrun
    · simpa [T,c0] using hpreserve
    · simpa [T,c0] using hleft
  exact s0Config_counted_decrement_from_relative_prefix l len q r b h hq hprefix

/-- Every bounded positive arbitrary-left S0 counter admits the exact
source decrement at the Inc0 cost. -/
theorem s0Config_counted_decrement_inc0
    (l : List Bool) (a z c : Nat) (h : Int)
    (hz : 0 < z) (hzlt : z < 2^a) :
    run tm2 (inc0Cost z c) (s0Config l a z c h) =
      some (s0Config l a (z-1) (c+1) h) := by
  obtain ⟨q,r,len,hfactor,ha,hq⟩ :=
    exists_odd_factor_bounded a z hz hzlt
  have hv := v2_of_odd_factorization z q r hfactor
  have hrun := s0Config_counted_decrement_anyValuation_hRun l len q r c h hq
  have hinput :
      s0Config l a z c h =
        s0Config l (len+1+r) ((2*q+1)*2^r) c h := by
    rw [ha,hfactor]
  have houtput :
      s0Config l a (z-1) (c+1) h =
        s0Config l (len+1+r) (((2*q+1)*2^r)-1) (c+1) h := by
    rw [ha,hfactor]
  simpa [inc0Cost,hv,hinput,houtput] using hrun

/-- Drain every bounded arbitrary-left S0 counter into its right unary
counter, with the exact recursively accumulated Inc0 cost. -/
theorem s0Config_counted_drain_general
    (l : List Bool) (a z c : Nat) (h : Int)
    (hbound : z < 2^a) :
    run tm2 (drainCost z c) (s0Config l a z c h) =
      some (s0Config l a 0 (c+z) h) := by
  have hInc0 : ∀ z' c', 0 < z' → z' < 2^a →
      run tm2 (inc0Cost z' c') (s0Config l a z' c' h) =
        some (s0Config l a (z'-1) (c'+1) h) := by
    intro z' c' hz hzlt
    exact s0Config_counted_decrement_inc0 l a z' c' h hz hzlt
  exact countedIncs0 l a z c h hbound hInc0

/-- The all-ones arbitrary-left S0 drain has the closed exact cost. -/
theorem s0Config_counted_drain_closed
    (l : List Bool) (a k : Nat) (h : Int)
    (hbound : 2^k-1 < 2^a) :
    run tm2 (6*4^k + 42*2^k - 12*k - 48)
      (s0Config l a (2^k-1) 0 h) =
      some (s0Config l a 0 (2^k-1) h) := by
  have hrun := s0Config_counted_drain_general l a (2^k-1) 0 h hbound
  rw [drainCost_binary_closed] at hrun
  simpa using hrun

#print axioms s0Config_carryInput_match
#print axioms s0Config_decrement_leftOutput
#print axioms s0Config_counted_decrement_of_prefix
#print axioms s0Config_counted_decrement_anyValuation_hRun
#print axioms s0Config_counted_decrement_inc0
#print axioms s0Config_counted_drain_general
#print axioms s0Config_counted_drain_closed

end BB6Coverage.Agent42Q4S0Drain
