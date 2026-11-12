import S1CarryOutputBridge
import CountedCarryLeftOutputR23
import LongResidue1
import S1CountedCarryPrefixBridge
import CountedSuffixOutput
import Lean.Elab.Tactic.Omega

namespace BB6Coverage.Agent24ChampionTime

open BB6Coverage.Agent8S1Encoder
open BB6Coverage.Agent48Champion
open BB6Coverage.Agent3CarryLeftOutput
open BB6Coverage.Agent24CarryLeftOutput

set_option maxHeartbeats 3000000

/-- The source S1 left stream has exactly the input-window pattern
d1^r ++ d0: all ones for i<3r, then 0,0,1. -/
private theorem sideBit_carryPrefixInput (r : Nat) (rest : List Bool)
    (i : Nat) (hi : i ≤ 3*r+2) :
    sideBit (d1pow r ++ d0 ++ rest) i =
      decide (i < 3*r ∨ i = 3*r+2) := by
  by_cases hlt : i < 3*r
  · have hones := sideBit_d1pow_true r i hlt
    rw [sideBit_append]
    simp [d1pow_length,hlt,hones]
  · have hc : i=3*r ∨ i=3*r+1 ∨ i=3*r+2 := by omega
    rcases hc with h0 | h1 | h2
    · subst i
      simp [sideBit_append,d1pow_length,d0,sideBit]
    · subst i
      simp [sideBit_append,d1pow_length,d0,sideBit]
    · subst i
      simp [sideBit_append,d1pow_length,d0,sideBit]

/-- The actual source S1 configuration matches the full local input
window required by the counted carry macro, for every odd-part quotient q. -/
theorem s1Config_carryInput_match
    (L n m len q r b : Nat) (h : Int) (hq : q < 2^len) :
    ∀ x, carryInputArea r x = true →
      (s1Config L n m (len+1+r) ((2*q+1)*2^r) b h).tape (h+x) =
        carryInputBit r x := by
  intro x harea
  by_cases hx0 : x ≤ 0
  · obtain ⟨i, rfl⟩ : ∃ i : Nat, x = -(i:Int) := by omega
    have hbound : i ≤ 3*r+2 := by
      simp [carryInputArea] at harea
      omega
    have hsource :
        (s1Config L n m (len+1+r) ((2*q+1)*2^r) b h).tape
            (h-(i:Int)) =
          sideBit
            (d1pow r ++ d0 ++ binDec len q ++
              markerWord m ++ d0 ++ binDec L n ++ lh) i :=
      s1Config_left_carryCells L n m len q r b h i hq
    have hside := sideBit_carryPrefixInput r
      (binDec len q ++ markerWord m ++ d0 ++ binDec L n ++ lh) i hbound
    have hbit : carryInputBit r (-(i:Int)) =
        decide (i < 3*r ∨ i = 3*r+2) := by
      simp [carryInputBit]
      omega
    have hcoord : h + (-(i:Int)) = h-(i:Int) := by omega
    rw [hcoord,hsource,hside,hbit]
  · obtain ⟨i, hxEq⟩ : ∃ i : Nat, x = 1+(i:Int) := by omega
    have hbound : i ≤ 5 := by
      simp [carryInputArea] at harea
      omega
    have hsource :
        (s1Config L n m (len+1+r) ((2*q+1)*2^r) b h).tape
            (h+1+(i:Int)) = sideBit (s1PhysicalRight b) i :=
      s1Config_right_cell L n m (len+1+r) ((2*q+1)*2^r) b h i
    rw [s1PhysicalRight_source] at hsource
    have hc : i=0 ∨ i=1 ∨ i=2 ∨ i=3 ∨ i=4 ∨ i=5 := by omega
    have hside : sideBit
        ([false,true,true,true,false,false] ++ d1pow (b+1)) i =
        carryInputBit r (1+(i:Int)) := by
      rcases hc with h0 | h1 | h2 | h3 | h4 | h5
      all_goals subst i <;> simp [sideBit,carryInputBit] <;> omega
    rw [hxEq,hsource,hside]

/-- The source S1 right side supplies the entire 111^(b+1) run
needed by the even counted suffix. -/
theorem s1Config_carryRightOnes
    (L n m len q r b : Nat) (h : Int) (hq : q < 2^len) :
    ∀ i : Nat, i < 3*(b+1) →
      (s1Config L n m (len+1+r) ((2*q+1)*2^r) b h).tape
        (h+7+(i:Int)) = true := by
  intro i hi
  have hcoord : h+7+(i:Int) = h+1+(6+(i:Int)) := by omega
  rw [hcoord,s1Config_right_cell,s1PhysicalRight_source]
  have hside :
      sideBit
        ([false,true,true,true,false,false] ++ d1pow (b+1))
        (6+i) = true := by
    rw [sideBit_append]
    have hlen : ([false,true,true,true,false,false] : List Bool).length = 6 := by rfl
    have hnot : ¬ 6+i < 6 := by omega
    have hidx : 6+i-6 = i := by omega
    simp [hlen,hnot,hidx]
    exact sideBit_d1pow_true (b+1) i hi
  exact hside

/-- Direct composition interface for prefix theorems already shifted
to the source configuration's absolute head coordinate. -/
theorem s1Config_counted_decrement_of_shifted_prefix
    (L n m len q r b : Nat) (h : Int) (hq : q < 2^len)
    (hprefix :
      ∃ Tpre : Int → Bool,
        run tm2 (15+12*r)
          (shiftConfig h ⟨3,0,fun x =>
            (s1Config L n m (len+1+r) ((2*q+1)*2^r) b h).tape (h+x)⟩) =
          some ⟨4,h+7,Tpre⟩ ∧
        Tpre (h+1) = true ∧ Tpre (h+2) = true ∧ Tpre (h+3) = true ∧
        Tpre (h+4) = true ∧ Tpre (h+5) = false ∧ Tpre (h+6) = true ∧
        (∀ x, 6 < x →
          Tpre (h+x) =
            (s1Config L n m (len+1+r) ((2*q+1)*2^r) b h).tape (h+x)) ∧
        (∀ x, x ≤ 0 →
          Tpre (h+x) = carryLeftOutputBit r
            (fun y =>
              (s1Config L n m (len+1+r) ((2*q+1)*2^r) b h).tape (h+y)) x)) :
    run tm2 (48+12*r+12*b)
        (s1Config L n m (len+1+r) ((2*q+1)*2^r) b h) =
      some (s1Config L n m (len+1+r) (((2*q+1)*2^r)-1) (b+1) h) := by
  let c0 := s1Config L n m (len+1+r) ((2*q+1)*2^r) b h
  let T : Int → Bool := fun x => c0.tape (h+x)
  rcases hprefix with
    ⟨Tpre,hrun,h1,h2,h3,h4,h5,h6,hpreserve,hleft⟩
  have hstart : shiftConfig h ⟨3,0,T⟩ = c0 := by
    ext
    · simp [shiftConfig,c0]
    · simp [shiftConfig,c0]
    · funext x
      simp [shiftConfig,T]
      omega
  let P : Int → Bool := fun x => Tpre (h+x)
  have hP1 : P 1 = true := by simpa [P] using h1
  have hP2 : P 2 = true := by simpa [P] using h2
  have hP3 : P 3 = true := by simpa [P] using h3
  have hP4 : P 4 = true := by simpa [P] using h4
  have hP5 : P 5 = false := by simpa [P] using h5
  have hP6 : P 6 = true := by simpa [P] using h6
  have hpreserveP : ∀ x, 6 < x →
      P x = c0.tape (h+x) := by
    intro x hx
    simpa [P,c0,s1Config] using hpreserve x hx
  have honeP : ∀ i : Nat, i < 3*(b+1) → P (7+(i:Int)) = true := by
    intro i hi
    rw [hpreserveP (7+(i:Int)) (by omega)]
    exact s1Config_carryRightOnes L n m len q r b h hq i hi
  have hleftP : ∀ x, x ≤ 0 →
      P x = (s0Config (markerWord m ++ d0 ++ binDec L n ++ lh)
        (len+1+r) (((2*q+1)*2^r)-1) (b+1) h).tape (h+x) := by
    intro x hx
    calc
      P x = Tpre (h+x) := rfl
      _ = carryLeftOutputBit r
          (fun y => (s1Config L n m (len+1+r) ((2*q+1)*2^r) b h).tape (h+y)) x :=
        hleft x hx
      _ = (s0Config (markerWord m ++ d0 ++ binDec L n ++ lh)
          (len+1+r) (((2*q+1)*2^r)-1) (b+1) h).tape (h+x) := by
        simpa [s1Config] using
          s1Config_decrement_leftOutput L n m len q r b h hq x hx
  have hrun' := hrun
  rw [hstart] at hrun'
  have hprefix0 : run tm2 (15+12*r)
      (s0Config (markerWord m ++ d0 ++ binDec L n ++ lh)
        (len+1+r) ((2*q+1)*2^r) b h) =
      some ⟨4,h+7,Tpre⟩ := by
    simpa [c0,s1Config] using hrun'
  have hdec := s0Config_counted_decrement_of_prefix
    (markerWord m ++ d0 ++ binDec L n ++ lh)
    (len+1+r) ((2*q+1)*2^r) (((2*q+1)*2^r)-1) b r h P
    hprefix0 hP1 hP2 hP3 hP4 hP5 hP6 honeP hpreserveP hleftP
  simpa [s1Config] using hdec

/-- Generic source composition: once the primitive carry prefix has its
local six-cell output, right exterior, and exact left-output identity, the
existing suffix theorem proves a full S1 decrement. -/
theorem s1Config_counted_decrement_of_prefix
    (L n m len q r b : Nat) (h : Int) (hq : q < 2^len)
    (hprefix :
      ∃ T' : Int → Bool,
        run tm2 (15+12*r)
          ⟨3,0,fun x =>
            (s1Config L n m (len+1+r) ((2*q+1)*2^r) b h).tape (h+x)⟩ =
          some ⟨4,7,T'⟩ ∧
        T' 1 = true ∧ T' 2 = true ∧ T' 3 = true ∧
        T' 4 = true ∧ T' 5 = false ∧ T' 6 = true ∧
        (∀ x, 6 < x →
          T' x = (s1Config L n m (len+1+r) ((2*q+1)*2^r) b h).tape (h+x)) ∧
        (∀ x, x ≤ 0 →
          T' x = carryLeftOutputBit r
            (fun y =>
              (s1Config L n m (len+1+r) ((2*q+1)*2^r) b h).tape (h+y)) x)) :
    run tm2 (48+12*r+12*b)
        (s1Config L n m (len+1+r) ((2*q+1)*2^r) b h) =
      some (s1Config L n m (len+1+r) (((2*q+1)*2^r)-1) (b+1) h) := by
  let c0 := s1Config L n m (len+1+r) ((2*q+1)*2^r) b h
  let T : Int → Bool := fun x => c0.tape (h+x)
  rcases hprefix with
    ⟨T',hprun,h1,h2,h3,h4,h5,h6,hpreserve,hleft⟩
  let Tpre : Int → Bool := fun x => T' (x-h)
  have hstart : shiftConfig h ⟨3,0,T⟩ = c0 := by
    ext
    · simp [shiftConfig,c0]
    · simp [shiftConfig,c0]
    · funext x
      simp [shiftConfig,T]
      omega
  have hshift := shift_run h tm2 ⟨3,0,T⟩ (15+12*r)
  rw [hprun] at hshift
  simp only [Option.map] at hshift
  rw [hstart] at hshift
  have hprefix0 : run tm2 (15+12*r) c0 =
      some ⟨4,h+7,Tpre⟩ := by
    simpa [shiftConfig,Tpre] using hshift
  let P : Int → Bool := fun x => Tpre (h+x)
  have hP : ∀ x, P x = T' x := by
    intro x
    simp [P,Tpre]
  have hP1 : P 1 = true := by simpa [P,Tpre] using h1
  have hP2 : P 2 = true := by simpa [P,Tpre] using h2
  have hP3 : P 3 = true := by simpa [P,Tpre] using h3
  have hP4 : P 4 = true := by simpa [P,Tpre] using h4
  have hP5 : P 5 = false := by simpa [P,Tpre] using h5
  have hP6 : P 6 = true := by simpa [P,Tpre] using h6
  have hpreserveP : ∀ x, 6 < x →
      P x = c0.tape (h+x) := by
    intro x hx
    simpa [P,Tpre] using hpreserve x hx
  have honeP : ∀ i : Nat, i < 3*(b+1) → P (7+(i:Int)) = true := by
    intro i hi
    rw [hpreserveP (7+(i:Int)) (by omega)]
    exact s1Config_carryRightOnes L n m len q r b h hq i hi
  have hleftP : ∀ x, x ≤ 0 →
      P x = (s0Config (markerWord m ++ d0 ++ binDec L n ++ lh)
        (len+1+r) (((2*q+1)*2^r)-1) (b+1) h).tape (h+x) := by
    intro x hx
    calc
      P x = T' x := by simp [P,Tpre]
      _ = carryLeftOutputBit r
          (fun y => (s1Config L n m (len+1+r) ((2*q+1)*2^r) b h).tape (h+y)) x :=
        hleft x hx
      _ = (s0Config (markerWord m ++ d0 ++ binDec L n ++ lh)
          (len+1+r) (((2*q+1)*2^r)-1) (b+1) h).tape (h+x) := by
        simpa [s1Config] using
          s1Config_decrement_leftOutput L n m len q r b h hq x hx
  have hprefix0' : run tm2 (15+12*r)
      (s0Config (markerWord m ++ d0 ++ binDec L n ++ lh)
        (len+1+r) ((2*q+1)*2^r) b h) =
      some ⟨4,h+7,Tpre⟩ := by
    simpa [c0,s1Config] using hprefix0
  have hdec := s0Config_counted_decrement_of_prefix
    (markerWord m ++ d0 ++ binDec L n ++ lh)
    (len+1+r) ((2*q+1)*2^r) (((2*q+1)*2^r)-1) b r h Tpre
    hprefix0' hP1 hP2 hP3 hP4 hP5 hP6 honeP hpreserveP hleftP
  simpa [s1Config] using hdec

/-- Long residue one: consume Agent 42's already-shifted prefix
interface directly, translating only the duplicate left-output definition. -/
theorem s1Config_counted_decrement_r1
    (L n m len q k b : Nat) (h : Int) (hq : q < 2^len) (hk : 0 < k) :
    run tm2 (48+12*(4*k+1)+12*b)
        (s1Config L n m (len+1+(4*k+1))
          ((2*q+1)*2^(4*k+1)) b h) =
      some (s1Config L n m (len+1+(4*k+1))
        (((2*q+1)*2^(4*k+1))-1) (b+1) h) := by
  let T : Int → Bool := fun x =>
    (s1Config L n m (len+1+(4*k+1))
      ((2*q+1)*2^(4*k+1)) b h).tape (h+x)
  have hmatch := s1Config_carryInput_match L n m len q (4*k+1) b h hq
  obtain ⟨Tpre,hrun,h1,h2,h3,h4,h5,h6,hpreserve,hleft⟩ :=
    BB6Coverage.Agent42CarryLeftOutput.carryLongPrefix_r1_shifted
      k T h hmatch hk
  have hprefix :
      ∃ Tpre : Int → Bool,
        run tm2 (15+12*(4*k+1))
          (shiftConfig h ⟨3,0,fun x =>
            (s1Config L n m (len+1+(4*k+1))
              ((2*q+1)*2^(4*k+1)) b h).tape (h+x)⟩) =
          some ⟨4,h+7,Tpre⟩ ∧
        Tpre (h+1) = true ∧ Tpre (h+2) = true ∧ Tpre (h+3) = true ∧
        Tpre (h+4) = true ∧ Tpre (h+5) = false ∧ Tpre (h+6) = true ∧
        (∀ x, 6 < x →
          Tpre (h+x) =
            (s1Config L n m (len+1+(4*k+1))
              ((2*q+1)*2^(4*k+1)) b h).tape (h+x)) ∧
        (∀ x, x ≤ 0 →
          Tpre (h+x) = carryLeftOutputBit (4*k+1)
            (fun y =>
              (s1Config L n m (len+1+(4*k+1))
                ((2*q+1)*2^(4*k+1)) b h).tape (h+y)) x) := by
    refine ⟨Tpre,hrun,h1,h2,h3,h4,h5,h6,hpreserve,?_⟩
    intro x hx
    simpa [BB6Coverage.Agent42CarryLeftOutput.carryLeftOutputBit,
      BB6Coverage.Agent3CarryLeftOutput.carryLeftOutputBit] using hleft x hx
  exact s1Config_counted_decrement_of_shifted_prefix
    L n m len q (4*k+1) b h hq hprefix

/-- The even-valuation residue-2 carry prefix is a complete source S1
counted decrement, including the canonical full tape after the suffix. -/
theorem s1Config_counted_decrement_r2
    (L n m len q k b : Nat) (h : Int) (hq : q < 2^len) :
    run tm2 (48+12*(4*k+2)+12*b)
        (s1Config L n m (len+1+(4*k+2))
          ((2*q+1)*2^(4*k+2)) b h) =
      some (s1Config L n m (len+1+(4*k+2))
        (((2*q+1)*2^(4*k+2))-1) (b+1) h) := by
  let T : Int → Bool := fun x =>
    (s1Config L n m (len+1+(4*k+2))
      ((2*q+1)*2^(4*k+2)) b h).tape (h+x)
  have hmatch := s1Config_carryInput_match L n m len q (4*k+2) b h hq
  have hprefix := carryLongPrefix_r2_left k T hmatch
  exact s1Config_counted_decrement_of_prefix
    L n m len q (4*k+2) b h hq hprefix

/-- The even-valuation residue-3 carry prefix is a complete source S1
counted decrement, including the canonical full tape after the suffix. -/
theorem s1Config_counted_decrement_r3
    (L n m len q k b : Nat) (h : Int) (hq : q < 2^len) :
    run tm2 (48+12*(4*k+3)+12*b)
        (s1Config L n m (len+1+(4*k+3))
          ((2*q+1)*2^(4*k+3)) b h) =
      some (s1Config L n m (len+1+(4*k+3))
        (((2*q+1)*2^(4*k+3))-1) (b+1) h) := by
  let T : Int → Bool := fun x =>
    (s1Config L n m (len+1+(4*k+3))
      ((2*q+1)*2^(4*k+3)) b h).tape (h+x)
  have hmatch := s1Config_carryInput_match L n m len q (4*k+3) b h hq
  have hprefix := carryLongPrefix_r3_left k T hmatch
  exact s1Config_counted_decrement_of_prefix
    L n m len q (4*k+3) b h hq hprefix

/-- Complete source-level S1 decrement for every positive carry
valuation r. The four residue classes are closed by the r=0 bridge,
the short/long r=1 bridges, and the new r=2/r=3 left-output bridges. -/
theorem s1Config_counted_decrement_allPositive
    (L n m len q r b : Nat) (h : Int)
    (hq : q < 2^len) (hr : 0 < r) :
    run tm2 (48+12*r+12*b)
        (s1Config L n m (len+1+r) ((2*q+1)*2^r) b h) =
      some (s1Config L n m (len+1+r) (((2*q+1)*2^r)-1) (b+1) h) := by
  let k := r/4
  have hdiv := Nat.mod_add_div r 4
  have hdecomp : 4*k + r%4 = r := by
    dsimp [k]
    omega
  have hmodlt : r%4 < 4 := Nat.mod_lt r (by omega)
  have hmod : r%4=0 ∨ r%4=1 ∨ r%4=2 ∨ r%4=3 := by omega
  let T : Int → Bool := fun x =>
    (s1Config L n m (len+1+r) ((2*q+1)*2^r) b h).tape (h+x)
  have hmatch := s1Config_carryInput_match L n m len q r b h hq
  rcases hmod with h0 | h1 | h2 | h3
  · have hrEq : r = 4*k := by omega
    have hm : ∀ x, carryInputArea (4*k) x = true →
        T x = carryInputBit (4*k) x := by
      simpa [hrEq] using hmatch
    obtain ⟨Tgen,hrunGen,g1,g2,g3,g4,g5,g6,gout⟩ :=
      carryPrefix_anyPositive (4*k) T (by omega) hm
    obtain ⟨Tleft,hrunLeft,gleft⟩ :=
      BB6Coverage.Agent3CarryLeftOutput.carryLongPrefix_r0_left
        k T hm
    have hconf : (⟨4,7,Tgen⟩ : Config) = ⟨4,7,Tleft⟩ := by
      apply Option.some.inj
      calc
        some (⟨4,7,Tgen⟩ : Config) =
            run tm2 (15+12*(4*k)) ⟨3,0,T⟩ := hrunGen.symm
        _ = some ⟨4,7,Tleft⟩ := hrunLeft
    cases hconf
    have hprefix :
        ∃ T' : Int → Bool,
          run tm2 (15+12*(4*k)) ⟨3,0,T⟩ = some ⟨4,7,T'⟩ ∧
          T' 1 = true ∧ T' 2 = true ∧ T' 3 = true ∧
          T' 4 = true ∧ T' 5 = false ∧ T' 6 = true ∧
          (∀ x, 6 < x → T' x = T x) ∧
          (∀ x, x ≤ 0 → T' x = carryLeftOutputBit (4*k) T x) := by
      refine ⟨Tgen,hrunGen,g1,g2,g3,g4,g5,g6,gout,?_⟩
      intro x hx
      simpa using gleft x hx
    exact s1Config_counted_decrement_of_prefix
      L n m len q (4*k) b h hq (by simpa [hrEq,T] using hprefix)
  · have hrEq : r = 4*k+1 := by omega
    by_cases hk : k=0
    · have hr1 : r=1 := by omega
      have hm : ∀ x, carryInputArea 1 x = true →
          T x = carryInputBit 1 x := by
        simpa [hr1] using hmatch
      obtain ⟨T',hrun,s1,s2,s3,s4,s5,s6,sout,sleft⟩ :=
        carryShortPrefix_r1 T hm
      have hleft : ∀ x, x ≤ 0 → T' x = carryLeftOutputBit 1 T x := by
        intro x hx
        simpa [carryLeftOutputBit] using sleft x hx
      have hprefix :
          ∃ T' : Int → Bool,
            run tm2 (15+12*1) ⟨3,0,T⟩ = some ⟨4,7,T'⟩ ∧
            T' 1 = true ∧ T' 2 = true ∧ T' 3 = true ∧
            T' 4 = true ∧ T' 5 = false ∧ T' 6 = true ∧
            (∀ x, 6 < x → T' x = T x) ∧
            (∀ x, x ≤ 0 → T' x = carryLeftOutputBit 1 T x) := by
        refine ⟨T',?_,s1,s2,s3,s4,s5,s6,sout,hleft⟩
        simpa using hrun
      exact s1Config_counted_decrement_of_prefix
        L n m len q 1 b h hq (by simpa [hr1,T] using hprefix)
    · have hdec := s1Config_counted_decrement_r1
        L n m len q k b h hq hk
      simpa [hrEq] using hdec
  · have hrEq : r = 4*k+2 := by omega
    have hdec := s1Config_counted_decrement_r2
      L n m len q k b h hq
    simpa [hrEq] using hdec
  · have hrEq : r = 4*k+3 := by omega
    have hdec := s1Config_counted_decrement_r3
      L n m len q k b h hq
    simpa [hrEq] using hdec

/-- Every even positive bounded S1 counter admits a complete
source-level counted decrement. The odd-factor decomposition supplies
the positive carry valuation, and the all-residue prefix theorem closes it. -/
theorem s1Config_counted_decrement_even
    (L n m a z b : Nat) (h : Int)
    (hz : 0 < z) (hzlt : z < 2^a) (heven : z%2=0) :
    ∃ q r len, z=(2*q+1)*2^r ∧ a=len+1+r ∧ q<2^len ∧ 0<r ∧
      run tm2 (48+12*r+12*b) (s1Config L n m a z b h) =
        some (s1Config L n m a (z-1) (b+1) h) := by
  obtain ⟨q,r,len,hr,ha,hq⟩ :=
    exists_odd_factor_bounded a z hz hzlt
  have hrpos : 0 < r := by
    by_contra hnot
    have hr0 : r=0 := by omega
    have hodd : ((2*q+1)*2^r)%2=1 := by
      simp [hr0]
    rw [hr] at heven
    omega
  have hdec := s1Config_counted_decrement_allPositive
    L n m len q r b h hq hrpos
  have hinput : s1Config L n m a z b h =
      s1Config L n m (len+1+r) ((2*q+1)*2^r) b h := by
    rw [ha,hr]
  have houtput : s1Config L n m a (z-1) (b+1) h =
      s1Config L n m (len+1+r) (((2*q+1)*2^r)-1) (b+1) h := by
    rw [ha,hr]
  refine ⟨q,r,len,hr,ha,hq,hrpos,?_⟩
  simpa [hinput,houtput] using hdec

#print axioms s1Config_counted_decrement_allPositive
#print axioms s1Config_counted_decrement_even

/-- Canonicalize Agent 42's existing even-counter return witness:
the returned state-3 tape is exactly the S1 encoding of z-1 and b+1. -/
theorem s1Config_evenCounter_countedReturn_canonical
    (L n m a z b : Nat) (h : Int)
    (hz : 0<z) (hzlt : z<2^a) (heven : z%2=0) :
    ∃ q r len T',
      z=(2*q+1)*2^r ∧ a=len+1+r ∧ q<2^len ∧ 0<r ∧
      run tm2 (48+12*r+12*b) (s1Config L n m a z b h) =
        some ⟨(3 : Fin 6),h,T'⟩ ∧
      T' = (s1Config L n m a (z-1) (b+1) h).tape := by
  obtain ⟨q,r,len,T',hfactor,ha,hq,hr,hrun⟩ :=
    BB6Coverage.Agent42CarryPrefixBridge.s1Config_evenCounter_countedReturn
      L n m a z b h hz hzlt heven
  have hdec := s1Config_counted_decrement_allPositive
    L n m len q r b h hq hr
  have hinput : s1Config L n m a z b h =
      s1Config L n m (len+1+r) ((2*q+1)*2^r) b h := by
    rw [ha,hfactor]
  have houtput : s1Config L n m a (z-1) (b+1) h =
      s1Config L n m (len+1+r) (((2*q+1)*2^r)-1) (b+1) h := by
    rw [ha,hfactor]
  have hcanonical : run tm2 (48+12*r+12*b)
      (s1Config L n m a z b h) =
      some (s1Config L n m a (z-1) (b+1) h) := by
    simpa [hinput,houtput] using hdec
  have hcfg : (⟨(3 : Fin 6),h,T'⟩ : Config) =
      s1Config L n m a (z-1) (b+1) h := by
    apply Option.some.inj
    calc
      some (⟨(3 : Fin 6),h,T'⟩ : Config) =
          run tm2 (48+12*r+12*b) (s1Config L n m a z b h) := hrun.symm
      _ = some (s1Config L n m a (z-1) (b+1) h) := hcanonical
  refine ⟨q,r,len,T',hfactor,ha,hq,hr,hrun,?_⟩
  exact congrArg Config.tape hcfg

#print axioms s1Config_evenCounter_countedReturn_canonical
#print axioms s1Config_carryInput_match
#print axioms s1Config_carryRightOnes
#print axioms s1Config_counted_decrement_of_prefix
#print axioms s1Config_counted_decrement_r2
#print axioms s1Config_counted_decrement_r3

end BB6Coverage.Agent24ChampionTime
