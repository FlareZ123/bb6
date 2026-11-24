import S1CarryOutputBridge
import CountedSuffixOutput
import CountedCarryPrefixHRun
import Lean.Elab.Tactic.Omega

namespace BB6Coverage.Agent24ChampionTime

/-- Extensionality for the repository's infinite-tape configuration.
The base structure intentionally has no generated Config.ext theorem. -/
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

open BB6Coverage.Agent8S1Encoder
open BB6Coverage.Agent48Champion
open BB6Coverage.Agent3CarryLeftOutput

set_option maxHeartbeats 3000000

/-- The source S1 left stream has exactly the input-window pattern
d1^r ++ d0: all ones for i<3r, then 0,0,1. -/
private theorem sideBit_carryPrefixInput (r : Nat) (rest : List Bool)
    (i : Nat) (hi : i ≤ 3*r+2) :
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

/-- The actual source S1 configuration matches the full local input
window required by the counted carry macro, for every odd-part quotient q. -/
theorem s1Config_carryInput_match
    (L n m len q r b : Nat) (h : Int) (hq : q < 2^len) :
    ∀ x, carryInputArea r x = true →
      (s1Config L n m (len+1+r) ((2*q+1)*2^r) b h).tape (h+x) =
        carryInputBit r x := by
  intro x harea
  by_cases hx0 : x ≤ 0
  · let i : Nat := Int.toNat (-x)
    have hxEq : x = -(i:Int) := by
      dsimp [i]
      have hnonneg : 0 ≤ -x := Int.neg_nonneg.mpr hx0
      have hcast : (Int.toNat (-x) : Int) = -x :=
        Int.toNat_of_nonneg hnonneg
      calc
        x = -(-x) := by simp
        _ = -(Int.toNat (-x) : Int) := by rw [hcast]
    rw [hxEq] at harea
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
    have hside :
        sideBit
          (d1pow r ++ d0 ++ binDec len q ++
            markerWord m ++ d0 ++ binDec L n ++ lh) i =
          decide (i < 3*r ∨ i = 3*r+2) := by
      simpa only [List.append_assoc] using
        sideBit_carryPrefixInput r
          (binDec len q ++ markerWord m ++ d0 ++ binDec L n ++ lh) i hbound
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
    simp only [hxEq]
    calc
      (s1Config L n m (len+1+r) ((2*q+1)*2^r) b h).tape
          (h + (-(i:Int))) =
          (s1Config L n m (len+1+r) ((2*q+1)*2^r) b h).tape
            (h-(i:Int)) := by rw [hcoord]
      _ = sideBit
          (d1pow r ++ d0 ++ binDec len q ++
            markerWord m ++ d0 ++ binDec L n ++ lh) i := hsource
      _ = decide (i < 3*r ∨ i = 3*r+2) := hside
      _ = carryInputBit r (-(i:Int)) := hbit.symm
  · let i : Nat := Int.toNat (x-1)
    have hxEq : x = 1+(i:Int) := by
      dsimp [i]
      have hnonneg : 0 ≤ x-1 := by omega
      have hcast : (Int.toNat (x-1) : Int) = x-1 :=
        Int.toNat_of_nonneg hnonneg
      calc
        x = 1+(x-1) := by omega
        _ = 1+(Int.toNat (x-1) : Int) := by rw [hcast]
    rw [hxEq] at harea
    have hbound : i ≤ 5 := by
      simp [carryInputArea] at harea
      omega
    have hsource :
        (s1Config L n m (len+1+r) ((2*q+1)*2^r) b h).tape
            (h+1+(i:Int)) = sideBit (s1PhysicalRight b) i :=
      s1Config_right_cell L n m (len+1+r) ((2*q+1)*2^r) b h i
    rw [s1PhysicalRight_source] at hsource
    have hsideAll (j : Nat) (hj : j ≤ 5) :
        sideBit ([false,true,true,true,false,false] ++ d1pow (b+1)) j =
          carryInputBit r (1+(j:Int)) := by
      have hc : j=0 ∨ j=1 ∨ j=2 ∨ j=3 ∨ j=4 ∨ j=5 := by omega
      rcases hc with h0 | h1 | h2 | h3 | h4 | h5
      all_goals subst j <;> simp [sideBit,carryInputBit] <;> omega
    have hside := hsideAll i hbound
    simp only [hxEq]
    have hcoord : h + (1+(i:Int)) = h+1+(i:Int) := by omega
    calc
      (s1Config L n m (len+1+r) ((2*q+1)*2^r) b h).tape
          (h+(1+(i:Int))) =
        (s1Config L n m (len+1+r) ((2*q+1)*2^r) b h).tape
          (h+1+(i:Int)) := by rw [hcoord]
      _ = sideBit ([false,true,true,true,false,false] ++ d1pow (b+1)) i :=
        hsource
      _ = carryInputBit r (1+(i:Int)) := hside
/-- The source S1 right side supplies the entire 111^(b+1) run
needed by the even counted suffix. -/
theorem s1Config_carryRightOnes
    (L n m len q r b : Nat) (h : Int) (hq : q < 2^len) :
    ∀ i : Nat, i < 3*(b+1) →
      (s1Config L n m (len+1+r) ((2*q+1)*2^r) b h).tape
        (h+7+(i:Int)) = true := by
  intro i hi
  have hcoord : h+7+(i:Int) = h+1+(6+(i:Int)) := by omega
  have hsource :
      (s1Config L n m (len+1+r) ((2*q+1)*2^r) b h).tape
          (h+1+(6+(i:Int))) =
        sideBit (s1PhysicalRight b) (6+i) := by
    simpa using
      s1Config_right_cell L n m (len+1+r) ((2*q+1)*2^r) b h (6+i)
  rw [s1PhysicalRight_source] at hsource
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
  rw [hcoord,hsource,hside]

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
    apply config_ext_by_fields
    · simp [shiftConfig,c0,s1Config]
    · simp [shiftConfig,c0,s1Config]
    · funext x
      change T (x-h) = c0.tape x
      dsimp [T]
      rw [show h + (x-h) = x by omega]
  have hrun' := hrun
  rw [hstart] at hrun'
  have hprefix0 : run tm2 (15+12*r)
      (s0Config (markerWord m ++ d0 ++ binDec L n ++ lh)
        (len+1+r) ((2*q+1)*2^r) b h) =
      some ⟨4,h+7,Tpre⟩ := by
    simpa [c0,s1Config] using hrun'
  have hpreserve' : ∀ x, 6 < x →
      Tpre (h+x) =
        (s0Config (markerWord m ++ d0 ++ binDec L n ++ lh)
          (len+1+r) ((2*q+1)*2^r) b h).tape (h+x) := by
    intro x hx
    simpa [s1Config] using hpreserve x hx
  have hone : ∀ i : Nat, i < 3*(b+1) →
      Tpre (h+7+(i:Int)) = true := by
    intro i hi
    have hpres :
        Tpre (h+7+(i:Int)) =
          (s1Config L n m (len+1+r) ((2*q+1)*2^r) b h).tape
            (h+7+(i:Int)) := by
      simpa [Int.add_assoc] using hpreserve (7+(i:Int)) (by omega)
    rw [hpres]
    exact s1Config_carryRightOnes L n m len q r b h hq i hi
  have hleft' : ∀ x, x ≤ 0 →
      Tpre (h+x) =
        (s0Config (markerWord m ++ d0 ++ binDec L n ++ lh)
          (len+1+r) (((2*q+1)*2^r)-1) (b+1) h).tape (h+x) := by
    intro x hx
    rw [hleft x hx]
    simpa [s1Config] using
      s1Config_decrement_leftOutput L n m len q r b h hq x hx
  have hdec := s0Config_counted_decrement_of_prefix
    (markerWord m ++ d0 ++ binDec L n ++ lh)
    (len+1+r) ((2*q+1)*2^r) (((2*q+1)*2^r)-1) b r h Tpre
    hprefix0 h1 h2 h3 h4 h5 h6 hone hpreserve' hleft'
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
  have hcancel (x : Int) : h+x-h = x := by omega
  have hstart : shiftConfig h ⟨3,0,T⟩ = c0 := by
    apply config_ext_by_fields
    · simp [shiftConfig,c0,s1Config]
    · simp [shiftConfig,c0,s1Config]
    · funext x
      change T (x-h) = c0.tape x
      dsimp [T]
      rw [show h + (x-h) = x by omega]
  have hshift := shift_run h tm2 ⟨3,0,T⟩ (15+12*r)
  rw [hprun] at hshift
  simp only [Option.map] at hshift
  rw [hstart] at hshift
  have hhead : (7:Int)+h = h+7 := by omega
  have hprefix0 : run tm2 (15+12*r) c0 =
      some ⟨4,h+7,Tpre⟩ := by
    simpa [shiftConfig,Tpre,hhead] using hshift
  have hpreserve' : ∀ x, 6 < x →
      Tpre (h+x) =
        (s0Config (markerWord m ++ d0 ++ binDec L n ++ lh)
          (len+1+r) ((2*q+1)*2^r) b h).tape (h+x) := by
    intro x hx
    simpa [Tpre, hcancel, s1Config] using hpreserve x hx
  have hone : ∀ i : Nat, i < 3*(b+1) →
      Tpre (h+7+(i:Int)) = true := by
    intro i hi
    have hpres :
        Tpre (h+7+(i:Int)) =
          (s1Config L n m (len+1+r) ((2*q+1)*2^r) b h).tape
            (h+7+(i:Int)) := by
      simpa [Tpre, hcancel, Int.add_assoc] using hpreserve (7+(i:Int)) (by omega)
    rw [hpres]
    exact s1Config_carryRightOnes L n m len q r b h hq i hi
  have hleft' : ∀ x, x ≤ 0 →
      Tpre (h+x) =
        (s0Config (markerWord m ++ d0 ++ binDec L n ++ lh)
          (len+1+r) (((2*q+1)*2^r)-1) (b+1) h).tape (h+x) := by
    intro x hx
    calc
      Tpre (h+x) =
          carryLeftOutputBit r
            (fun y => (s1Config L n m (len+1+r) ((2*q+1)*2^r) b h).tape (h+y)) x := by
        simpa [Tpre, hcancel] using hleft x hx
      _ = (s0Config (markerWord m ++ d0 ++ binDec L n ++ lh)
          (len+1+r) (((2*q+1)*2^r)-1) (b+1) h).tape (h+x) := by
        simpa [s1Config] using
          s1Config_decrement_leftOutput L n m len q r b h hq x hx
  have h1' : Tpre (h+1) = true := by simpa [Tpre, hcancel] using h1
  have h2' : Tpre (h+2) = true := by simpa [Tpre, hcancel] using h2
  have h3' : Tpre (h+3) = true := by simpa [Tpre, hcancel] using h3
  have h4' : Tpre (h+4) = true := by simpa [Tpre, hcancel] using h4
  have h5' : Tpre (h+5) = false := by simpa [Tpre, hcancel] using h5
  have h6' : Tpre (h+6) = true := by simpa [Tpre, hcancel] using h6
  have hdec := s0Config_counted_decrement_of_prefix
    (markerWord m ++ d0 ++ binDec L n ++ lh)
    (len+1+r) ((2*q+1)*2^r) (((2*q+1)*2^r)-1) b r h Tpre
    hprefix0 h1' h2' h3' h4' h5' h6' hone hpreserve' hleft'
  simpa [s1Config] using hdec

/-- Uniform source-level S1 decrement for every 2-adic valuation r,
including r=0. The exact counted LInc H-run supplies the prefix for all r;
the existing suffix interface then canonicalizes the complete S1 tape. -/
theorem s1Config_counted_decrement_anyValuation_hRun
    (L n m len q r b : Nat) (h : Int)
    (hq : q < 2^len) :
    run tm2 (48+12*r+12*b)
        (s1Config L n m (len+1+r) ((2*q+1)*2^r) b h) =
      some (s1Config L n m (len+1+r) (((2*q+1)*2^r)-1) (b+1) h) := by
  let T : Int → Bool := fun x =>
    (s1Config L n m (len+1+r) ((2*q+1)*2^r) b h).tape (h+x)
  have hmatch := s1Config_carryInput_match L n m len q r b h hq
  obtain ⟨T',hrun,h1,h2,h3,h4,h5,h6,hpreserve,hleft⟩ :=
    BB6Coverage.Agent48Champion.carryPrefix_anyNonnegative_hRun r T hmatch
  have hprefix :
      ∃ T' : Int → Bool,
        run tm2 (15+12*r)
          ⟨3,0,fun x =>
            (s1Config L n m (len+1+r) ((2*q+1)*2^r) b h).tape (h+x)⟩ =
          some ⟨4,7,T'⟩ ∧
        T' 1 = true ∧ T' 2 = true ∧ T' 3 = true ∧
        T' 4 = true ∧ T' 5 = false ∧ T' 6 = true ∧
        (∀ x, 6 < x →
          T' x =
            (s1Config L n m (len+1+r) ((2*q+1)*2^r) b h).tape (h+x)) ∧
        (∀ x, x ≤ 0 →
          T' x = carryLeftOutputBit r
            (fun y =>
              (s1Config L n m (len+1+r) ((2*q+1)*2^r) b h).tape (h+y)) x) := by
    refine ⟨T', ?_, h1, h2, h3, h4, h5, h6, ?_, ?_⟩
    · simpa [T] using hrun
    · simpa [T] using hpreserve
    · simpa [T] using hleft
  exact s1Config_counted_decrement_of_prefix
    L n m len q r b h hq hprefix

/-- The former residue-one bridge is now a direct specialization of the
uniform all-valuation H-run; the positivity side condition is retained only
for compatibility with the earlier interface. -/
theorem s1Config_counted_decrement_r1
    (L n m len q k b : Nat) (h : Int) (hq : q < 2^len)
    (_hk : 0 < k) :
    run tm2 (48+12*(4*k+1)+12*b)
        (s1Config L n m (len+1+(4*k+1))
          ((2*q+1)*2^(4*k+1)) b h) =
      some (s1Config L n m (len+1+(4*k+1))
        (((2*q+1)*2^(4*k+1))-1) (b+1) h) := by
  exact s1Config_counted_decrement_anyValuation_hRun
    L n m len q (4*k+1) b h hq

/-- The former residue-two bridge is a direct specialization of the
uniform all-valuation H-run. -/
theorem s1Config_counted_decrement_r2
    (L n m len q k b : Nat) (h : Int) (hq : q < 2^len) :
    run tm2 (48+12*(4*k+2)+12*b)
        (s1Config L n m (len+1+(4*k+2))
          ((2*q+1)*2^(4*k+2)) b h) =
      some (s1Config L n m (len+1+(4*k+2))
        (((2*q+1)*2^(4*k+2))-1) (b+1) h) := by
  exact s1Config_counted_decrement_anyValuation_hRun
    L n m len q (4*k+2) b h hq

/-- The former residue-three bridge is a direct specialization of the
uniform all-valuation H-run. -/
theorem s1Config_counted_decrement_r3
    (L n m len q k b : Nat) (h : Int) (hq : q < 2^len) :
    run tm2 (48+12*(4*k+3)+12*b)
        (s1Config L n m (len+1+(4*k+3))
          ((2*q+1)*2^(4*k+3)) b h) =
      some (s1Config L n m (len+1+(4*k+3))
        (((2*q+1)*2^(4*k+3))-1) (b+1) h) := by
  exact s1Config_counted_decrement_anyValuation_hRun
    L n m len q (4*k+3) b h hq

/-- Backward-compatible positive-valuation wrapper. The uniform H-run
actually proves the stronger statement for r=0 as well. -/
theorem s1Config_counted_decrement_allPositive
    (L n m len q r b : Nat) (h : Int)
    (hq : q < 2^len) (hr : 0 < r) :
    run tm2 (48+12*r+12*b)
        (s1Config L n m (len+1+r) ((2*q+1)*2^r) b h) =
      some (s1Config L n m (len+1+r) (((2*q+1)*2^r)-1) (b+1) h) := by
  exact s1Config_counted_decrement_anyValuation_hRun
    L n m len q r b h hq

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
    by_cases hr0 : r = 0
    · rw [hr0, Nat.pow_zero, Nat.mul_one] at hr
      rw [hr] at heven
      omega
    · omega
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

#print axioms s1Config_counted_decrement_anyValuation_hRun
#print axioms s1Config_counted_decrement_allPositive
#print axioms s1Config_counted_decrement_even

/-- Canonical state-3 witness for every even bounded S1 counter.  This
now follows from the uniform source decrement itself, rather than importing
a second prefix witness with a separate dependency chain. -/
theorem s1Config_evenCounter_countedReturn_canonical
    (L n m a z b : Nat) (h : Int)
    (hz : 0<z) (hzlt : z<2^a) (heven : z%2=0) :
    ∃ q r len T',
      z=(2*q+1)*2^r ∧ a=len+1+r ∧ q<2^len ∧ 0<r ∧
      run tm2 (48+12*r+12*b) (s1Config L n m a z b h) =
        some ⟨(3 : Fin 6),h,T'⟩ ∧
      T' = (s1Config L n m a (z-1) (b+1) h).tape := by
  obtain ⟨q,r,len,hfactor,ha,hq,hr,hrun⟩ :=
    s1Config_counted_decrement_even L n m a z b h hz hzlt heven
  let T' := (s1Config L n m a (z-1) (b+1) h).tape
  have hcfg : (⟨(3 : Fin 6),h,T'⟩ : Config) =
      s1Config L n m a (z-1) (b+1) h := by
    apply config_ext_by_fields
    · simp [s1Config_state]
    · simp [s1Config_head]
    · rfl
  refine ⟨q,r,len,T',hfactor,ha,hq,hr,?_ ,?_⟩
  · simpa [hcfg] using hrun
  · rfl

#print axioms s1Config_evenCounter_countedReturn_canonical
#print axioms s1Config_carryInput_match
#print axioms s1Config_carryRightOnes
#print axioms s1Config_counted_decrement_of_prefix
#print axioms s1Config_counted_decrement_of_shifted_prefix
#print axioms s1Config_counted_decrement_r1
#print axioms s1Config_counted_decrement_r2
#print axioms s1Config_counted_decrement_r3

end BB6Coverage.Agent24ChampionTime
