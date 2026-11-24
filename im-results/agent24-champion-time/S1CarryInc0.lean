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
      simp [carryInputBit] <;> omega
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
    apply config_ext_by_fields
    · simp [shiftConfig,c0,s1Config]
    · simp [shiftConfig,c0,s1Config]
    · funext x
      change T (x-h) = c0.tape x
      dsimp [T]
      rw [show h + (x-h) = x by omega]
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
  have h1' : Tpre (h+1) = true := by simpa [Tpre] using h1
  have h2' : Tpre (h+2) = true := by simpa [Tpre] using h2
  have h3' : Tpre (h+3) = true := by simpa [Tpre] using h3
  have h4' : Tpre (h+4) = true := by simpa [Tpre] using h4
  have h5' : Tpre (h+5) = false := by simpa [Tpre] using h5
  have h6' : Tpre (h+6) = true := by simpa [Tpre] using h6
  have hdec := s0Config_counted_decrement_of_prefix
    (markerWord m ++ d0 ++ binDec L n ++ lh)
    (len+1+r) ((2*q+1)*2^r) (((2*q+1)*2^r)-1) b r h Tpre
    hprefix0 h1' h2' h3' h4' h5' h6' hone hpreserve' hleft'
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
