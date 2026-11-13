import Rst1PrimeBridge9Source
import CountedQ4Prefix
import Lean.Elab.Tactic.Omega

/-!
# Source-level bridge 6 after the fourth counted sweep in Rst1'

This file continues the already source-connected chain through bridge9 and
the following (a+1)-block right sweep. It proves bridge6's local input
window from the original S1 source and composes the six-step bridge.
-/

namespace BB6Coverage.Agent8Rst1PrimeTail

open BB6Coverage
open BB6Coverage.Agent48Champion
open BB6Coverage.Agent8S1Encoder
open BB6Coverage.Agent24ChampionTime
open BB6Coverage.Agent8Rst1Prime
open BB6Coverage.Agent4Rst1Prime
open BB6Coverage.Agent6Q4Prefix

/-- After bridge9, every cell strictly to the right of the original
right-hand sentinel region is still the original S1 source cell. -/
theorem rst1PrimeAfterBridge9_eq_source_right
    (L a b : Nat) (h x : Int) (hx : h+1 < x) :
    (rst1PrimeAfterBridge9 L a b h).tape x =
      (s1Config L 0 1 a 0 b h).tape x := by
  let H0 : Int := h-((3*a+1:Int))
  let H1 : Int := H0-2
  let H2 : Int := H1-((3*L+5:Int))
  let H3 : Int := H2+4
  change
    (frameAt
      (sweptRight (L+1) (rst1PrimeAfterBridge20 L a b h).tape H3)
      H0 inside9 bridge9End).tape x =
      (s1Config L 0 1 a 0 b h).tape x
  have hrel9 : x-H0 = x-(h-((3*a+1:Int))) := by
    dsimp [H0]
  have hout9 : inside9 (x-H0) = false := by
    simp [inside9,inWindow,hrel9]
    dsimp [H0]
    omega
  rw [frameAt_tape]
  simp only [hout9]
  have hafter3 :
      sweptRight (L+1) (rst1PrimeAfterBridge20 L a b h).tape H3 x =
        (rst1PrimeAfterBridge20 L a b h).tape x := by
    apply rst1Prime_sweptRight_preserves_after
    dsimp [H0,H1,H2,H3]
    omega
  rw [hafter3]
  change
    (frameAt
      (sweptLeft (3*L+5) (rst1PrimeAfterBridge8 L a b h).tape H1)
      H2 inside20 bridge20End).tape x =
      (s1Config L 0 1 a 0 b h).tape x
  have hout20 : inside20 (x-H2) = false := by
    simp [inside20,inWindow]
    dsimp [H0,H1,H2]
    omega
  rw [frameAt_tape]
  simp only [hout20]
  have hleft2 :
      sweptLeft (3*L+5) (rst1PrimeAfterBridge8 L a b h).tape H1 x =
        (rst1PrimeAfterBridge8 L a b h).tape x := by
    apply sweptLeft_eq_of_gt
    dsimp [H0,H1]
    omega
  rw [hleft2]
  change
    (frameAt
      (sweptLeft (3*a+1) (s1Config L 0 1 a 0 b h).tape h)
      H0 inside8 bridge8End).tape x =
      (s1Config L 0 1 a 0 b h).tape x
  have hout8 : inside8 (x-H0) = false := by
    simp [inside8,inWindow]
    dsimp [H0]
    omega
  rw [frameAt_tape]
  simp only [hout8]
  apply sweptLeft_eq_of_gt
  exact hx

/-- Full configuration after the (a+1)-block right sweep following
bridge9. -/
def rst1PrimeAfterRightSweepA
    (L a b : Nat) (h : Int) : Config :=
  ⟨3,
    (h-((3*a+1:Int))+3)+3*((a+1):Int),
    sweptRight (a+1) (rst1PrimeAfterBridge9 L a b h).tape
      (h-((3*a+1:Int))+3)⟩

/-- Reuse Agent 4's exact original-source run through the fourth sweep. -/
theorem rst1Prime_rightSweep_after_bridge9_run_source
    (L a b : Nat) (h : Int) :
    run tm2
      (9*a+3+8+3*(3*L+5)+20+3*(L+1)+9+3*(a+1))
      (s1Config L 0 1 a 0 b h) =
      some (rst1PrimeAfterRightSweepA L a b h) := by
  simpa [rst1PrimeAfterRightSweepA] using
    rst1Prime_rightSweep_after_bridge9_run L a b h

/-- The fourth sweep's endpoint is h+5. -/
theorem rst1PrimeAfterRightSweepA_head
    (L a b : Nat) (h : Int) :
    (rst1PrimeAfterRightSweepA L a b h).head = h+5 := by
  simp [rst1PrimeAfterRightSweepA]
  omega

/-- Bridge6 sees its exact five-cell source window after the fourth
counted sweep. -/
theorem rst1Prime_bridge6_window_after_rightSweep
    (L a b : Nat) (h : Int) :
    ∀ x, inside6 x = true →
      (rst1PrimeAfterRightSweepA L a b h).tape
        (((h-((3*a+1:Int))+3)+3*((a+1):Int))+x) =
        decide (x ∈ bridge6Start.marked) := by
  let H0 : Int := h-((3*a+1:Int))
  let Hs : Int := H0+3
  let H6 : Int := Hs+3*((a+1):Int)
  intro x hx
  have hxw : -1 ≤ x ∧ x ≤ 3 := by
    simpa [inside6,inWindow] using hx
  have hcases : x=(-1:Int) ∨ x=0 ∨ x=1 ∨ x=2 ∨ x=3 := by omega
  change
    sweptRight (a+1) (rst1PrimeAfterBridge9 L a b h).tape Hs
      (H6+x) = decide (x ∈ bridge6Start.marked)
  rcases hcases with hneg | hzero | hone | htwo | hthree
  · subst x
    have hlast := rst1Prime_sweptRight_lastBlock a
      (rst1PrimeAfterBridge9 L a b h).tape Hs
    have hcoord : H6+(-1:Int) = Hs+3*(a:Int)+2 := by
      dsimp [H6,Hs,H0]
      omega
    rw [hcoord]
    simpa [bridge6Start] using hlast.2.2
  · subst x
    have hafter := rst1Prime_sweptRight_preserves_after
      (a+1) (rst1PrimeAfterBridge9 L a b h).tape Hs H6 (by
        dsimp [H6,Hs,H0]
        omega)
    rw [hafter]
    have hsource := rst1PrimeAfterBridge9_eq_source_right
      L a b h H6 (by dsimp [H6,Hs,H0]; omega)
    rw [hsource]
    have hcoord : H6 = h+5 := by dsimp [H6,Hs,H0]; omega
    rw [hcoord]
    have hcell := s1Config_right_cell L 0 1 a 0 b h 4
    simpa [bridge6Start,s1PhysicalRight,s0PhysicalRight,
      s0RightFacing,sideBit] using hcell
  · subst x
    have hafter := rst1Prime_sweptRight_preserves_after
      (a+1) (rst1PrimeAfterBridge9 L a b h).tape Hs (H6+1) (by
        dsimp [H6,Hs,H0]
        omega)
    rw [hafter]
    have hsource := rst1PrimeAfterBridge9_eq_source_right
      L a b h (H6+1) (by dsimp [H6,Hs,H0]; omega)
    rw [hsource]
    have hcoord : H6+1 = h+1+5 := by dsimp [H6,Hs,H0]; omega
    rw [hcoord]
    have hcell := s1Config_right_cell L 0 1 a 0 b h 5
    simpa [bridge6Start,s1PhysicalRight,s0PhysicalRight,
      s0RightFacing,sideBit] using hcell
  · subst x
    have hafter := rst1Prime_sweptRight_preserves_after
      (a+1) (rst1PrimeAfterBridge9 L a b h).tape Hs (H6+2) (by
        dsimp [H6,Hs,H0]
        omega)
    rw [hafter]
    have hsource := rst1PrimeAfterBridge9_eq_source_right
      L a b h (H6+2) (by dsimp [H6,Hs,H0]; omega)
    rw [hsource]
    have hcoord : H6+2 = h+1+6 := by dsimp [H6,Hs,H0]; omega
    rw [hcoord]
    have hcell := s1Config_right_cell L 0 1 a 0 b h 6
    simpa [bridge6Start,s1PhysicalRight,s0PhysicalRight,
      s0RightFacing,sideBit] using hcell
  · subst x
    have hafter := rst1Prime_sweptRight_preserves_after
      (a+1) (rst1PrimeAfterBridge9 L a b h).tape Hs (H6+3) (by
        dsimp [H6,Hs,H0]
        omega)
    rw [hafter]
    have hsource := rst1PrimeAfterBridge9_eq_source_right
      L a b h (H6+3) (by dsimp [H6,Hs,H0]; omega)
    rw [hsource]
    have hcoord : H6+3 = h+1+7 := by dsimp [H6,Hs,H0]; omega
    rw [hcoord]
    have hcell := s1Config_right_cell L 0 1 a 0 b h 7
    simpa [bridge6Start,s1PhysicalRight,s0PhysicalRight,
      s0RightFacing,sideBit] using hcell

/-- Full configuration after bridge6. -/
def rst1PrimeAfterBridge6
    (L a b : Nat) (h : Int) : Config :=
  frameAt (rst1PrimeAfterRightSweepA L a b h).tape
    ((h-((3*a+1:Int))+3)+3*((a+1):Int))
    inside6 bridge6End

/-- Compose the fourth sweep with the exact six-step bridge6. -/
theorem rst1Prime_bridge6_after_rightSweep
    (L a b : Nat) (h : Int) :
    run tm2
      (9*a+3+8+3*(3*L+5)+20+3*(L+1)+9+3*(a+1)+6)
      (s1Config L 0 1 a 0 b h) =
      some (rst1PrimeAfterBridge6 L a b h) := by
  rw [run_add,rst1Prime_rightSweep_after_bridge9_run_source]
  simp only [Option.bind_some]
  exact bridge6_at (rst1PrimeAfterRightSweepA L a b h).tape
    ((h-((3*a+1:Int))+3)+3*((a+1):Int))
    (rst1Prime_bridge6_window_after_rightSweep L a b h)

#print axioms rst1PrimeAfterBridge9_eq_source_right
#print axioms rst1Prime_rightSweep_after_bridge9_run_source
#print axioms rst1Prime_bridge6_window_after_rightSweep
#print axioms rst1Prime_bridge6_after_rightSweep

/-- Bridge6's output leaves the first three cells of the final right
counter as `1,0,0` at h+6,h+7,h+8. -/
theorem rst1PrimeAfterBridge6_local_right
    (L a b : Nat) (h : Int) :
    (rst1PrimeAfterBridge6 L a b h).tape (h+6) = true ∧
    (rst1PrimeAfterBridge6 L a b h).tape (h+7) = false ∧
    (rst1PrimeAfterBridge6 L a b h).tape (h+8) = false := by
  let H6 : Int := (h-((3*a+1:Int))+3)+3*((a+1):Int)
  have hH6 : H6 = h+5 := by
    dsimp [H6]
    omega
  constructor
  · change (frameAt (rst1PrimeAfterRightSweepA L a b h).tape H6
      inside6 bridge6End).tape (h+6) = true
    rw [hH6]
    rw [frameAt_tape]
    simp [inside6,inWindow,bridge6End]
  constructor
  · change (frameAt (rst1PrimeAfterRightSweepA L a b h).tape H6
      inside6 bridge6End).tape (h+7) = false
    rw [hH6]
    rw [frameAt_tape]
    simp [inside6,inWindow,bridge6End]
  · change (frameAt (rst1PrimeAfterRightSweepA L a b h).tape H6
      inside6 bridge6End).tape (h+8) = false
    rw [hH6]
    rw [frameAt_tape]
    simp [inside6,inWindow,bridge6End]

/-- Beyond bridge6's window and the fourth sweep's endpoint, the tape
again agrees with the original S1 right-facing source. -/
theorem rst1PrimeAfterBridge6_eq_source_right
    (L a b : Nat) (h x : Int) (hx : h+9 ≤ x) :
    (rst1PrimeAfterBridge6 L a b h).tape x =
      (s1Config L 0 1 a 0 b h).tape x := by
  let Hs : Int := h-((3*a+1:Int))+3
  let H6 : Int := Hs+3*((a+1):Int)
  change
    (frameAt
      (sweptRight (a+1) (rst1PrimeAfterBridge9 L a b h).tape Hs)
      H6 inside6 bridge6End).tape x =
      (s1Config L 0 1 a 0 b h).tape x
  have hout6 : inside6 (x-H6) = false := by
    simp [inside6,inWindow]
    dsimp [Hs,H6]
    omega
  rw [frameAt_tape]
  simp only [hout6]
  have hafterA :
      sweptRight (a+1) (rst1PrimeAfterBridge9 L a b h).tape Hs x =
        (rst1PrimeAfterBridge9 L a b h).tape x := by
    apply rst1Prime_sweptRight_preserves_after
    dsimp [Hs,H6]
    omega
  rw [hafterA]
  exact rst1PrimeAfterBridge9_eq_source_right L a b h x (by omega)

/-- The S0 right-facing suffix has ones exactly on its d1-power tail. -/
theorem rst1Prime_s0RightFacing_tail_true
    (b i : Nat) (hi : 6 ≤ i) (hend : i < 3*b+9) :
    sideBit (s0RightFacing b) i = true := by
  change sideBit ([false,true,true,true,false,false] ++ d1pow (b+1)) i = true
  rw [sideBit_append_right _ _ _ (by simp; omega)]
  have hidx : i-6 < 3*(b+1) := by omega
  exact sideBit_d1pow_true (b+1) (i-6) hidx

/-- Cells beyond the complete S0 right-facing source word are blank. -/
theorem rst1Prime_s0RightFacing_tail_false
    (b i : Nat) (hi : 3*b+9 ≤ i) :
    sideBit (s0RightFacing b) i = false := by
  change sideBit ([false,true,true,true,false,false] ++ d1pow (b+1)) i = false
  apply sideBit_ge_length
  simp [d1pow_length]
  omega

/-- The post-bridge6 tape has the original source bit at every position
in the final d1-power suffix. -/
theorem rst1PrimeAfterBridge6_source_bit_true
    (L a b : Nat) (h : Int) (i : Nat)
    (hi : 8 ≤ i) (hend : i < 3*b+9) :
    (rst1PrimeAfterBridge6 L a b h).tape (h+1+(i:Int)) = true := by
  have heq := rst1PrimeAfterBridge6_eq_source_right L a b h
    (h+1+(i:Int)) (by omega)
  rw [heq]
  have hcell := s1Config_right_cell L 0 1 a 0 b h i
  rw [hcell]
  simpa [s1PhysicalRight,s0PhysicalRight] using
    rst1Prime_s0RightFacing_tail_true b i (by omega) hend

/-- The post-bridge6 tape is blank beyond the original S0 right-facing
source word. -/
theorem rst1PrimeAfterBridge6_source_bit_false
    (L a b : Nat) (h : Int) (i : Nat)
    (hi : 3*b+9 ≤ i) :
    (rst1PrimeAfterBridge6 L a b h).tape (h+1+(i:Int)) = false := by
  have heq := rst1PrimeAfterBridge6_eq_source_right L a b h
    (h+1+(i:Int)) (by omega)
  rw [heq]
  have hcell := s1Config_right_cell L 0 1 a 0 b h i
  rw [hcell]
  simpa [s1PhysicalRight,s0PhysicalRight] using
    rst1Prime_s0RightFacing_tail_false b i hi

/-- The final b three-one blocks are still present after bridge6. -/
theorem rst1Prime_rightSweep_preconditions_after_bridge6
    (L a b : Nat) (h : Int) :
    rightOnes (rst1PrimeAfterBridge6 L a b h).tape (h+9) b := by
  intro i hi
  have h0 := rst1PrimeAfterBridge6_source_bit_true L a b h
    (8+3*i) (by omega) (by omega)
  have h1 := rst1PrimeAfterBridge6_source_bit_true L a b h
    (9+3*i) (by omega) (by omega)
  have h2 := rst1PrimeAfterBridge6_source_bit_true L a b h
    (10+3*i) (by omega) (by omega)
  have e0 : h+9+3*(i:Int) = h+1+((8+3*i:Int)) := by omega
  have e1 : h+9+3*(i:Int)+1 = h+1+((9+3*i:Int)) := by omega
  have e2 : h+9+3*(i:Int)+2 = h+1+((10+3*i:Int)) := by omega
  rw [e0,e1,e2]
  exact ⟨h0,h1,h2⟩

/-- Full configuration after draining the final b right-counter blocks. -/
def rst1PrimeAfterRightSweepB
    (L a b : Nat) (h : Int) : Config :=
  ⟨3,(h+9)+3*(b:Int),
    sweptRight b (rst1PrimeAfterBridge6 L a b h).tape (h+9)⟩

/-- Compose the final b-block right sweep with the source-connected
bridge6 prefix. -/
theorem rst1Prime_rightSweep_after_bridge6_run
    (L a b : Nat) (h : Int) :
    run tm2
      (9*a+3+8+3*(3*L+5)+20+3*(L+1)+9+3*(a+1)+6+3*b)
      (s1Config L 0 1 a 0 b h) =
      some (rst1PrimeAfterRightSweepB L a b h) := by
  rw [run_add,rst1Prime_bridge6_after_rightSweep]
  simp only [Option.bind_some]
  have hhead :
      ((h-((3*a+1:Int))+3)+3*((a+1):Int))+bridge6End.head = h+9 := by
    simp [bridge6End]
    omega
  simpa [rst1PrimeAfterBridge6,frameAt,bridge6End,hhead] using
    counted_right_sweep b (rst1PrimeAfterBridge6 L a b h).tape (h+9)
      (rst1Prime_rightSweep_preconditions_after_bridge6 L a b h)

/-- The bridge30 input window after the final right sweep has marked
offsets exactly -3 and 0. -/
theorem rst1Prime_bridge30_window_after_finalRightSweep
    (L a b : Nat) (h : Int) :
    ∀ x, inside30 x = true →
      (rst1PrimeAfterRightSweepB L a b h).tape
        (h+9+3*(b:Int)+x) =
        decide (x ∈ bridge30Start.marked) := by
  intro x hx
  have hxw : -3 ≤ x ∧ x ≤ 5 := by
    simpa [inside30,inWindow] using hx
  have hcases :
      x=(-3:Int) ∨ x=(-2:Int) ∨ x=(-1:Int) ∨ x=0 ∨
      x=1 ∨ x=2 ∨ x=3 ∨ x=4 ∨ x=5 := by omega
  change
    sweptRight b (rst1PrimeAfterBridge6 L a b h).tape (h+9)
      (h+9+3*(b:Int)+x) =
      decide (x ∈ bridge30Start.marked)
  rcases hcases with hneg3 | hneg2 | hneg1 | hzero | hone | htwo |
      hthree | hfour | hfive
  · subst x
    by_cases hb : b=0
    · subst b
      have hcell := (rst1PrimeAfterBridge6_local_right L a 0 h).1
      have hcoord : h+9+3*(0:Int)+(-3:Int) = h+6 := by omega
      rw [hcoord]
      simpa [bridge30Start,sweptRight] using hcell
    · obtain ⟨n,rfl⟩ := Nat.exists_eq_succ_of_ne_zero hb
      have hpre := rst1Prime_rightSweep_preconditions_after_bridge6 L a (n+1) h
      have hfirst := (hpre n (by omega)).1
      have hlast := rst1Prime_sweptRight_lastBlock n
        (rst1PrimeAfterBridge6 L a (n+1) h).tape (h+9)
      have hcoord :
          h+9+3*((n+1):Int)+(-3:Int) = h+9+3*(n:Int) := by omega
      rw [hcoord,hlast.1,hfirst]
      simp [bridge30Start]
  · subst x
    by_cases hb : b=0
    · subst b
      have hcell := (rst1PrimeAfterBridge6_local_right L a 0 h).2.1
      have hcoord : h+9+3*(0:Int)+(-2:Int) = h+7 := by omega
      rw [hcoord]
      simpa [bridge30Start,sweptRight] using hcell
    · obtain ⟨n,rfl⟩ := Nat.exists_eq_succ_of_ne_zero hb
      have hlast := rst1Prime_sweptRight_lastBlock n
        (rst1PrimeAfterBridge6 L a (n+1) h).tape (h+9)
      have hcoord :
          h+9+3*((n+1):Int)+(-2:Int) = h+9+3*(n:Int)+1 := by omega
      rw [hcoord]
      simpa [bridge30Start] using hlast.2.1
  · subst x
    by_cases hb : b=0
    · subst b
      have hcell := (rst1PrimeAfterBridge6_local_right L a 0 h).2.2
      have hcoord : h+9+3*(0:Int)+(-1:Int) = h+8 := by omega
      rw [hcoord]
      simpa [bridge30Start,sweptRight] using hcell
    · obtain ⟨n,rfl⟩ := Nat.exists_eq_succ_of_ne_zero hb
      have hlast := rst1Prime_sweptRight_lastBlock n
        (rst1PrimeAfterBridge6 L a (n+1) h).tape (h+9)
      have hcoord :
          h+9+3*((n+1):Int)+(-1:Int) = h+9+3*(n:Int)+2 := by omega
      rw [hcoord]
      simpa [bridge30Start] using hlast.2.2
  · subst x
    have hafter := rst1Prime_sweptRight_preserves_after
      b (rst1PrimeAfterBridge6 L a b h).tape (h+9) (h+9+3*(b:Int)) (by omega)
    rw [hafter]
    have hsource := rst1PrimeAfterBridge6_source_bit_true L a b h
      (8+3*b) (by omega) (by omega)
    have hcoord : h+9+3*(b:Int) = h+1+((8+3*b:Int)) := by omega
    rw [hcoord]
    simpa [bridge30Start] using hsource
  · subst x
    have hafter := rst1Prime_sweptRight_preserves_after
      b (rst1PrimeAfterBridge6 L a b h).tape (h+9)
      (h+9+3*(b:Int)+1) (by omega)
    rw [hafter]
    have hsource := rst1PrimeAfterBridge6_source_bit_false L a b h
      (9+3*b) (by omega)
    have hcoord : h+9+3*(b:Int)+1 = h+1+((9+3*b:Int)) := by omega
    rw [hcoord]
    simpa [bridge30Start] using hsource
  · subst x
    have hafter := rst1Prime_sweptRight_preserves_after
      b (rst1PrimeAfterBridge6 L a b h).tape (h+9)
      (h+9+3*(b:Int)+2) (by omega)
    rw [hafter]
    have hsource := rst1PrimeAfterBridge6_source_bit_false L a b h
      (10+3*b) (by omega)
    have hcoord : h+9+3*(b:Int)+2 = h+1+((10+3*b:Int)) := by omega
    rw [hcoord]
    simpa [bridge30Start] using hsource
  · subst x
    have hafter := rst1Prime_sweptRight_preserves_after
      b (rst1PrimeAfterBridge6 L a b h).tape (h+9)
      (h+9+3*(b:Int)+3) (by omega)
    rw [hafter]
    have hsource := rst1PrimeAfterBridge6_source_bit_false L a b h
      (11+3*b) (by omega)
    have hcoord : h+9+3*(b:Int)+3 = h+1+((11+3*b:Int)) := by omega
    rw [hcoord]
    simpa [bridge30Start] using hsource
  · subst x
    have hafter := rst1Prime_sweptRight_preserves_after
      b (rst1PrimeAfterBridge6 L a b h).tape (h+9)
      (h+9+3*(b:Int)+4) (by omega)
    rw [hafter]
    have hsource := rst1PrimeAfterBridge6_source_bit_false L a b h
      (12+3*b) (by omega)
    have hcoord : h+9+3*(b:Int)+4 = h+1+((12+3*b:Int)) := by omega
    rw [hcoord]
    simpa [bridge30Start] using hsource
  · subst x
    have hafter := rst1Prime_sweptRight_preserves_after
      b (rst1PrimeAfterBridge6 L a b h).tape (h+9)
      (h+9+3*(b:Int)+5) (by omega)
    rw [hafter]
    have hsource := rst1PrimeAfterBridge6_source_bit_false L a b h
      (13+3*b) (by omega)
    have hcoord : h+9+3*(b:Int)+5 = h+1+((13+3*b:Int)) := by omega
    rw [hcoord]
    simpa [bridge30Start] using hsource

/-- Full configuration after the final 30-step bridge. -/
def rst1PrimeAfterBridge30
    (L a b : Nat) (h : Int) : Config :=
  frameAt (rst1PrimeAfterRightSweepB L a b h).tape
    (h+9+3*(b:Int)) inside30 bridge30End

/-- Compose the final b-block sweep with the exact bridge30. -/
theorem rst1Prime_bridge30_after_finalRightSweep
    (L a b : Nat) (h : Int) :
    run tm2
      (9*a+3+8+3*(3*L+5)+20+3*(L+1)+9+3*(a+1)+6+3*b+30)
      (s1Config L 0 1 a 0 b h) =
      some (rst1PrimeAfterBridge30 L a b h) := by
  rw [run_add,rst1Prime_rightSweep_after_bridge6_run]
  simp only [Option.bind_some]
  exact bridge30_at (rst1PrimeAfterRightSweepB L a b h).tape
    (h+9+3*(b:Int))
    (rst1Prime_bridge30_window_after_finalRightSweep L a b h)

#print axioms rst1PrimeAfterBridge6_eq_source_right
#print axioms rst1Prime_rightSweep_preconditions_after_bridge6
#print axioms rst1Prime_rightSweep_after_bridge6_run
#print axioms rst1Prime_bridge30_window_after_finalRightSweep
#print axioms rst1Prime_bridge30_after_finalRightSweep


/-- The final bridge leaves the canonical S1 head position. -/
theorem rst1PrimeAfterBridge30_head
    (L a b : Nat) (h : Int) :
    (rst1PrimeAfterBridge30 L a b h).head = h+5+3*(b:Int) := by
  simp [rst1PrimeAfterBridge30,frameAt_head,bridge30End]
  omega

/-- The complete right-facing output word after bridge30 is exactly
the S1 separator followed by one d1 block. -/
theorem rst1PrimeAfterBridge30_rightFacing
    (L a b : Nat) (h : Int) :
    ∀ i : Nat,
      (rst1PrimeAfterBridge30 L a b h).tape
        (h+5+3*(b:Int)+1+(i:Int)) =
      sideBit (s0RightFacing 0) i := by
  intro i
  let H7 : Int := h+9
  let H8 : Int := H7+3*(b:Int)
  let Hf : Int := H8-4
  change (frameAt
    (sweptRight b (rst1PrimeAfterBridge6 L a b h).tape H7)
    H8 inside30 bridge30End).tape (Hf+1+(i:Int)) =
      sideBit (s0RightFacing 0) i
  by_cases hi : i<9
  · have hcases :
      i=0 ∨ i=1 ∨ i=2 ∨ i=3 ∨ i=4 ∨ i=5 ∨ i=6 ∨ i=7 ∨ i=8 := by omega
    rcases hcases with hi0 | hi1 | hi2 | hi3 | hi4 | hi5 | hi6 | hi7 | hi8
    · subst i
      have hcoord : Hf+1+(0:Int) = H8+(-3:Int) := by
        dsimp [Hf,H8,H7]
        omega
      rw [frameAt_tape,hcoord]
      simp [inside30,inWindow,bridge30End,s0RightFacing,d1pow,sideBit]
    · subst i
      have hcoord : Hf+1+(1:Int) = H8+(-2:Int) := by
        dsimp [Hf,H8,H7]
        omega
      rw [frameAt_tape,hcoord]
      simp [inside30,inWindow,bridge30End,s0RightFacing,d1pow,sideBit]
    · subst i
      have hcoord : Hf+1+(2:Int) = H8+(-1:Int) := by
        dsimp [Hf,H8,H7]
        omega
      rw [frameAt_tape,hcoord]
      simp [inside30,inWindow,bridge30End,s0RightFacing,d1pow,sideBit]
    · subst i
      have hcoord : Hf+1+(3:Int) = H8+(0:Int) := by
        dsimp [Hf,H8,H7]
        omega
      rw [frameAt_tape,hcoord]
      simp [inside30,inWindow,bridge30End,s0RightFacing,d1pow,sideBit]
    · subst i
      have hcoord : Hf+1+(4:Int) = H8+1 := by
        dsimp [Hf,H8,H7]
        omega
      rw [frameAt_tape,hcoord]
      simp [inside30,inWindow,bridge30End,s0RightFacing,d1pow,sideBit]
    · subst i
      have hcoord : Hf+1+(5:Int) = H8+2 := by
        dsimp [Hf,H8,H7]
        omega
      rw [frameAt_tape,hcoord]
      simp [inside30,inWindow,bridge30End,s0RightFacing,d1pow,sideBit]
    · subst i
      have hcoord : Hf+1+(6:Int) = H8+3 := by
        dsimp [Hf,H8,H7]
        omega
      rw [frameAt_tape,hcoord]
      simp [inside30,inWindow,bridge30End,s0RightFacing,d1pow,sideBit]
    · subst i
      have hcoord : Hf+1+(7:Int) = H8+4 := by
        dsimp [Hf,H8,H7]
        omega
      rw [frameAt_tape,hcoord]
      simp [inside30,inWindow,bridge30End,s0RightFacing,d1pow,sideBit]
    · subst i
      have hcoord : Hf+1+(8:Int) = H8+5 := by
        dsimp [Hf,H8,H7]
        omega
      rw [frameAt_tape,hcoord]
      simp [inside30,inWindow,bridge30End,s0RightFacing,d1pow,sideBit]
  · have hcoord :
      Hf+1+(i:Int) = H8 + ((i:Int)-3) := by
        dsimp [Hf]
        omega
    have hout : inside30 ((i:Int)-3) = false := by
      simp [inside30,inWindow]
      omega
    rw [frameAt_tape,hcoord]
    simp only [hout]
    have hafter := rst1Prime_sweptRight_preserves_after
      b (rst1PrimeAfterBridge6 L a b h).tape H7
      (H8+((i:Int)-3)) (by dsimp [H7,H8]; omega)
    rw [hafter]
    have hsource := rst1PrimeAfterBridge6_source_bit_false L a b h
      (5+3*b+i) (by omega)
    have hsourceCoord :
      H8+((i:Int)-3) = h+1+((5+3*b+i:Int)) := by
        dsimp [H7,H8]
        omega
    rw [hsourceCoord]
    simpa [s0RightFacing,d1pow,sideBit] using hsource

#print axioms rst1PrimeAfterBridge30_head
#print axioms rst1PrimeAfterBridge30_rightFacing


/-- All cells at and to the left of the bridge20 window are preserved
through bridge9, the fourth sweep, bridge6, the final sweep, and bridge30. -/
theorem rst1PrimeAfterBridge30_eq_afterBridge20_left
    (L a b : Nat) (h x : Int)
    (hx : x ≤ h-((3*a+1:Int))-2-((3*L+5:Int))+3) :
    (rst1PrimeAfterBridge30 L a b h).tape x =
      (rst1PrimeAfterBridge20 L a b h).tape x := by
  let H0 : Int := h-((3*a+1:Int))
  let H1 : Int := H0-2
  let H2 : Int := H1-((3*L+5:Int))
  let H3 : Int := H2+4
  let Hs : Int := H0+3
  let H6 : Int := Hs+3*((a+1):Int)
  let H8 : Int := h+9+3*(b:Int)
  change
    (frameAt
      (sweptRight b (rst1PrimeAfterBridge6 L a b h).tape (h+9))
      H8 inside30 bridge30End).tape x =
      (rst1PrimeAfterBridge20 L a b h).tape x
  have hout30 : inside30 (x-H8) = false := by
    simp [inside30,inWindow]
    dsimp [H0,H1,H2,H3,Hs,H6,H8]
    omega
  rw [frameAt_tape]
  simp only [hout30]
  have hleftB :
      sweptRight b (rst1PrimeAfterBridge6 L a b h).tape (h+9) x =
        (rst1PrimeAfterBridge6 L a b h).tape x := by
    apply rst1Prime_sweptRight_preserves_left
    dsimp [H0,H1,H2,H3,Hs,H6,H8]
    omega
  rw [hleftB]
  change
    (frameAt
      (sweptRight (a+1) (rst1PrimeAfterBridge9 L a b h).tape Hs)
      H6 inside6 bridge6End).tape x =
      (rst1PrimeAfterBridge20 L a b h).tape x
  have hout6 : inside6 (x-H6) = false := by
    simp [inside6,inWindow]
    dsimp [H0,H1,H2,H3,Hs,H6,H8]
    omega
  rw [frameAt_tape]
  simp only [hout6]
  have hleftA :
      sweptRight (a+1) (rst1PrimeAfterBridge9 L a b h).tape Hs x =
        (rst1PrimeAfterBridge9 L a b h).tape x := by
    apply rst1Prime_sweptRight_preserves_left
    dsimp [H0,H1,H2,H3,Hs,H6,H8]
    omega
  rw [hleftA]
  change
    (frameAt
      (sweptRight (L+1) (rst1PrimeAfterBridge20 L a b h).tape H3)
      H0 inside9 bridge9End).tape x =
      (rst1PrimeAfterBridge20 L a b h).tape x
  have hout9 : inside9 (x-H0) = false := by
    simp [inside9,inWindow]
    dsimp [H0,H1,H2,H3,Hs,H6,H8]
    omega
  rw [frameAt_tape]
  simp only [hout9]
  apply rst1Prime_sweptRight_preserves_left
  dsimp [H0,H1,H2,H3,Hs,H6,H8]
  omega

/-- The six-cell left-hand source tail supplied by bridge20 survives
unchanged through the entire Rst1' suffix. -/
theorem rst1PrimeAfterBridge30_left_tail
    (L a b : Nat) (h : Int) (i : Nat) (hi : i<6) :
    (rst1PrimeAfterBridge30 L a b h).tape
      (h-((3*a+1:Int))-2-((3*L+5:Int))-(i:Int)) =
      sideBit lh i := by
  let H2 : Int := h-((3*a+1:Int))-2-((3*L+5:Int))
  have heq := rst1PrimeAfterBridge30_eq_afterBridge20_left
    L a b h (H2-(i:Int)) (by dsimp [H2]; omega)
  rw [heq]
  simpa [H2] using rst1PrimeAfterBridge20_left_cell L a b h i hi

/-- The tape is blank strictly beyond the six-cell left source tail. -/
theorem rst1PrimeAfterBridge30_left_blank
    (L a b : Nat) (h x : Int)
    (hx : x ≤ h-((3*a+1:Int))-2-((3*L+5:Int))-6) :
    (rst1PrimeAfterBridge30 L a b h).tape x = false := by
  have heq := rst1PrimeAfterBridge30_eq_afterBridge20_left L a b h x (by omega)
  rw [heq]
  exact rst1PrimeAfterBridge20_left_blank L a b h x (by omega)

#print axioms rst1PrimeAfterBridge30_eq_afterBridge20_left
#print axioms rst1PrimeAfterBridge30_left_tail
#print axioms rst1PrimeAfterBridge30_left_blank


/-- The final bridge is inactive on every cell at or to the left of
the final head. -/
theorem rst1PrimeAfterBridge30_eq_afterRightSweepB_left
    (L a b : Nat) (h x : Int)
    (hx : x ≤ h+5+3*(b:Int)) :
    (rst1PrimeAfterBridge30 L a b h).tape x =
      (rst1PrimeAfterRightSweepB L a b h).tape x := by
  change (frameAt (rst1PrimeAfterRightSweepB L a b h).tape
    (h+9+3*(b:Int)) inside30 bridge30End).tape x =
      (rst1PrimeAfterRightSweepB L a b h).tape x
  have hout : inside30 (x-(h+9+3*(b:Int))) = false := by
    simp [inside30,inWindow]
    omega
  rw [frameAt_tape]
  simp [hout]

/-- On the region through h+5, bridge30 and the final b-sweep leave
the bridge6 output unchanged. -/
theorem rst1PrimeAfterBridge30_eq_afterBridge6_left
    (L a b : Nat) (h x : Int) (hx : x ≤ h+5) :
    (rst1PrimeAfterBridge30 L a b h).tape x =
      (rst1PrimeAfterBridge6 L a b h).tape x := by
  rw [rst1PrimeAfterBridge30_eq_afterRightSweepB_left L a b h x (by omega)]
  change sweptRight b (rst1PrimeAfterBridge6 L a b h).tape (h+9) x =
    (rst1PrimeAfterBridge6 L a b h).tape x
  apply rst1Prime_sweptRight_preserves_left
  omega

/-- On the region through h+1, the later bridge6/final-sweep/bridge30
stages leave the fourth-sweep output unchanged. -/
theorem rst1PrimeAfterBridge30_eq_afterRightSweepA_left
    (L a b : Nat) (h x : Int) (hx : x ≤ h+1) :
    (rst1PrimeAfterBridge30 L a b h).tape x =
      (rst1PrimeAfterRightSweepA L a b h).tape x := by
  rw [rst1PrimeAfterBridge30_eq_afterBridge6_left L a b h x (by omega)]
  change (frameAt (rst1PrimeAfterRightSweepA L a b h).tape
    ((h-((3*a+1:Int))+3)+3*((a+1):Int))
    inside6 bridge6End).tape x =
      (rst1PrimeAfterRightSweepA L a b h).tape x
  have hout : inside6
      (x-((h-((3*a+1:Int))+3)+3*((a+1):Int))) = false := by
    simp [inside6,inWindow]
    omega
  rw [frameAt_tape]
  simp [hout]

/-- On the region through H0-4, the final tape is exactly the output of
the third right sweep after bridge20. -/
theorem rst1PrimeAfterBridge30_eq_afterThirdRightSweep_left
    (L a b : Nat) (h x : Int)
    (hx : x ≤ h-((3*a+1:Int))-4) :
    (rst1PrimeAfterBridge30 L a b h).tape x =
      sweptRight (L+1) (rst1PrimeAfterBridge20 L a b h).tape
        (((h-((3*a+1:Int))-2)-((3*L+5:Int)))+4) x := by
  let H0 : Int := h-((3*a+1:Int))
  let H2 : Int := H0-2-((3*L+5:Int))
  let H3 : Int := H2+4
  let Hs : Int := H0+3
  let H6 : Int := Hs+3*((a+1):Int)
  let H8 : Int := h+9+3*(b:Int)
  change
    (frameAt
      (sweptRight b (rst1PrimeAfterBridge6 L a b h).tape (h+9))
      H8 inside30 bridge30End).tape x =
      sweptRight (L+1) (rst1PrimeAfterBridge20 L a b h).tape H3 x
  have hout30 : inside30 (x-H8) = false := by
    simp [inside30,inWindow]
    dsimp [H0,H2,H3,Hs,H6,H8]
    omega
  rw [frameAt_tape]
  simp only [hout30]
  have hleftB :
      sweptRight b (rst1PrimeAfterBridge6 L a b h).tape (h+9) x =
        (rst1PrimeAfterBridge6 L a b h).tape x := by
    apply rst1Prime_sweptRight_preserves_left
    dsimp [H0,H2,H3,Hs,H6,H8]
    omega
  rw [hleftB]
  change
    (frameAt
      (sweptRight (a+1) (rst1PrimeAfterBridge9 L a b h).tape Hs)
      H6 inside6 bridge6End).tape x =
      sweptRight (L+1) (rst1PrimeAfterBridge20 L a b h).tape H3 x
  have hout6 : inside6 (x-H6) = false := by
    simp [inside6,inWindow]
    dsimp [H0,H2,H3,Hs,H6,H8]
    omega
  rw [frameAt_tape]
  simp only [hout6]
  have hleftA :
      sweptRight (a+1) (rst1PrimeAfterBridge9 L a b h).tape Hs x =
        (rst1PrimeAfterBridge9 L a b h).tape x := by
    apply rst1Prime_sweptRight_preserves_left
    dsimp [H0,H2,H3,Hs,H6,H8]
    omega
  rw [hleftA]
  change
    (frameAt
      (sweptRight (L+1) (rst1PrimeAfterBridge20 L a b h).tape H3)
      H0 inside9 bridge9End).tape x =
      sweptRight (L+1) (rst1PrimeAfterBridge20 L a b h).tape H3 x
  have hout9 : inside9 (x-H0) = false := by
    simp [inside9,inWindow]
    dsimp [H0,H2,H3,Hs,H6,H8]
    omega
  rw [frameAt_tape]
  simp [hout9]

/-- The later source-connected stages preserve the third-sweep region
to the left of bridge9. -/
theorem rst1PrimeAfterBridge30_eq_afterBridge9_left
    (L a b : Nat) (h x : Int)
    (hx : x ≤ h-((3*a+1:Int))+2) :
    (rst1PrimeAfterBridge30 L a b h).tape x =
      (rst1PrimeAfterBridge9 L a b h).tape x := by
  rw [rst1PrimeAfterBridge30_eq_afterRightSweepA_left L a b h x (by omega)]
  change (rst1PrimeAfterRightSweepA L a b h).tape x =
    (rst1PrimeAfterBridge9 L a b h).tape x
  unfold rst1PrimeAfterRightSweepA
  apply rst1Prime_sweptRight_preserves_left
  omega

#print axioms rst1PrimeAfterBridge30_eq_afterRightSweepB_left
#print axioms rst1PrimeAfterBridge30_eq_afterBridge6_left
#print axioms rst1PrimeAfterBridge30_eq_afterRightSweepA_left
#print axioms rst1PrimeAfterBridge30_eq_afterThirdRightSweep_left
#print axioms rst1PrimeAfterBridge30_eq_afterBridge9_left


end BB6Coverage.Agent8Rst1PrimeTail
