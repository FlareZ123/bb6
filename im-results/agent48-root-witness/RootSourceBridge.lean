import RootFiniteBits
import S1Encoder

namespace BB6Coverage.Agent42InitialS1Root

set_option maxRecDepth 10000
set_option maxHeartbeats 0

open BB6Coverage
open BB6Coverage.Agent48Champion
open BB6Coverage.Agent42InitialS1Bits
open BB6Coverage.Agent8S1Encoder

def rootS1Config : Config := s1Config 3 7 2 6 0 63 29

theorem rootS1_left_length : (s1LeftFacing 3 7 2 6 0).length = 40 := by decide
theorem rootS1_right_length : (s1PhysicalRight 63).length = 198 := by decide

theorem sideBit_false_of_length_le (xs : List Bool) (i : Nat)
    (hi : xs.length ≤ i) : sideBit xs i = false := by
  induction xs generalizing i with
  | nil => simp [sideBit]
  | cons a xs ih =>
    cases i with
    | zero => simp at hi
    | succ i =>
      simp only [sideBit]
      apply ih
      simp at hi
      omega

def rootBitCells : List Bool :=
  (List.range 238).map (fun i => Nat.testBit bFinal.tape i)

def rootSourceCells : List Bool :=
  (List.range 238).map (fun i : Nat => rootS1Config.tape ((i : Int)-10))

theorem rootCells_eq : rootBitCells = rootSourceCells := by decide

theorem rootCell_eq (i : Nat) (hi : i < 238) :
    Nat.testBit bFinal.tape i = rootS1Config.tape ((i:Int)-10) := by
  have h := congrArg (fun xs : List Bool => xs[i]?) rootCells_eq
  have hb : rootBitCells[i]? = some (Nat.testBit bFinal.tape i) := by
    simp [rootBitCells, hi]
  have hs : rootSourceCells[i]? = some (rootS1Config.tape ((i:Int)-10)) := by
    simp [rootSourceCells, hi]
  rw [hb, hs] at h
  exact Option.some.inj h

theorem rootSource_tape_false_left (x : Int) (hx : x < -10) :
    rootS1Config.tape x = false := by
  let i := Int.toNat (29-x)
  have hnonneg : 0 ≤ 29-x := by omega
  have hcast : ((i : Nat) : Int) = 29-x := by
    dsimp [i]
    exact Int.toNat_of_nonneg hnonneg
  have hcoord : 29-(i:Int) = x := by omega
  have hi : 40 ≤ i := by dsimp [i]; omega
  have hlen : (s1LeftFacing 3 7 2 6 0).length ≤ i := by
    rw [rootS1_left_length]
    exact hi
  have hbit := sideBit_false_of_length_le (s1LeftFacing 3 7 2 6 0) i hlen
  have hcell := s1Config_left_cell 3 7 2 6 0 63 29 i
  rw [hcoord] at hcell
  exact hcell.trans hbit

theorem rootSource_tape_false_right (x : Int) (hx : 227 < x) :
    rootS1Config.tape x = false := by
  let i := Int.toNat (x-30)
  have hnonneg : 0 ≤ x-30 := by omega
  have hcast : ((i : Nat) : Int) = x-30 := by
    dsimp [i]
    exact Int.toNat_of_nonneg hnonneg
  have hcoord : 29+1+(i:Int) = x := by omega
  have hi : 198 ≤ i := by dsimp [i]; omega
  have hlen : (s1PhysicalRight 63).length ≤ i := by
    rw [rootS1_right_length]
    exact hi
  have hbit := sideBit_false_of_length_le (s1PhysicalRight 63) i hlen
  have hcell := s1Config_right_cell 3 7 2 6 0 63 29 i
  rw [hcoord] at hcell
  exact hcell.trans hbit

theorem embedB_b0 : embedB b0 = blank := by
  simp [embedB, b0, blank]

theorem embedB_bFinal : embedB bFinal = rootS1Config := by
  change Config.mk (3 : Fin 6) 29
    (fun x => if -10 ≤ x then
      Nat.testBit bFinal.tape (Int.toNat (x+10)) else false) =
    Config.mk (3 : Fin 6) 29 rootS1Config.tape
  apply congrArg (fun f : Int → Bool => Config.mk (3 : Fin 6) 29 f)
  funext x
  by_cases hleft : x < -10
  · have hsrc := rootSource_tape_false_left x hleft
    have hnot : ¬ -10 ≤ x := by omega
    simp [hnot, hsrc]
  · by_cases hright : 227 < x
    · have hsrc := rootSource_tape_false_right x hright
      have hidx : 238 ≤ Int.toNat (x+10) := by omega
      have hlt238 : bFinal.tape < 2^238 := by decide
      have hpow : 2^238 ≤ 2^(Int.toNat (x+10)) :=
        Nat.pow_le_pow_right (by decide) hidx
      have hlt : bFinal.tape < 2^(Int.toNat (x+10)) :=
        Nat.lt_of_lt_of_le hlt238 hpow
      have hbit : Nat.testBit bFinal.tape (Int.toNat (x+10)) = false :=
        Nat.testBit_lt_two_pow hlt
      simp [hright, hsrc, hbit]
    · have hlo : -10 ≤ x := by omega
      let i := Int.toNat (x+10)
      have hi : i < 238 := by dsimp [i]; omega
      have hcast : (i:Int)-10=x := by
        dsimp [i]
        have hn : 0 ≤ x+10 := by omega
        have hv : ((Int.toNat (x+10):Nat):Int)=x+10 :=
          Int.toNat_of_nonneg hn
        omega
      have hcell := rootCell_eq i hi
      rw [hcast] at hcell
      simp [hlo, i, hcell]

theorem tm2_blank_reaches_initialS1_source :
    run tm2 27959 blank = some rootS1Config := by
  have h := bRun_sound tm2 27959 b0 bFinal tm2_blank_reaches_initialS1_bits
  rw [embedB_b0] at h
  rw [embedB_bFinal] at h
  exact h

#print axioms tm2_blank_reaches_initialS1_source

end BB6Coverage.Agent42InitialS1Root
