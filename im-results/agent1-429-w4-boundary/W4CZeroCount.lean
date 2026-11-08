import W4CZeroSafe
import W4JuncOne
import Lean.Elab.Tactic.Omega

set_option maxRecDepth 8192
set_option maxHeartbeats 30000000

namespace BB429W4CZeroCount

open BB429OddExcursion BB429SourceE1Return BB429W4CZeroSafe
open BB429FinishScanEDelta BB429JuncHeadExcursion BB429W4JuncOne

/-- Count every state-C, read-zero configuration at instruction start.
    The final configuration at time n is excluded from the count. -/
def runCount : Nat → Zipper → Option (Zipper × Nat)
 | 0,c => some (c,0)
 | n+1,c => (one c).bind (fun c' =>
     (runCount n c').map (fun p =>
       (p.1,p.2+(if c.state == 2 && !c.current then 1 else 0))))

theorem runCount_add (m n : Nat) (c : Zipper) :
    runCount (m+n) c = (runCount m c).bind (fun p =>
      (runCount n p.1).map (fun q => (q.1,p.2+q.2))) := by
  induction m generalizing c with
  | zero => simp [runCount]
  | succ m ih =>
      simp only [Nat.succ_add,runCount]
      cases h : one c with
      | none => simp [h]
      | some p =>
          simp only [h,Option.bind_some]
          rw [ih]
          cases hm : runCount m p with
          | none => simp [hm]
          | some a =>
              simp only [hm,Option.bind_some]
              cases hn : runCount n a.1 with
              | none => simp [hn]
              | some b =>
                  simp only [hn,Option.bind_some,Option.map_some,
                    Option.some.injEq,Prod.mk.injEq]
                  constructor
                  · trivial
                  · omega

/-- A successful execution with the C/0 guard emits no C/0 instruction.
    This is the semantic bridge between safe execution and exact counting. -/
theorem runSafe_to_count_zero (n : Nat) (c d : Zipper)
    (h : runSafe n c = some d) : runCount n c = some (d,0) := by
  induction n generalizing c with
  | zero => simpa [runSafe,runCount] using h
  | succ n ih =>
      simp only [runSafe] at h
      cases hs : oneSafe c with
      | none => simp [hs] at h
      | some p =>
          simp only [hs,Option.bind_some] at h
          have hone : one c = some p := by
            unfold oneSafe at hs
            split at hs
            · simp at hs
            · exact hs
          have hgood : (c.state == 2 && !c.current) = false := by
            cases hbad : (c.state == 2 && !c.current) with
            | false => rfl
            | true => simp [oneSafe,hbad] at hs
          simp only [runCount,hone,Option.bind_some]
          rw [ih p h]
          simp [hgood]

private theorem pairs01_rightstep (n : Nat) :
    pairs01 (n+1) = pairs01 n ++ [false,true] := by
  induction n with
  | zero => rfl
  | succ n ih =>
      change false::true::pairs01 (n+1) =
        (false::true::pairs01 n) ++ [false,true]
      rw [ih]
      rfl

theorem junc0_prep20_count (v : Nat) :
    runCount 20 (junc 0 v 1) =
      some (z 1 (ones 5) false
        (true :: (pairs01 (v+2) ++ ones 1 ++ [false,true])), 0) := by
  rfl

theorem shift_B01_pair_count (left suffix : List Bool) :
    runCount 2 (z 1 left false (true::true::suffix)) =
      some (z 1 (false::true::left) true suffix, 0) := by rfl

theorem shift_B01_count (v : Nat) (left suffix : List Bool) :
    runCount (2*(v+1))
        (z 1 left false (true :: (pairs01 v ++ (true :: suffix)))) =
      some (z 1 (pairs01 (v+1) ++ left) true suffix, 0) := by
  induction v generalizing left suffix with
  | zero => simpa [pairs01] using shift_B01_pair_count left suffix
  | succ v ih =>
      have hpair : runCount 2
          (z 1 left false (true :: (pairs01 (v+1) ++ (true :: suffix)))) =
        some (z 1 (false::true::left) false
          (true :: (pairs01 v ++ (true :: suffix))), 0) := by rfl
      rw [show 2*(v+2) = 2+2*(v+1) by omega,runCount_add,hpair]
      simp only [Option.bind_some]
      rw [ih (false::true::left) suffix]
      simp only [Option.map_some]
      have hleft : pairs01 (v+1) ++ (false :: true :: left) =
          pairs01 (v+2) ++ left := by
        calc
          pairs01 (v+1) ++ (false :: true :: left) =
            pairs01 (v+1) ++ ([false,true] ++ left) := rfl
          _ = (pairs01 (v+1) ++ [false,true]) ++ left := by
            rw [← List.append_assoc]
          _ = pairs01 (v+2) ++ left := by
            exact congrArg (fun ys : List Bool => ys ++ left)
              (pairs01_rightstep (v+1)).symm
      rw [hleft]

theorem junc0_w1_to_b_count (v : Nat) :
    runCount (2*v+26) (junc 0 v 1) =
      some (z 1 (pairs01 (v+3) ++ ones 5) true [false,true], 0) := by
  have hprep := junc0_prep20_count v
  have hshift := shift_B01_count (v+2) (ones 5) [false,true]
  have hinput : z 1 (ones 5) false
      (true :: (pairs01 (v+2) ++ ones 1 ++ [false,true])) =
    z 1 (ones 5) false
      (true :: (pairs01 (v+2) ++ (true :: [false,true]))) := by
    simp [ones, List.append_assoc]
  have htime : 2*v+26 = 20 + 2*((v+2)+1) := by omega
  rw [htime,runCount_add,hprep]
  simp only [Option.bind_some]
  rw [hinput,hshift]
  rfl

/-- The sixteen-step B/1 excursion encounters precisely one C/0 state:
    its already established first record-right C/0 position. -/
theorem b1_to_scanE_16_count (v : Nat) :
    runCount 16 (z 1 (pairs01 (v+3) ++ ones 5) true [false,true]) =
      some (sourceScanE (v+2) sigma, 1) := by rfl

theorem junc0_w1_to_scanE_count (v : Nat) :
    runCount (2*v+42) (junc 0 v 1) =
      some (sourceScanE (v+2) sigma, 1) := by
  have hB := junc0_w1_to_b_count v
  have h16 := b1_to_scanE_16_count v
  rw [show 2*v+42 = (2*v+26)+16 by omega,runCount_add,hB]
  simp only [Option.bind_some]
  rw [h16]
  rfl

/-- The final fourteen-step C/1 continuation encounters no C/0 state
    before reaching its terminal C/0, even with arbitrary left context. -/
theorem c1_to_czero14_count (left : List Bool) :
    runCount 14 (z 2 left true sigma) =
      some (z 2 (([true,false,true] ++ ones 7) ++ left) false [],0) := by rfl

/-- Full parameter-uniform C/0 census up to the SECOND explicit visit.
    Exactly ONE C/0 instruction occurs at a strictly earlier time; the
    endpoint itself is a C/0 state, excluded from the count by definition.
    Combined with the exact first-visit time 2v+31, these are the only
    two visits in the entire closed interval. -/
theorem junc0_w1_second_czero_count (v : Nat) :
    runCount (2*v+42+(crossTime (v+2)+15)) (junc 0 v 1) =
      some (z 2 (([true,false,true] ++ ones 7) ++ finalLeft (v+2)) false [],1) := by
  have hfirst := junc0_w1_to_scanE_count v
  have hret : runCount (crossTime (v+2)+1) (sourceScanE (v+2) sigma) =
      some (z 2 (finalLeft (v+2)) true sigma,0) :=
    runSafe_to_count_zero (crossTime (v+2)+1) (sourceScanE (v+2) sigma)
      (z 2 (finalLeft (v+2)) true sigma) (scanE_safe (v+2) sigma)
  have htail := c1_to_czero14_count (finalLeft (v+2))
  have htime : 2*v+42+(crossTime (v+2)+15) =
      (2*v+42)+((crossTime (v+2)+1)+14) := by omega
  rw [htime,runCount_add,hfirst]
  simp only [Option.bind_some]
  rw [runCount_add,hret]
  simp only [Option.bind_some]
  rw [htail]
  rfl

#print axioms runCount_add
#print axioms runSafe_to_count_zero
#print axioms junc0_w1_second_czero_count

end BB429W4CZeroCount
