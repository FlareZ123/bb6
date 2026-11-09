import Frontier429
import Lean.Elab.Tactic.Omega

set_option maxRecDepth 8192
namespace BB429Odd0100
open Frontier429

/-- Three primitive instructions after the initial C/0. -/
theorem c3 (m : Nat) (tail : List Bool) :
    run 3 ⟨2, true :: ones2 m ++ [false,true,false,false] ++ tail, false, []⟩ =
      some ⟨0, ones2 m ++ [false,true,false,false] ++ tail, true, [false,true]⟩ := by
  simp [run,step,leftStep,rightStep]

/-- Repeat the A/1, F/1 left sweep without examining the remote suffix. -/
theorem af_sweep (m : Nat) (l r : List Bool) :
    run (2*m) ⟨0, ones2 m ++ l, true, r⟩ =
      some ⟨0,l,true,pairs m ++ r⟩ := by
  induction m generalizing r with
  | zero => simp [ones2,pairs,run]
  | succ m ih =>
    rw [show 2*(m+1)=2+2*m by omega,run_add]
    simp only [ones2,List.cons_append,twoAF,Option.bind_some]
    rw [ih]
    simp [pairs_succ_tail,List.append_assoc]

/-- Exact fixed turnaround, independent of the untouched right tape. -/
theorem turn14 (tail r : List Bool) :
    run 14 ⟨0,[false,true,false,false] ++ tail,true,r⟩ =
      some ⟨0,[true,true,true,true] ++ tail,false,r⟩ := by
  simp [run,step,leftStep,rightStep]

/-- Exact arbitrary-suffix fresh-frontier return of the original #429 table.
    Left and right lists are nearest-cell first, and all unlisted cells are 0. -/
theorem odd_0100_root (m : Nat) (tail : List Bool) :
    run (4*m+21)
      ⟨2,ones2 m ++ [true,false,true,false,false] ++ tail,false,[]⟩ =
    some ⟨2,[true,false] ++ ones2 (m+3) ++ tail,false,[]⟩ := by
  rw [show 4*m+21=3+(2*m+(14+(2*m+4))) by omega,run_add]
  have hs : ones2 m ++ [true,false,true,false,false] ++ tail =
      true :: ones2 m ++ [false,true,false,false] ++ tail := by
    induction m with
    | zero => rfl
    | succ m ih =>
        simpa [ones2,List.append_assoc] using
          congrArg (fun xs => true :: true :: xs) ih
  rw [hs, c3]
  simp only [Option.bind_some]
  rw [run_add]
  simp only [List.append_assoc]
  rw [af_sweep]
  simp only [Option.bind_some]
  rw [run_add,turn14]
  simp only [Option.bind_some]
  rw [show 2*m+4=2*m+4 by omega,run_add,ab_sweep]
  simp only [Option.bind_some]
  rw [finish4]
  simp only [Option.some.injEq]
  congr 1
  have h : ones2 m ++ [true,true,true,true] ++ tail =
      [true,true,true,true] ++ ones2 m ++ tail := by
    simp only [List.append_assoc, List.cons_append, List.nil_append]
    change ones2 m ++ (true :: true :: true :: true :: tail) =
      true :: true :: true :: true :: (ones2 m ++ tail)
    rw [ones2_rotate m (true :: true :: tail)]
    rw [ones2_rotate m tail]
  simpa [ones2, List.append_assoc] using h

#print axioms odd_0100_root
end BB429Odd0100
