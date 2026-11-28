import Raw42Cut
import SweepPumping
import Lean.Elab.Tactic.Omega

/-!
An explicit two-phase quadratic-time growth invariant for the heavyweight
original Raw42 / 0LE / Run15760 leaf (eleven fixed instructions, F1 undefined).
Unlike the original 78×67-state BiDFA proof, this uses six finite local
symbolic transfer laws and two block sweeps. Source verification is required
before claiming an accepted Cover or replacing original DFA artifacts.
-/
open BB6Coverage BB6Coverage.Agent31Pump
set_option maxRecDepth 4096
set_option maxHeartbeats 0
namespace BB6.Agent32Raw42Run15760Growth

def p : PartialMachine := fun s => match s with
  | (0,false) => some (some ⟨true,true,1⟩)
  | (0,true)  => some (some ⟨false,true,0⟩)
  | (1,false) => some (some ⟨true,true,2⟩)
  | (1,true)  => some (some ⟨false,false,4⟩)
  | (2,false) => some (some ⟨false,true,3⟩)
  | (2,true)  => some (some ⟨false,false,0⟩)
  | (3,false) => some (some ⟨true,false,3⟩)
  | (3,true)  => some (some ⟨false,false,1⟩)
  | (4,false) => some (some ⟨true,false,5⟩)
  | (4,true)  => some (some ⟨true,true,3⟩)
  | (5,false) => some (some ⟨false,true,0⟩)
  | _ => none

def a (n : Nat) : Z0 :=
  ⟨4, [false], [false,false,true,true,true] ++ rep [true,true] n ++ [false,true,true]⟩

def b (n : Nat) : Z0 :=
  ⟨4, [false,false], [false,false] ++ rep [true,false] (n+1) ++
      [true,true,true,true]⟩

theorem first : run0 p 83 ⟨0,[],[]⟩ = some (a 0) := by decide

-- A_n -> B_n: fixed initial phase, block transfer rightward, turn,
-- block transfer leftward, fixed terminal phase.
theorem aInit (R : List Bool) :
  run0 p 12 ⟨4,[false],[false,false,true,true,true] ++ R⟩ =
  some ⟨1,[false,true,false,false],[false,true,true] ++ R⟩ := by rfl

theorem aSweepR (L R : List Bool) :
  run0 p 6 ⟨1,[false] ++ L,[false,true,true] ++ R⟩ =
  some ⟨1,[false,true,true] ++ L,[false] ++ R⟩ := by rfl

theorem aTurn (L : List Bool) :
  run0 p 6 ⟨1,[false,true,true] ++ L,[false,false,true,true]⟩ =
  some ⟨4,[true] ++ L,[false,false,true,true,true,true]⟩ := by rfl

theorem aSweepL (L R : List Bool) :
  run0 p 4 ⟨4,[true,true,true] ++ L,[false,false] ++ R⟩ =
  some ⟨4,[true] ++ L,[false,false,true,false] ++ R⟩ := by rfl

theorem aTerminal (R : List Bool) :
  run0 p 4 ⟨4,[true,true,false,false],[false,false] ++ R⟩ =
  some ⟨4,[false,false],[false,false,true,false] ++ R⟩ := by rfl

theorem a_to_b (n : Nat) :
  run0 p (10*n+28) (a n) = some (b n) := by
  have h0 : run0 p 12 (a n) =
      some ⟨1,[false,true,false,false],
        [false] ++ rep [true,true] (n+1) ++ [false,true,true]⟩ := by
    simpa only [a,rep,List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using
      (aInit (rep [true,true] n ++ [false,true,true]))
  have h1 : run0 p (6*(n+1))
      ⟨1,[false,true,false,false],
        [false] ++ rep [true,true] (n+1) ++ [false,true,true]⟩ =
      some ⟨1,[false] ++ rep [true,true] (n+1) ++ [true,false,false],
        [false,false,true,true]⟩ := by
    simpa only [rep,List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using
      (sweepR p 1 [false] [false] [true,true] [true,true] 6
        aSweepR (n+1) [true,false,false] [false,true,true])
  have h2 : run0 p 6
      ⟨1,[false] ++ rep [true,true] (n+1) ++ [true,false,false],
        [false,false,true,true]⟩ =
      some ⟨4,[true] ++ rep [true,true] n ++ [true,false,false],
        [false,false,true,true,true,true]⟩ := by
    simpa only [rep,List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using
      (aTurn (rep [true,true] n ++ [true,false,false]))
  have h3 : run0 p (4*n)
      ⟨4,[true] ++ rep [true,true] n ++ [true,false,false],
        [false,false,true,true,true,true]⟩ =
      some ⟨4,[true,true,false,false],
        [false,false] ++ rep [true,false] n ++ [true,true,true,true]⟩ := by
    simpa only [rep,List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using
      (sweepL p 4 [true] [false,false] [true,true] [true,false] 4
        aSweepL n [true,false,false] [true,true,true,true])
  have h4 : run0 p 4
      ⟨4,[true,true,false,false],
        [false,false] ++ rep [true,false] n ++ [true,true,true,true]⟩ =
      some (b n) := by
    simpa only [b,rep,List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using
      (aTerminal (rep [true,false] n ++ [true,true,true,true]))
  have h := join0 (join0 (join0 (join0 h0 h1) h2) h3) h4
  rw [show 12+6*(n+1)+6+4*n+4 = 10*n+28 by omega] at h
  exact h

-- B_n -> A_(n+1): an alternating sweep right, a short turn, an
-- alternating-to-solid sweep left, and a constant terminal transition.
theorem bInit (R : List Bool) :
  run0 p 4 ⟨4,[false,false],[false,false] ++ R⟩ =
  some ⟨1,[false,true,false,false],R⟩ := by rfl

theorem bSweepR (L R : List Bool) :
  run0 p 4 ⟨1,[false] ++ L,[true,false] ++ R⟩ =
  some ⟨1,[false,true,false] ++ L,R⟩ := by rfl

theorem bTurn (L : List Bool) :
  run0 p 27 ⟨1,[false,true,false] ++ L,[true,true,true,true]⟩ =
  some ⟨4,[true,false] ++ L,[false,false,true,false,true,true]⟩ := by rfl

theorem bSweepL (L R : List Bool) :
  run0 p 12 ⟨4,[true,false,true] ++ L,[false,false] ++ R⟩ =
  some ⟨4,[true] ++ L,[false,false,true,true] ++ R⟩ := by rfl

theorem bTerminal (R : List Bool) :
  run0 p 12 ⟨4,[true,false,false],[false,false,true,true] ++ R⟩ =
  some ⟨4,[false],[false,false,true,true,true,true] ++ R⟩ := by rfl

theorem rotate_b (n : Nat) :
    [true,false] ++ rep [true,false] n ++ [true,false,false] =
    [true] ++ rep [false,true] (n+1) ++ [false,false] := by
  have hr : rep [true,false] n ++ [true] = [true] ++ rep [false,true] n := by
    simpa only [List.cons_append,List.nil_append] using (rotate true [false] n).symm
  calc
    _ = [true,false] ++ (rep [true,false] n ++ [true]) ++ [false,false] := by
      simp only [List.append_assoc,List.cons_append,List.nil_append]
    _ = [true,false] ++ ([true] ++ rep [false,true] n) ++ [false,false] := by rw [hr]
    _ = [true] ++ rep [false,true] (n+1) ++ [false,false] := by
      simp only [rep,List.append_assoc,List.cons_append,List.nil_append]

theorem rotate_a (n : Nat) :
    [false,false,true,true,true,true] ++ rep [true,true] n ++
      [true,false,true,true] =
    [false,false,true,true,true] ++ rep [true,true] (n+1) ++
      [false,true,true] := by
  have hr : rep [true,true] n ++ [true] = [true] ++ rep [true,true] n := by
    simpa only [List.cons_append,List.nil_append] using (rotate true [true] n).symm
  calc
    _ = [false,false,true,true,true,true] ++
          (rep [true,true] n ++ [true]) ++ [false,true,true] := by
      simp only [List.append_assoc,List.cons_append,List.nil_append]
    _ = [false,false,true,true,true,true] ++
          ([true] ++ rep [true,true] n) ++ [false,true,true] := by rw [hr]
    _ = [false,false,true,true,true] ++ rep [true,true] (n+1) ++
          [false,true,true] := by
      simp only [rep,List.append_assoc,List.cons_append,List.nil_append]

theorem b_to_a (n : Nat) :
  run0 p (16*n+59) (b n) = some (a (n+1)) := by
  have h0 : run0 p 4 (b n) =
      some ⟨1,[false,true,false,false],
        rep [true,false] (n+1) ++ [true,true,true,true]⟩ := by
    simpa only [b,List.append_assoc,List.cons_append,List.nil_append] using
      (bInit (rep [true,false] (n+1) ++ [true,true,true,true]))
  have h1 : run0 p (4*(n+1))
      ⟨1,[false,true,false,false],
        rep [true,false] (n+1) ++ [true,true,true,true]⟩ =
      some ⟨1,[false] ++ rep [true,false] (n+1) ++ [true,false,false],
        [true,true,true,true]⟩ := by
    simpa only [rep,List.append_assoc,List.cons_append,List.nil_append] using
      (sweepR p 1 [false] [] [true,false] [true,false] 4
        bSweepR (n+1) [true,false,false] [true,true,true,true])
  have h2 : run0 p 27
      ⟨1,[false] ++ rep [true,false] (n+1) ++ [true,false,false],
        [true,true,true,true]⟩ =
      some ⟨4,[true] ++ rep [false,true] (n+1) ++ [false,false],
        [false,false,true,false,true,true]⟩ := by
    have hh := bTurn (rep [true,false] n ++ [true,false,false])
    have heq : [true,false] ++ (rep [true,false] n ++ [true,false,false]) =
        [true] ++ rep [false,true] (n+1) ++ [false,false] := by
      simpa only [List.append_assoc] using rotate_b n
    rw [heq] at hh
    simpa only [rep,List.append_assoc,List.cons_append,List.nil_append] using hh
  have h3 : run0 p (12*(n+1))
      ⟨4,[true] ++ rep [false,true] (n+1) ++ [false,false],
        [false,false,true,false,true,true]⟩ =
      some ⟨4,[true,false,false],
        [false,false] ++ rep [true,true] (n+1) ++ [true,false,true,true]⟩ := by
    simpa only [rep,List.append_assoc,List.cons_append,List.nil_append] using
      (sweepL p 4 [true] [false,false] [false,true] [true,true] 12
        bSweepL (n+1) [false,false] [true,false,true,true])
  have h4 : run0 p 12
      ⟨4,[true,false,false],
        [false,false] ++ rep [true,true] (n+1) ++ [true,false,true,true]⟩ =
      some (a (n+1)) := by
    have hh := bTerminal (rep [true,true] n ++ [true,false,true,true])
    have heq : [false,false,true,true,true,true] ++ (rep [true,true] n ++ [true,false,true,true]) =
        [false,false,true,true,true] ++ rep [true,true] (n+1) ++ [false,true,true] := by
      simpa only [List.append_assoc] using rotate_a n
    rw [heq] at hh
    simpa only [a,rep,List.append_assoc,List.cons_append,List.nil_append] using hh
  have h := join0 (join0 (join0 (join0 h0 h1) h2) h3) h4
  rw [show 4+4*(n+1)+27+12*(n+1)+12 = 16*n+59 by omega] at h
  exact h

theorem grow (n : Nat) :
  run0 p (26*n+87) (a n) = some (a (n+1)) := by
  have h := join0 (a_to_b n) (b_to_a n)
  rw [show 10*n+28+(16*n+59)=26*n+87 by omega] at h
  exact h

theorem never (m : Machine) (hm : compatible p m) : NeverHalts m :=
  never_of_growth p a 83 (fun n => 26*n+87) first (by omega) grow m hm
#print axioms never

theorem cover (B : Nat) : Cover (WeightedBound B) p := by
  apply Cover.leaf p
  intro m hm
  exact weighted_never B m (never m hm)
#print axioms cover

end BB6.Agent32Raw42Run15760Growth
