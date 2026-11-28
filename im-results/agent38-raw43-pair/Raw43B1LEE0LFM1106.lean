import SweepPumping
set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace BB6.Agent38Raw43B1LEE0LFM1106
open BB6Coverage BB6Coverage.Agent31Pump

/-!
Exact unbounded two-sweep recurrence for Raw43/B1LE/E0LF residual 1106:
  1RB1LC_1RC1LE_0RD0RB_1LD0RB_0LF---_0LA1LE

The only unassigned row is E1.  The recurrence never queries it.  Starting
from the blank tape, the machine reaches family 0 in 135 steps and then maps
family n to family (n+1) in exactly 4*n+41 steps.  The variable work is one
left sweep of (01) blocks and one right sweep of (10) blocks.
-/

def table : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0,false => some (some ⟨true,true,1⟩)
  | 0,true  => some (some ⟨true,false,2⟩)
  | 1,false => some (some ⟨true,true,2⟩)
  | 1,true  => some (some ⟨true,false,4⟩)
  | 2,false => some (some ⟨false,true,3⟩)
  | 2,true  => some (some ⟨false,true,1⟩)
  | 3,false => some (some ⟨true,false,3⟩)
  | 3,true  => some (some ⟨false,true,1⟩)
  | 4,false => some (some ⟨false,false,5⟩)
  | 5,false => some (some ⟨false,false,0⟩)
  | 5,true  => some (some ⟨true,false,4⟩)
  | _,_ => none

def zeros (n : Nat) : List Bool := rep [false] n

def family (n : Nat) : Z0 :=
  ⟨1,
    [false,false,false,true] ++ rep [false,true] (n+2) ++
      [false,false,true] ++ zeros (n+2) ++ [true,false,false,false,true,true],
    []⟩

theorem first : run0 table 135 ⟨0,[],[]⟩ = some (family 0) := by
  decide +kernel

theorem left_two : ∀ L R,
    run0 table 2 ⟨4,[false,true]++L,R⟩ =
      some ⟨4,L,[true,false]++R⟩ := by
  intro L R
  rfl

theorem right_two : ∀ L R,
    run0 table 2 ⟨1,[false]++L,[true,false]++R⟩ =
      some ⟨1,[false,false,true]++L,R⟩ := by
  intro L R
  rfl

theorem middle12 : ∀ L R,
    run0 table 12 ⟨4,[false,false,true,false,false]++L,
      [true,false,true,false,true,false]++R⟩ =
      some ⟨1,[false,false,true,false,true,false,false,true,false,false,false]++L,R⟩ := by
  intro L R
  rfl

theorem finish5 : ∀ L,
    run0 table 5 ⟨1,[false]++L,[true,false,false,true]⟩ =
      some ⟨1,[false,false,false,true,false,true]++L,[]⟩ := by
  intro L
  rfl

theorem growth (n : Nat) :
    run0 table (4*n+41) (family n) = some (family (n+1)) := by
  have h0 : run0 table 18 (family n) =
      some ⟨4,
        rep [false,true] (n+3) ++ [false,false,true] ++ zeros (n+2) ++
          [true,false,false,false,true,true],
        [true,false,false,true]⟩ := by
    rfl
  have hL : run0 table (2*(n+3))
      ⟨4,rep [false,true] (n+3) ++ [false,false,true] ++ zeros (n+2) ++
          [true,false,false,false,true,true],
        [true,false,false,true]⟩ =
      some ⟨4,
        [false,false,true] ++ zeros (n+2) ++ [true,false,false,false,true,true],
        rep [true,false] (n+3) ++ [true,false,false,true]⟩ := by
    have h := sweepL table 4 [] [] [false,true] [true,false] 2 left_two
      (n+3) ([false,false,true] ++ zeros (n+2) ++ [true,false,false,false,true,true])
      [true,false,false,true]
    simpa [List.append_assoc] using h
  have hM : run0 table 12
      ⟨4,[false,false,true] ++ zeros (n+2) ++ [true,false,false,false,true,true],
        rep [true,false] (n+3) ++ [true,false,false,true]⟩ =
      some ⟨1,
        [false,false,true,false,true,false,false,true] ++ zeros (n+3) ++
          [true,false,false,false,true,true],
        rep [true,false] n ++ [true,false,false,true]⟩ := by
    have h := middle12
      (zeros n ++ [true,false,false,false,true,true])
      (rep [true,false] n ++ [true,false,false,true])
    simpa [zeros, rep, List.append_assoc] using h
  have hR : run0 table (2*n)
      ⟨1,[false,false,true,false,true,false,false,true] ++ zeros (n+3) ++
          [true,false,false,false,true,true],
        rep [true,false] n ++ [true,false,false,true]⟩ =
      some ⟨1,
        [false] ++ rep [false,true] n ++ [false,true,false,true,false,false,true] ++
          zeros (n+3) ++ [true,false,false,false,true,true],
        [true,false,false,true]⟩ := by
    have h := sweepR table 1 [false] [] [true,false] [false,true] 2 right_two n
      ([false,true,false,true,false,false,true] ++ zeros (n+3) ++ [true,false,false,false,true,true])
      [true,false,false,true]
    simpa [List.append_assoc] using h
  have hEnd : run0 table 5
      ⟨1,[false] ++ rep [false,true] n ++ [false,true,false,true,false,false,true] ++
          zeros (n+3) ++ [true,false,false,false,true,true],
        [true,false,false,true]⟩ = some (family (n+1)) := by
    have h := finish5
      (rep [false,true] n ++ [false,true,false,true,false,false,true] ++
        zeros (n+3) ++ [true,false,false,false,true,true])
    have h' : run0 table 5
        ⟨1,[false] ++ rep [false,true] n ++ [false,true,false,true,false,false,true] ++
            zeros (n+3) ++ [true,false,false,false,true,true],
          [true,false,false,true]⟩ =
        some ⟨1,
          [false,false,false,true,false,true] ++ rep [false,true] n ++
            [false,true,false,true,false,false,true] ++ zeros (n+3) ++
            [true,false,false,false,true,true], []⟩ := by
      simpa [List.append_assoc] using h
    have commT (T : List Bool) :
        rep [false,true] n ++ ([false,true] ++ [false,true] ++ T) =
          [false,true] ++ [false,true] ++ rep [false,true] n ++ T := by
      calc
        rep [false,true] n ++ ([false,true] ++ [false,true] ++ T) =
            (rep [false,true] n ++ [false,true]) ++ [false,true] ++ T := by
              simp [List.append_assoc]
        _ = ([false,true] ++ rep [false,true] n) ++ [false,true] ++ T := by
              rw [rep_snoc [false,true] n]
        _ = [false,true] ++ (rep [false,true] n ++ [false,true]) ++ T := by
              simp [List.append_assoc]
        _ = [false,true] ++ ([false,true] ++ rep [false,true] n) ++ T := by
              rw [rep_snoc [false,true] n]
        _ = [false,true] ++ [false,true] ++ rep [false,true] n ++ T := by
              simp [List.append_assoc]
    have hl :
        [false,false,false,true,false,true] ++ rep [false,true] n ++
            [false,true,false,true,false,false,true] ++ zeros (n+3) ++
            [true,false,false,false,true,true] = (family (n+1)).l := by
      have hc := commT
        ([false,false,true] ++ zeros (n+3) ++ [true,false,false,false,true,true])
      have hp := congrArg
        (fun x : List Bool => [false,false,false,true,false,true] ++ x) hc
      simpa [family, zeros, rep, List.append_assoc] using hp
    rw [hl] at h'
    exact h'
  have H := join0 h0 (join0 hL (join0 hM (join0 hR hEnd)))
  have hc : 18 + ((2*(n+3)) + (12 + ((2*n) + 5))) = 4*n+41 := by omega
  simpa only [hc] using H

theorem never (m : Machine) (hm : compatible table m) : NeverHalts m := by
  apply never_of_growth table family 135 (fun n => 4*n+41) first
  · intro n
    omega
  · exact growth
  · exact hm

#print axioms first
#print axioms growth
#print axioms never
end BB6.Agent38Raw43B1LEE0LFM1106
