import SweepPumping
set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace BB6.Agent9Raw43B1LEE0LFM559
open BB6Coverage BB6Coverage.Agent31Pump

/-!
Exact formalization of the previously opaque final phase of the Raw43/B1LE/E0LF
residual-559 recurrence.

Residual:
  1RB---_1RC1LE_0RD1RF_1LD0RB_0LF0LE_1RA0RB

Only A1 is undefined.  The theorem `phase_final` proves, for every n, the
entire final P4 -> F segment in exactly 136*n+204 primitive transitions.
This replaces finite simulation of that segment by a parametric kernel proof.
-/

def table : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0,false => some (some ⟨true,true,1⟩)
  | 1,false => some (some ⟨true,true,2⟩)
  | 1,true  => some (some ⟨true,false,4⟩)
  | 2,false => some (some ⟨false,true,3⟩)
  | 2,true  => some (some ⟨true,true,5⟩)
  | 3,false => some (some ⟨true,false,3⟩)
  | 3,true  => some (some ⟨false,true,1⟩)
  | 4,false => some (some ⟨false,false,5⟩)
  | 4,true  => some (some ⟨false,false,4⟩)
  | 5,false => some (some ⟨true,true,0⟩)
  | 5,true  => some (some ⟨false,true,1⟩)
  | _,_ => none

def A (n : Nat) : Nat := 4*n+3
def B (n : Nat) : Nat := 2*n+2

def cTail : List Bool :=
  [true,false,true,true,false,false,true,false,true,true,false,true]

def eTail : List Bool :=
  [true,false,false,true,false,true,true,false,true]

def fTail : List Bool :=
  [true,false,true,false,true,true,false,true,true,false,true]

/-- P4_n from the discovered quadratic recurrence, arranged for the C sweeps. -/
def p4 (n : Nat) : Z0 :=
  ⟨4,[],
    [false,false,false,false,false,true,false,true,true,false,true] ++
      rep [true,true] (B n) ++ [true] ++
      rep [false,true,true] (A n) ++ [false,false,true,true]⟩

/-- Exact output of the final phase, before the separate family-list normalization. -/
def finalOut (n : Nat) : Z0 :=
  ⟨5,
    [false,true,true,false] ++ rep [true,true,false] (A n + 1) ++
      [true] ++ rep [true,false] (B n) ++ fTail,
    []⟩

/-- The F-on-fresh-zero family observed on the exact blank orbit. -/
def family (n : Nat) : Z0 :=
  ⟨5,
    [false,true] ++ rep [true,false,true] (4*n+2) ++
      rep [false,true] (2*n+1) ++ [true,false,true,true,false,true],
    []⟩

theorem preludeC (R : List Bool) :
    run0 table 21
      ⟨4,[],[false,false,false,false,false,true,false,true,true,false,true]++R⟩ =
    some ⟨2,[true,true,false,true,true,false,false,true,false,true,true,false,true],R⟩ := by
  rfl

theorem right6C (L R : List Bool) :
    run0 table 6 ⟨2,[true]++L,[true,true]++R⟩ =
      some ⟨2,[true,true,false]++L,R⟩ := by
  rfl

theorem right3C (L R : List Bool) :
    run0 table 3 ⟨2,[true]++L,[true,false,true]++R⟩ =
      some ⟨2,[true,true,false,true]++L,R⟩ := by
  rfl

theorem finishCE (L R : List Bool) :
    run0 table 11 ⟨2,[true]++L,[true,false,false,true,true]++R⟩ =
      some ⟨4,[true,true,false,true]++L,[false,true]++R⟩ := by
  rfl

theorem left15 (L R : List Bool) :
    run0 table 15 ⟨4,[true,true,false,true]++L,R⟩ =
      some ⟨4,[true]++L,[false,true,true]++R⟩ := by
  rfl

theorem left14 (L R : List Bool) :
    run0 table 14 ⟨4,[true,false,true]++L,[false]++R⟩ =
      some ⟨4,[true]++L,[false,true,true]++R⟩ := by
  rfl

theorem preludeF (L R : List Bool) :
    run0 table 21 ⟨4,[true,true,false,false]++L,[false,true,true]++R⟩ =
      some ⟨5,[true,true,true,false,true,false,true]++L,R⟩ := by
  rfl

theorem right6F (L R : List Bool) :
    run0 table 6 ⟨5,[true,true]++L,[true,true]++R⟩ =
      some ⟨5,[true,true,true,false]++L,R⟩ := by
  rfl

theorem right3F (L R : List Bool) :
    run0 table 3 ⟨5,[true]++L,[false,true,true]++R⟩ =
      some ⟨5,[true,true,true,false]++L,R⟩ := by
  rfl

theorem finish3 (L : List Bool) :
    run0 table 3 ⟨5,[true]++L,[false,true]⟩ =
      some ⟨5,[false,true,true,false]++L,[]⟩ := by
  rfl

theorem rotateRightC (n : Nat) :
    [true] ++ rep [false,true,true] (A n) ++ [false,false,true,true] =
      rep [true,false,true] (A n) ++ [true,false,false,true,true] := by
  have h := rotate true [false,true] (A n)
  have hh := congrArg
    (fun x : List Bool => x ++ [false,false,true,true]) h
  simpa [List.append_assoc] using hh

theorem alignTail (k : Nat) :
    rep [true,false] k ++ cTail =
      [true,false,true] ++ rep [false,true] k ++ eTail := by
  induction k with
  | zero => rfl
  | succ k ih =>
    simp only [rep, cTail, eTail, List.append_assoc]
    rw [ih]
    rfl

theorem alignAfterCE (a b : Nat) :
    [true,true,false,true] ++ rep [true,false,true] a ++
        rep [true,false] b ++ cTail =
      [true] ++ rep [true,false,true] (a+2) ++
        rep [false,true] b ++ eTail := by
  simp only [List.append_assoc]
  rw [show rep [true,false] b ++ cTail =
      [true,false,true] ++ rep [false,true] b ++ eTail from alignTail b]
  rw [show a+2 = (a+1)+1 by omega]
  have h := rep_snoc [true,false,true] a
  have hh := congrArg
    (fun x : List Bool => [true] ++ x ++ rep [false,true] b ++ eTail) h
  simpa [rep, List.append_assoc] using hh

theorem alignBeforeF (b : Nat) (X : List Bool) :
    [false] ++ rep [true,true] b ++ [true,true] ++ X =
      [false,true,true] ++ rep [true,true] b ++ X := by
  have h := rep_snoc [true,true] b
  have hh := congrArg (fun x : List Bool => [false] ++ x ++ X) h
  simpa [List.append_assoc] using hh

theorem alignFTail (p : Nat) :
    rep [true,false] p ++ fTail =
      [true,false,true] ++ rep [false,true] (p+1) ++
        [true,false,true,true,false,true] := by
  induction p with
  | zero => rfl
  | succ p ih =>
    simp only [rep, List.append_assoc]
    rw [ih]
    rfl

theorem prefixShift (m : Nat) (X : List Bool) :
    [false,true,true,false] ++ [true] ++ rep [true,false,true] m ++
        [true,false,true] ++ X =
      [false,true] ++ [true,false,true] ++ [true,false,true] ++
        rep [true,false,true] m ++ X := by
  have h := rep_snoc [true,false,true] m
  have hh := congrArg
    (fun x : List Bool => [false,true] ++ [true,false,true] ++ x ++ X) h
  simpa [List.append_assoc] using hh

theorem normalizeFinal (m p : Nat) :
    [false,true,true,false] ++ rep [true,true,false] m ++ [true] ++
        rep [true,false] p ++ fTail =
      [false,true] ++ rep [true,false,true] (m+2) ++
        rep [false,true] (p+1) ++ [true,false,true,true,false,true] := by
  have hr := rotate true [true,false] m
  have hr0 :
      [true] ++ rep [true,false,true] m =
        rep [true,true,false] m ++ [true] := by
    simpa using hr
  have ht := alignFTail p
  simp only [List.append_assoc]
  rw [← List.append_assoc (rep [true,true,false] m) [true]
    (rep [true,false] p ++ fTail)]
  rw [← hr0]
  simp only [List.append_assoc]
  rw [ht]
  rw [show m+2=(m+1)+1 by omega]
  simp only [rep, List.append_assoc]
  simpa [List.append_assoc] using prefixShift m
    ([false,true] ++ rep [false,true] p ++
      [true,false,true,true,false,true])

theorem finalOut_eq_family_succ (n : Nat) : finalOut n = family (n+1) := by
  apply Z0.mk.injEq.mpr
  constructor
  · rfl
  constructor
  · simpa [finalOut, family, A, B] using normalizeFinal (A n + 1) (B n)
  · rfl

def C (n : Nat) : Nat := 4*n+2
def D (n : Nat) : Nat := 2*n+1

/-- Exact first-phase endpoint, kept in sweep-native form. -/
def p1raw (n : Nat) : Z0 :=
  ⟨4,[],
    [false,false,true,true,false,true,true,false] ++
      rep [true,true] (D n) ++ [true,true] ++
      rep [false,true,true] (4*n+1) ++
      [false,false,true,true,false,false,true,true]⟩

/-- Exact P2 endpoint after the fixed 16-step turnaround. -/
def p2raw (n : Nat) : Z0 :=
  ⟨4,[],
    [false,false,false,false,false,true,false,true,true,false] ++
      rep [true,true] (D n) ++ [true,true] ++
      rep [false,true,true] (4*n+1) ++
      [false,false,true,true,false,false,true,true]⟩

theorem start41 (L : List Bool) :
    run0 table 41 ⟨5,[false]++L,[]⟩ =
      some ⟨4,L,[false,false,true,true,false,false,true,true]⟩ := by
  rfl

theorem finish31 (R : List Bool) :
    run0 table 31 ⟨4,[true,true,false,true,true,false,true],R⟩ =
      some ⟨4,[],[false,false,true,true,false,true,true]++R⟩ := by
  rfl

theorem turn16 (R : List Bool) :
    run0 table 16 ⟨4,[],[false,false,true,true,false,true,true,false]++R⟩ =
      some ⟨4,[],[false,false,false,false,false,true,false,true,true,false]++R⟩ := by
  rfl

theorem phase_first_raw (n : Nat) :
    run0 table (88*n+116) (family n) = some (p1raw n) := by
  have h0 : run0 table 41 (family n) =
      some ⟨4,
        [true] ++ rep [true,false,true] (C n) ++
          rep [false,true] (D n) ++ [true,false,true,true,false,true],
        [false,false,true,true,false,false,true,true]⟩ := by
    simpa [family, C, D, List.append_assoc] using
      start41
        ([true] ++ rep [true,false,true] (C n) ++
          rep [false,true] (D n) ++ [true,false,true,true,false,true])

  have h1 : run0 table (15*(C n))
      ⟨4,[true] ++ rep [true,false,true] (C n) ++
          rep [false,true] (D n) ++ [true,false,true,true,false,true],
        [false,false,true,true,false,false,true,true]⟩ =
      some ⟨4,
        [true] ++ rep [false,true] (D n) ++ [true,false,true,true,false,true],
        rep [false,true,true] (C n) ++
          [false,false,true,true,false,false,true,true]⟩ := by
    have h := sweepL table 4 [true] [] [true,false,true] [false,true,true] 15
      left15 (C n)
      (rep [false,true] (D n) ++ [true,false,true,true,false,true])
      [false,false,true,true,false,false,true,true]
    simpa [List.append_assoc] using h

  have h2 : run0 table (14*(D n))
      ⟨4,[true] ++ rep [false,true] (D n) ++ [true,false,true,true,false,true],
        rep [false,true,true] (C n) ++
          [false,false,true,true,false,false,true,true]⟩ =
      some ⟨4,[true,true,false,true,true,false,true],
        [false] ++ rep [true,true] (D n) ++ [true,true] ++
          rep [false,true,true] (4*n+1) ++
          [false,false,true,true,false,false,true,true]⟩ := by
    have h := sweepL table 4 [true] [false] [false,true] [true,true] 14
      left14 (D n) [true,false,true,true,false,true]
      ([true,true] ++ rep [false,true,true] (4*n+1) ++
        [false,false,true,true,false,false,true,true])
    have hc : C n = (4*n+1)+1 := by simp [C]; omega
    rw [hc] at *
    simpa [rep, List.append_assoc] using h

  have h3 : run0 table 31
      ⟨4,[true,true,false,true,true,false,true],
        [false] ++ rep [true,true] (D n) ++ [true,true] ++
          rep [false,true,true] (4*n+1) ++
          [false,false,true,true,false,false,true,true]⟩ =
      some (p1raw n) := by
    simpa [p1raw, List.append_assoc] using finish31
      ([false] ++ rep [true,true] (D n) ++ [true,true] ++
        rep [false,true,true] (4*n+1) ++
        [false,false,true,true,false,false,true,true])

  have H := join0 h0 (join0 h1 (join0 h2 h3))
  have hc :
      41 + (15*(C n) + (14*(D n) + 31)) = 88*n+116 := by
    simp [C,D]
    omega
  simpa only [hc] using H

theorem phase_turn_raw (n : Nat) :
    run0 table 16 (p1raw n) = some (p2raw n) := by
  simpa [p1raw, p2raw, List.append_assoc] using
    turn16
      (rep [true,true] (D n) ++ [true,true] ++
        rep [false,true,true] (4*n+1) ++
        [false,false,true,true,false,false,true,true])

theorem phase_to_p2raw (n : Nat) :
    run0 table (88*n+132) (family n) = some (p2raw n) := by
  have H := join0 (phase_first_raw n) (phase_turn_raw n)
  have hc : (88*n+116)+16 = 88*n+132 := by omega
  simpa only [hc] using H

def K (n : Nat) : Nat := 4*n+1

/-- Endpoint of the first half of the P2 -> P3 transfer. -/
def midraw (n : Nat) : Z0 :=
  ⟨4,[true,true,false,false,true,false,true,true,false,true],
    [false] ++ rep [true,true] (D n) ++ [true,true] ++
      rep [false,true,true] (K n + 1) ++
      [false,true,false,false,true,true]⟩

/-- P3 in the same sweep-native representation as P1/P2. -/
def p3raw (n : Nat) : Z0 :=
  ⟨4,[],
    [false,false,true,true,false,true,true,false] ++
      rep [true,true] (D n + 1) ++ [true,true] ++
      rep [false,true,true] (K n + 2) ++ [false,false,true,true]⟩

/-- The turnaround image of P3, before the equivalent P4 rebracketing. -/
def p4turn (n : Nat) : Z0 :=
  ⟨4,[],
    [false,false,false,false,false,true,false,true,true,false] ++
      rep [true,true] (D n + 1) ++ [true,true] ++
      rep [false,true,true] (K n + 2) ++ [false,false,true,true]⟩

theorem finish8FE (L R : List Bool) :
    run0 table 8 ⟨5,[true]++L,[false,true,false,false,true]++R⟩ =
      some ⟨4,[true,true,false]++L,[false,false,true]++R⟩ := by
  rfl

theorem alignOnesPrelude (d : Nat) :
    [true] ++ rep [true,true] d ++ [true,true] =
      rep [true,true] (d+1) ++ [true] := by
  induction d with
  | zero => rfl
  | succ d ih =>
    have hh := congrArg (fun x : List Bool => [true,true] ++ x) ih
    simpa [rep, List.append_assoc] using hh

theorem alignOnesTurn (d : Nat) :
    rep [true,true] d ++ [true,true] =
      [true] ++ rep [true,true] d ++ [true] := by
  induction d with
  | zero => rfl
  | succ d ih =>
    simp only [rep, List.append_assoc]
    rw [ih]
    rfl

theorem rotate011 (k : Nat) (X : List Bool) :
    [true] ++ rep [false,true,true] k ++ X =
      rep [true,false,true] k ++ [true] ++ X := by
  have h := rotate true [false,true] k
  have hh := congrArg (fun x : List Bool => x ++ X) h
  simpa [List.append_assoc] using hh

theorem alignAfterFE (m p : Nat) :
    rep [true,true,false] m ++ [true] ++ rep [true,false] p ++ fTail =
      [true] ++ rep [true,false,true] (m+1) ++ rep [false,true] (p+1) ++
        [true,false,true,true,false,true] := by
  have hr := rotate true [true,false] m
  have hr0 :
      [true] ++ rep [true,false,true] m =
        rep [true,true,false] m ++ [true] := by
    simpa using hr
  have ht := alignFTail p
  have hs := rep_snoc [true,false,true] m
  simp only [List.append_assoc]
  rw [← List.append_assoc (rep [true,true,false] m) [true]
    (rep [true,false] p ++ fTail)]
  rw [← hr0]
  simp only [List.append_assoc]
  rw [ht]
  have hm :
      rep [true,false,true] (m+1) =
        [true,false,true] ++ rep [true,false,true] m := by
    rfl
  rw [hm]
  have hh := congrArg
    (fun x : List Bool => [true] ++ x ++ rep [false,true] (p+1) ++
      [true,false,true,true,false,true]) hs
  simpa [List.append_assoc] using hh

theorem phase_middle_first (n : Nat) :
    run0 table (112*n+100) (p2raw n) = some (midraw n) := by
  have h0raw : run0 table 21 (p2raw n) =
      some ⟨2,[true,true,false,true,true,false,false,true,false,true,true,false,true],
        [true] ++ rep [true,true] (2*n) ++ [true,true] ++
          rep [false,true,true] (K n) ++
          [false,false,true,true,false,false,true,true]⟩ := by
    simpa [p2raw, D, K, rep, List.append_assoc] using
      preludeC
        ([true] ++ rep [true,true] (2*n) ++ [true,true] ++
          rep [false,true,true] (K n) ++
          [false,false,true,true,false,false,true,true])

  have h0 : run0 table 21 (p2raw n) =
      some ⟨2,[true]++cTail,
        rep [true,true] (D n) ++ [true] ++
          rep [false,true,true] (K n) ++
          [false,false,true,true,false,false,true,true]⟩ := by
    rw [alignOnesPrelude (2*n)] at h0raw
    simpa [cTail, D, List.append_assoc] using h0raw

  have h1 : run0 table (6*(D n))
      ⟨2,[true]++cTail,
        rep [true,true] (D n) ++ [true] ++ rep [false,true,true] (K n) ++
          [false,false,true,true,false,false,true,true]⟩ =
      some ⟨2,[true] ++ rep [true,false] (D n) ++ cTail,
        [true] ++ rep [false,true,true] (K n) ++
          [false,false,true,true,false,false,true,true]⟩ := by
    have h := sweepR table 2 [true] [] [true,true] [true,false] 6 right6C
      (D n) cTail
      ([true] ++ rep [false,true,true] (K n) ++
        [false,false,true,true,false,false,true,true])
    simpa [List.append_assoc] using h

  have h2 : run0 table (3*(K n))
      ⟨2,[true] ++ rep [true,false] (D n) ++ cTail,
        [true] ++ rep [false,true,true] (K n) ++
          [false,false,true,true,false,false,true,true]⟩ =
      some ⟨2,[true] ++ rep [true,false,true] (K n) ++
          rep [true,false] (D n) ++ cTail,
        [true,false,false,true,true,false,false,true,true]⟩ := by
    have h := sweepR table 2 [true] [] [true,false,true] [true,false,true] 3
      right3C (K n) (rep [true,false] (D n) ++ cTail)
      [true,false,false,true,true,false,false,true,true]
    rw [← rotate011 (K n)
      [false,false,true,true,false,false,true,true]] at h
    simpa [List.append_assoc] using h

  have h3raw : run0 table 11
      ⟨2,[true] ++ rep [true,false,true] (K n) ++
          rep [true,false] (D n) ++ cTail,
        [true,false,false,true,true,false,false,true,true]⟩ =
      some ⟨4,[true,true,false,true] ++ rep [true,false,true] (K n) ++
          rep [true,false] (D n) ++ cTail,
        [false,true,false,false,true,true]⟩ := by
    simpa [List.append_assoc] using finishCE
      (rep [true,false,true] (K n) ++ rep [true,false] (D n) ++ cTail)
      [false,false,true,true]

  have h3 : run0 table 11
      ⟨2,[true] ++ rep [true,false,true] (K n) ++
          rep [true,false] (D n) ++ cTail,
        [true,false,false,true,true,false,false,true,true]⟩ =
      some ⟨4,[true] ++ rep [true,false,true] (K n+2) ++
          rep [false,true] (D n) ++ eTail,
        [false,true,false,false,true,true]⟩ := by
    rw [← alignAfterCE (K n) (D n)]
    exact h3raw

  have h4 : run0 table (15*(K n+2))
      ⟨4,[true] ++ rep [true,false,true] (K n+2) ++
          rep [false,true] (D n) ++ eTail,
        [false,true,false,false,true,true]⟩ =
      some ⟨4,[true] ++ rep [false,true] (D n) ++ eTail,
        rep [false,true,true] (K n+2) ++ [false,true,false,false,true,true]⟩ := by
    have h := sweepL table 4 [true] [] [true,false,true] [false,true,true] 15
      left15 (K n+2) (rep [false,true] (D n) ++ eTail)
      [false,true,false,false,true,true]
    simpa [List.append_assoc] using h

  have h5 : run0 table (14*(D n))
      ⟨4,[true] ++ rep [false,true] (D n) ++ eTail,
        rep [false,true,true] (K n+2) ++ [false,true,false,false,true,true]⟩ =
      some (midraw n) := by
    have h := sweepL table 4 [true] [false] [false,true] [true,true] 14
      left14 (D n) eTail
      ([true,true] ++ rep [false,true,true] (K n+1) ++
        [false,true,false,false,true,true])
    have hk : K n+2 = (K n+1)+1 := by omega
    rw [hk] at *
    simpa [midraw, eTail, List.append_assoc] using h

  have H := join0 h0 (join0 h1 (join0 h2 (join0 h3 (join0 h4 h5))))
  have hc :
      21 + (6*(D n) + (3*(K n) + (11 + (15*(K n+2) + 14*(D n))))) =
        112*n+100 := by
    simp [D,K]
    omega
  simpa only [hc] using H

theorem phase_middle_second (n : Nat) :
    run0 table (112*n+160) (midraw n) = some (p3raw n) := by
  have h0raw : run0 table 21 (midraw n) =
      some ⟨5,[true,true]++fTail,
        rep [true,true] (2*n) ++ [true,true] ++
          rep [false,true,true] (K n+1) ++
          [false,true,false,false,true,true]⟩ := by
    simpa [midraw, D, fTail, rep, List.append_assoc] using
      preludeF [true,false,true,true,false,true]
        (rep [true,true] (2*n) ++ [true,true] ++
          rep [false,true,true] (K n+1) ++
          [false,true,false,false,true,true])

  have h0 : run0 table 21 (midraw n) =
      some ⟨5,[true,true]++fTail,
        rep [true,true] (D n) ++ rep [false,true,true] (K n+1) ++
          [false,true,false,false,true,true]⟩ := by
    have hs := rep_snoc [true,true] (2*n)
    rw [hs] at h0raw
    simpa [D, rep, List.append_assoc] using h0raw

  have h1 : run0 table (6*(D n))
      ⟨5,[true,true]++fTail,
        rep [true,true] (D n) ++ rep [false,true,true] (K n+1) ++
          [false,true,false,false,true,true]⟩ =
      some ⟨5,[true,true] ++ rep [true,false] (D n) ++ fTail,
        rep [false,true,true] (K n+1) ++
          [false,true,false,false,true,true]⟩ := by
    have h := sweepR table 5 [true,true] [] [true,true] [true,false] 6 right6F
      (D n) fTail
      (rep [false,true,true] (K n+1) ++ [false,true,false,false,true,true])
    simpa [List.append_assoc] using h

  have h2 : run0 table (3*(K n+1))
      ⟨5,[true,true] ++ rep [true,false] (D n) ++ fTail,
        rep [false,true,true] (K n+1) ++
          [false,true,false,false,true,true]⟩ =
      some ⟨5,[true] ++ rep [true,true,false] (K n+1) ++
          [true] ++ rep [true,false] (D n) ++ fTail,
        [false,true,false,false,true,true]⟩ := by
    have h := sweepR table 5 [true] [] [false,true,true] [true,true,false] 3
      right3F (K n+1) ([true] ++ rep [true,false] (D n) ++ fTail)
      [false,true,false,false,true,true]
    simpa [List.append_assoc] using h

  have h3raw : run0 table 8
      ⟨5,[true] ++ rep [true,true,false] (K n+1) ++
          [true] ++ rep [true,false] (D n) ++ fTail,
        [false,true,false,false,true,true]⟩ =
      some ⟨4,[true,true,false] ++ rep [true,true,false] (K n+1) ++
          [true] ++ rep [true,false] (D n) ++ fTail,
        [false,false,true,true]⟩ := by
    simpa [List.append_assoc] using finish8FE
      (rep [true,true,false] (K n+1) ++
        [true] ++ rep [true,false] (D n) ++ fTail)
      [true]

  have h3 : run0 table 8
      ⟨5,[true] ++ rep [true,true,false] (K n+1) ++
          [true] ++ rep [true,false] (D n) ++ fTail,
        [false,true,false,false,true,true]⟩ =
      some ⟨4,[true] ++ rep [true,false,true] (K n+3) ++
          rep [false,true] (D n+1) ++ [true,false,true,true,false,true],
        [false,false,true,true]⟩ := by
    have ha := alignAfterFE (K n+2) (D n)
    have hm :
        [true,true,false] ++ rep [true,true,false] (K n+1) =
          rep [true,true,false] (K n+2) := by
      rfl
    rw [hm] at h3raw
    rw [ha] at h3raw
    have hk : (K n+2)+1 = K n+3 := by omega
    simpa only [hk] using h3raw

  have h4 : run0 table (15*(K n+3))
      ⟨4,[true] ++ rep [true,false,true] (K n+3) ++
          rep [false,true] (D n+1) ++ [true,false,true,true,false,true],
        [false,false,true,true]⟩ =
      some ⟨4,[true] ++ rep [false,true] (D n+1) ++
          [true,false,true,true,false,true],
        rep [false,true,true] (K n+3) ++ [false,false,true,true]⟩ := by
    have h := sweepL table 4 [true] [] [true,false,true] [false,true,true] 15
      left15 (K n+3)
      (rep [false,true] (D n+1) ++ [true,false,true,true,false,true])
      [false,false,true,true]
    simpa [List.append_assoc] using h

  have h5 : run0 table (14*(D n+1))
      ⟨4,[true] ++ rep [false,true] (D n+1) ++
          [true,false,true,true,false,true],
        rep [false,true,true] (K n+3) ++ [false,false,true,true]⟩ =
      some ⟨4,[true,true,false,true,true,false,true],
        [false] ++ rep [true,true] (D n+1) ++ [true,true] ++
          rep [false,true,true] (K n+2) ++ [false,false,true,true]⟩ := by
    have h := sweepL table 4 [true] [false] [false,true] [true,true] 14
      left14 (D n+1) [true,false,true,true,false,true]
      ([true,true] ++ rep [false,true,true] (K n+2) ++ [false,false,true,true])
    have hk : K n+3 = (K n+2)+1 := by omega
    rw [hk] at *
    simpa [rep, List.append_assoc] using h

  have h6 : run0 table 31
      ⟨4,[true,true,false,true,true,false,true],
        [false] ++ rep [true,true] (D n+1) ++ [true,true] ++
          rep [false,true,true] (K n+2) ++ [false,false,true,true]⟩ =
      some (p3raw n) := by
    simpa [p3raw, List.append_assoc] using finish31
      ([false] ++ rep [true,true] (D n+1) ++ [true,true] ++
        rep [false,true,true] (K n+2) ++ [false,false,true,true])

  have H := join0 h0 (join0 h1 (join0 h2 (join0 h3 (join0 h4 (join0 h5 h6)))))
  have hc :
      21 + (6*(D n) + (3*(K n+1) + (8 + (15*(K n+3) +
        (14*(D n+1) + 31))))) = 112*n+160 := by
    simp [D,K]
    omega
  simpa only [hc] using H

theorem phase_middle (n : Nat) :
    run0 table (224*n+260) (p2raw n) = some (p3raw n) := by
  have H := join0 (phase_middle_first n) (phase_middle_second n)
  have hc : (112*n+100)+(112*n+160) = 224*n+260 := by omega
  simpa only [hc] using H

theorem phase_p3_turn (n : Nat) :
    run0 table 16 (p3raw n) = some (p4turn n) := by
  simpa [p3raw, p4turn, List.append_assoc] using turn16
    (rep [true,true] (D n+1) ++ [true,true] ++
      rep [false,true,true] (K n+2) ++ [false,false,true,true])

theorem p4turn_eq_p4 (n : Nat) : p4turn n = p4 n := by
  apply Z0.mk.injEq.mpr
  constructor
  · rfl
  constructor
  · rfl
  · have h := alignOnesTurn (D n+1)
    have hk : K n+2 = A n := by simp [K,A]; omega
    have hb : D n+1 = B n := by simp [D,B]; omega
    rw [hk, hb] at *
    simpa [p4turn, p4, List.append_assoc] using
      congrArg
        (fun x : List Bool =>
          [false,false,false,false,false,true,false,true,true,false] ++ x ++
            rep [false,true,true] (A n) ++ [false,false,true,true]) h

theorem phase_p2_to_p4 (n : Nat) :
    run0 table (224*n+276) (p2raw n) = some (p4 n) := by
  have H := join0 (phase_middle n) (phase_p3_turn n)
  rw [p4turn_eq_p4 n] at H
  have hc : (224*n+260)+16 = 224*n+276 := by omega
  simpa only [hc] using H

theorem phase_final (n : Nat) :
    run0 table (136*n+204) (p4 n) = some (finalOut n) := by
  have h0 : run0 table 21 (p4 n) =
      some ⟨2,
        [true,true,false,true,true,false,false,true,false,true,true,false,true],
        rep [true,true] (B n) ++ [true] ++
          rep [false,true,true] (A n) ++ [false,false,true,true]⟩ := by
    simpa [p4, List.append_assoc] using
      preludeC
        (rep [true,true] (B n) ++ [true] ++
          rep [false,true,true] (A n) ++ [false,false,true,true])

  have h1 : run0 table (6*(B n))
      ⟨2,[true,true,false,true,true,false,false,true,false,true,true,false,true],
        rep [true,true] (B n) ++ [true] ++
          rep [false,true,true] (A n) ++ [false,false,true,true]⟩ =
      some ⟨2,
        [true] ++ rep [true,false] (B n) ++ cTail,
        [true] ++ rep [false,true,true] (A n) ++ [false,false,true,true]⟩ := by
    have h := sweepR table 2 [true] [] [true,true] [true,false] 6 right6C
      (B n) cTail
      ([true] ++ rep [false,true,true] (A n) ++ [false,false,true,true])
    simpa [cTail, List.append_assoc] using h

  have h2 : run0 table (3*(A n))
      ⟨2,[true] ++ rep [true,false] (B n) ++ cTail,
        [true] ++ rep [false,true,true] (A n) ++ [false,false,true,true]⟩ =
      some ⟨2,
        [true] ++ rep [true,false,true] (A n) ++
          rep [true,false] (B n) ++ cTail,
        [true,false,false,true,true]⟩ := by
    have h := sweepR table 2 [true] [] [true,false,true] [true,false,true] 3
      right3C (A n) (rep [true,false] (B n) ++ cTail)
      [true,false,false,true,true]
    rw [← rotateRightC n] at h
    simpa [List.append_assoc] using h

  have h3raw : run0 table 11
      ⟨2,[true] ++ rep [true,false,true] (A n) ++
          rep [true,false] (B n) ++ cTail,
        [true,false,false,true,true]⟩ =
      some ⟨4,
        [true,true,false,true] ++ rep [true,false,true] (A n) ++
          rep [true,false] (B n) ++ cTail,
        [false,true]⟩ := by
    simpa [List.append_assoc] using
      finishCE
        (rep [true,false,true] (A n) ++ rep [true,false] (B n) ++ cTail)
        []

  have h3 : run0 table 11
      ⟨2,[true] ++ rep [true,false,true] (A n) ++
          rep [true,false] (B n) ++ cTail,
        [true,false,false,true,true]⟩ =
      some ⟨4,
        [true] ++ rep [true,false,true] (A n + 2) ++
          rep [false,true] (B n) ++ eTail,
        [false,true]⟩ := by
    rw [← alignAfterCE (A n) (B n)]
    exact h3raw

  have h4 : run0 table (15*(A n+2))
      ⟨4,[true] ++ rep [true,false,true] (A n+2) ++
          rep [false,true] (B n) ++ eTail,[false,true]⟩ =
      some ⟨4,[true] ++ rep [false,true] (B n) ++ eTail,
        rep [false,true,true] (A n+2) ++ [false,true]⟩ := by
    have h := sweepL table 4 [true] [] [true,false,true] [false,true,true] 15
      left15 (A n+2) (rep [false,true] (B n) ++ eTail) [false,true]
    simpa [List.append_assoc] using h

  have h5 : run0 table (14*(B n))
      ⟨4,[true] ++ rep [false,true] (B n) ++ eTail,
        rep [false,true,true] (A n+2) ++ [false,true]⟩ =
      some ⟨4,[true] ++ eTail,
        [false] ++ rep [true,true] (B n) ++ [true,true] ++
          rep [false,true,true] (A n+1) ++ [false,true]⟩ := by
    have h := sweepL table 4 [true] [false] [false,true] [true,true] 14
      left14 (B n) eTail
      ([true,true] ++ rep [false,true,true] (A n+1) ++ [false,true])
    have ha : A n + 2 = (A n + 1) + 1 := by omega
    rw [ha] at *
    simpa [rep, List.append_assoc] using h

  have h5' : run0 table (14*(B n))
      ⟨4,[true] ++ rep [false,true] (B n) ++ eTail,
        rep [false,true,true] (A n+2) ++ [false,true]⟩ =
      some ⟨4,[true,true,false,false,true,false,true,true,false,true],
        [false,true,true] ++ rep [true,true] (B n) ++
          rep [false,true,true] (A n+1) ++ [false,true]⟩ := by
    rw [alignBeforeF (B n)
      (rep [false,true,true] (A n+1) ++ [false,true])] at h5
    simpa [eTail, List.append_assoc] using h5

  have h6 : run0 table 21
      ⟨4,[true,true,false,false,true,false,true,true,false,true],
        [false,true,true] ++ rep [true,true] (B n) ++
          rep [false,true,true] (A n+1) ++ [false,true]⟩ =
      some ⟨5,[true,true] ++ fTail,
        rep [true,true] (B n) ++
          rep [false,true,true] (A n+1) ++ [false,true]⟩ := by
    simpa [fTail, List.append_assoc] using
      preludeF [true,false,true,true,false,true]
        (rep [true,true] (B n) ++
          rep [false,true,true] (A n+1) ++ [false,true])

  have h7 : run0 table (6*(B n))
      ⟨5,[true,true] ++ fTail,
        rep [true,true] (B n) ++ rep [false,true,true] (A n+1) ++ [false,true]⟩ =
      some ⟨5,[true,true] ++ rep [true,false] (B n) ++ fTail,
        rep [false,true,true] (A n+1) ++ [false,true]⟩ := by
    have h := sweepR table 5 [true,true] [] [true,true] [true,false] 6 right6F
      (B n) fTail (rep [false,true,true] (A n+1) ++ [false,true])
    simpa [List.append_assoc] using h

  have h8 : run0 table (3*(A n+1))
      ⟨5,[true,true] ++ rep [true,false] (B n) ++ fTail,
        rep [false,true,true] (A n+1) ++ [false,true]⟩ =
      some ⟨5,[true] ++ rep [true,true,false] (A n+1) ++
          [true] ++ rep [true,false] (B n) ++ fTail,[false,true]⟩ := by
    have h := sweepR table 5 [true] [] [false,true,true] [true,true,false] 3
      right3F (A n+1) ([true] ++ rep [true,false] (B n) ++ fTail) [false,true]
    simpa [List.append_assoc] using h

  have h9 : run0 table 3
      ⟨5,[true] ++ rep [true,true,false] (A n+1) ++
          [true] ++ rep [true,false] (B n) ++ fTail,[false,true]⟩ =
      some (finalOut n) := by
    simpa [finalOut, List.append_assoc] using
      finish3
        (rep [true,true,false] (A n+1) ++
          [true] ++ rep [true,false] (B n) ++ fTail)

  have H := join0 h0
    (join0 h1
      (join0 h2
        (join0 h3
          (join0 h4
            (join0 h5'
              (join0 h6 (join0 h7 (join0 h8 h9))))))))
  have hc :
      21 + (6*(B n) + (3*(A n) + (11 + (15*(A n+2) +
        (14*(B n) + (21 + (6*(B n) + (3*(A n+1) + 3)))))))) =
        136*n+204 := by
    simp [A,B]
    omega
  simpa only [hc] using H

theorem phase_final_family (n : Nat) :
    run0 table (136*n+204) (p4 n) = some (family (n+1)) := by
  rw [← finalOut_eq_family_succ n]
  exact phase_final n

#print axioms phase_first_raw
#print axioms phase_middle_first
#print axioms phase_middle_second
#print axioms phase_p2_to_p4
#print axioms phase_to_p2raw
#print axioms phase_final
#print axioms phase_final_family
end BB6.Agent9Raw43B1LEE0LFM559
