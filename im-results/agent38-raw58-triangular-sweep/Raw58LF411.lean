import Raw58Live

namespace BB6.Agent38Raw58LF411
open BB6Coverage Agent31Pump Agent50Zipper Agent4Live
set_option maxRecDepth 100000
set_option maxHeartbeats 0

/-- The unresolved Raw58 LF leaf 411. Its only undefined transition is E0. -/
def raw58LF411 : PartialMachine := fun s =>
  match s.1.val, s.2 with
  | 0, false => some (some ⟨true,true,1⟩)
  | 0, true  => some (some ⟨false,false,5⟩)
  | 1, false => some (some ⟨true,true,2⟩)
  | 1, true  => some (some ⟨false,true,0⟩)
  | 2, false => some (some ⟨false,true,3⟩)
  | 2, true  => some (some ⟨false,true,1⟩)
  | 3, false => some (some ⟨true,false,3⟩)
  | 3, true  => some (some ⟨true,true,4⟩)
  | 4, false => none
  | 4, true  => some (some ⟨false,true,0⟩)
  | 5, false => some (some ⟨true,false,0⟩)
  | 5, true  => some (some ⟨true,false,1⟩)
  | _, _ => none

/-- C(j,t): state C, current 0, with an alternating left-stack marker.
The left list is nearest-first, as in Agent31Pump.Z0. -/
def C (j t : Nat) : Z0 :=
  ⟨2, [false,true] ++ rep [false,true] (2*t) ++ [true] ++ rep [false,true] j, []⟩

lemma rep_add (w : List Bool) (m n : Nat) :
    rep w (m+n) = rep w m ++ rep w n := by
  induction m with
  | zero => simp [rep]
  | succ m ih =>
      simp [rep, ih, Nat.succ_add, List.append_assoc]

lemma alt_even (n : Nat) :
    [false,true] ++ rep [false,true] (2*n) ++ [true] =
      [false] ++ rep [true,false] (2*n) ++ [true,true] := by
  induction n with
  | zero => rfl
  | succ n ih =>
      calc
        [false,true] ++ rep [false,true] (2*(n+1)) ++ [true]
            = [false,true] ++ [false,true] ++
                ([false,true] ++ rep [false,true] (2*n) ++ [true]) := by
                  simp [rep, Nat.mul_succ, List.append_assoc]
        _ = [false,true] ++ [false,true] ++
                ([false] ++ rep [true,false] (2*n) ++ [true,true]) := by rw [ih]
        _ = [false] ++ rep [true,false] (2*(n+1)) ++ [true,true] := by
                  simp [rep, Nat.mul_succ, List.append_assoc]

lemma rep10_of_rep01 (n : Nat) :
    [true] ++ rep [false,true] n ++ [false] = rep [true,false] (n+1) := by
  induction n with
  | zero => rfl
  | succ n ih =>
      calc
        [true] ++ rep [false,true] (n+1) ++ [false]
            = [true,false] ++
                ([true] ++ rep [false,true] n ++ [false]) := by
                  simp [rep, List.append_assoc]
        _ = [true,false] ++ rep [true,false] (n+1) := by rw [ih]
        _ = rep [true,false] (n+2) := by rfl

/-! The four two-step sweeps used by both macros. -/

lemma sweep_A_left (L R : List Bool) :
    run0 raw58LF411 2 ⟨0, [true,false] ++ L, R⟩ =
      some ⟨0, L, [true,false] ++ R⟩ := by
  rfl

lemma sweep_F_left (L R : List Bool) :
    run0 raw58LF411 2 ⟨5, [false,true] ++ L, R⟩ =
      some ⟨5, L, [false,true] ++ R⟩ := by
  rfl

lemma sweep_B_right (L R : List Bool) :
    run0 raw58LF411 2 ⟨1, [false] ++ L, [true,false] ++ R⟩ =
      some ⟨1, [false] ++ [false,true] ++ L, R⟩ := by
  rfl

lemma sweep_A_right (L R : List Bool) :
    run0 raw58LF411 2 ⟨0, [false] ++ L, [true,false] ++ R⟩ =
      some ⟨0, [false] ++ [false,true] ++ L, R⟩ := by
  rfl

/-- Fourteen-step entry into the F-left sweep, valid once t≥2. -/
lemma inner_pre (j t : Nat) (ht : 2 ≤ t) :
    run0 raw58LF411 14 (C (j+1) t) =
      some ⟨5,
        rep [false,true] (2*t-3) ++ [true,false,true] ++ rep [false,true] j,
        rep [false,true] 4 ++ [false]⟩ := by
  have hnum : 2*t+1 = 4 + (2*t-3) := by omega
  have hsplit :
      [false,true] ++ rep [false,true] (2*t) =
        rep [false,true] 4 ++ rep [false,true] (2*t-3) := by
    calc
      [false,true] ++ rep [false,true] (2*t)
          = rep [false,true] (2*t+1) := by rfl
      _ = rep [false,true] (4+(2*t-3)) := by rw [hnum]
      _ = rep [false,true] 4 ++ rep [false,true] (2*t-3) :=
        rep_add [false,true] 4 (2*t-3)
  rw [C, hsplit]
  rfl

lemma inner_zero (j : Nat) :
    run0 raw58LF411 14 (C (j+1) 0) = some (C j 1) := by
  rfl

lemma inner_one (j : Nat) :
    run0 raw58LF411 22 (C (j+1) 1) = some (C j 2) := by
  rfl

/-- One inner counter tick: move the 11 defect one block left and add
two alternating blocks at the near end. -/
theorem inner (j t : Nat) :
    run0 raw58LF411 (8*t+14) (C (j+1) t) = some (C j (t+1)) := by
  by_cases h0 : t = 0
  · subst t
    simpa using inner_zero j
  by_cases h1 : t = 1
  · subst t
    simpa using inner_one j
  have ht : 2 ≤ t := by omega
  have hpre := inner_pre j t ht
  have hF := sweepL raw58LF411 5 [] [] [false,true] [false,true] 2
    (by intro L R; exact sweep_F_left L R) (2*t-3)
    ([true,false,true] ++ rep [false,true] j)
    (rep [false,true] 4 ++ [false])
  have hrep :
      rep [false,true] (2*t-3) ++ rep [false,true] 4 =
        rep [false,true] (2*t+1) := by
    calc
      rep [false,true] (2*t-3) ++ rep [false,true] 4
          = rep [false,true] ((2*t-3)+4) := by
              rw [← rep_add]
      _ = rep [false,true] (2*t+1) := by congr 1 <;> omega
  have hF1 :
      run0 raw58LF411 1
        ⟨5, [true,false,true] ++ rep [false,true] j,
          rep [false,true] (2*t-3) ++ (rep [false,true] 4 ++ [false])⟩ =
        some ⟨1, [false,true] ++ rep [false,true] j,
          rep [true,false] (2*t+2)⟩ := by
    rw [← List.append_assoc, hrep]
    rw [← rep10_of_rep01 (2*t+1)]
    rfl
  have hB := sweepR raw58LF411 1 [false] [] [true,false] [false,true] 2
    (by intro L R; exact sweep_B_right L R) (2*t+2)
    ([true] ++ rep [false,true] j) []
  have hB0 :
      run0 raw58LF411 1
        ⟨1, [false] ++ rep [false,true] (2*t+2) ++ [true] ++ rep [false,true] j, []⟩ =
        some (C j (t+1)) := by
    rfl
  have hcomp := join0 (join0 (join0 (join0 hpre hF) hF1) hB) hB0
  have htime : 14 + 2*(2*t-3) + 1 + 2*(2*t+2) + 1 = 8*t+14 := by omega
  simpa [htime] using hcomp

/-- The five-step reset prelude at C(0,k). -/
lemma reset_pre (k : Nat) :
    run0 raw58LF411 5 (C 0 k) =
      some ⟨0, rep [true,false] (2*k+1) ++ [true,true], []⟩ := by
  rw [C, alt_even]
  rfl

/-- Reset the inner sweep counter: C(0,k) grows to C(2k+4,0). -/
theorem reset (k : Nat) :
    run0 raw58LF411 (16*k+37) (C 0 k) = some (C (2*k+4) 0) := by
  have hpre := reset_pre k
  have hA := sweepL raw58LF411 0 [] [] [true,false] [true,false] 2
    (by intro L R; exact sweep_A_left L R) (2*k+1) [true,true] []
  have hA2 :
      run0 raw58LF411 2
        ⟨0, [true,true], rep [true,false] (2*k+1)⟩ =
        some ⟨1, [], rep [true,false] (2*k+2)⟩ := by
    rfl
  have hB := sweepR raw58LF411 1 [false] [] [true,false] [false,true] 2
    (by intro L R; exact sweep_B_right L R) (2*k+2) [] []
  have hB6 :
      run0 raw58LF411 6
        ⟨1, [false] ++ rep [false,true] (2*k+2), []⟩ =
        some ⟨0, rep [true,false] (2*k+3) ++ [true], []⟩ := by
    rfl
  have hA2s := sweepL raw58LF411 0 [] [] [true,false] [true,false] 2
    (by intro L R; exact sweep_A_left L R) (2*k+3) [true] []
  have hA2tail :
      run0 raw58LF411 2
        ⟨0, [true], rep [true,false] (2*k+3)⟩ =
        some ⟨0, [], rep [true,false] (2*k+4)⟩ := by
    rfl
  have hAr := sweepR raw58LF411 0 [false] [] [true,false] [false,true] 2
    (by intro L R; exact sweep_A_right L R) (2*k+4) [] []
  have hAfinal :
      run0 raw58LF411 2
        ⟨0, [false] ++ rep [false,true] (2*k+4), []⟩ =
        some (C (2*k+4) 0) := by
    rfl
  have hcomp := join0 (join0 (join0 (join0 (join0 (join0 (join0 hpre hA) hA2) hB) hB6) hA2s) hA2tail) hAr
  have hcomp' := join0 hcomp hAfinal
  have htime :
      5 + 2*(2*k+1) + 2 + 2*(2*k+2) + 6 +
        2*(2*k+3) + 2 + 2*(2*k+4) + 2 = 16*k+37 := by omega
  simpa [htime] using hcomp'

/-- Drain j inner ticks, transferring C(j,t) to C(0,t+j). -/
def drainTime : Nat → Nat → Nat
  | 0, t => 0
  | j+1, t => (8*t+14) + drainTime j (t+1)

theorem drain (j t : Nat) :
    run0 raw58LF411 (drainTime j t) (C j t) =
      some (C 0 (t+j)) := by
  induction j generalizing t with
  | zero =>
      simp [drainTime, C, run0]
  | succ j ih =>
      have hfirst := inner j t
      have htail := ih (t+1)
      have hcomp := join0 hfirst htail
      have hindex : t + (1+j) = t + (j+1) := by omega
      rw [hindex]
      simpa [drainTime, Nat.add_assoc] using hcomp

/-- A complete growth cycle C(k,0) -> C(2k+4,0). -/
def cycleTime (k : Nat) : Nat := drainTime k 0 + (16*k+37)

theorem grow (k : Nat) :
    run0 raw58LF411 (cycleTime k) (C k 0) =
      some (C (2*k+4) 0) := by
  have hcomp := join0 (drain k 0) (reset k)
  simpa [cycleTime, Nat.zero_add] using hcomp

def index : Nat → Nat
  | 0 => 4
  | n+1 => 2*index n + 4

def elapsed : Nat → Nat
  | 0 => 39
  | n+1 => elapsed n + cycleTime (index n)

theorem iter_run (n : Nat) :
    run0 raw58LF411 (elapsed n) ⟨0, [], []⟩ =
      some (C (index n) 0) := by
  induction n with
  | zero =>
      simpa [elapsed, index] using entry
  | succ n ih =>
      have hcomp := join0 ih (grow (index n))
      simpa [elapsed, index, cycleTime] using hcomp

theorem elapsed_ge (n : Nat) : n ≤ elapsed n := by
  induction n with
  | zero => simp [elapsed]
  | succ n ih =>
      have hpos : 1 ≤ cycleTime (index n) := by
        unfold cycleTime
        omega
      simp only [elapsed]
      omega

/-- Repeated growth gives arbitrarily long finite live prefixes. -/
theorem long (n : Nat) :
    ∃ t, n ≤ t ∧ run0 raw58LF411 t ⟨0, [], []⟩ =
      some (C (index n) 0) := by
  exact ⟨elapsed n, elapsed_ge n, iter_run n⟩

theorem arbitrary : ∀ n : Nat, ∃ t z, n ≤ t ∧ run0 raw58LF411 t ⟨0, [], []⟩ = some z := by
  intro n
  obtain ⟨t, ht, hrun⟩ := long n
  exact ⟨t, C (index n) 0, ht, hrun⟩

/-- The 411 LF leaf cannot halt in any completion of its partial table. -/
theorem never (m : Machine) (hm : compatible raw58LF411 m) : NeverHalts m :=
  Agent4Live.never_of_live raw58LF411 arbitrary m hm

#print axioms never
end BB6.Agent38Raw58LF411
