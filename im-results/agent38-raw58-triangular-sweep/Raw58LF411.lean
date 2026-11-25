import Raw58Live

namespace BB6.Agent38Raw58LF411
open BB6Coverage Agent31Pump Agent50Zipper Agent4Live
set_option maxRecDepth 100000
set_option maxHeartbeats 0

/-- The unresolved Raw58 LF leaf 411. Its only undefined transition is E0. -/
def raw58LF411 : PartialMachine := fun s =>
  match s.1.val, s.2 with
  | 0, false => some ⟨true, Dir.R, ⟨1⟩⟩
  | 0, true  => some ⟨false, Dir.L, ⟨5⟩⟩
  | 1, false => some ⟨true, Dir.R, ⟨2⟩⟩
  | 1, true  => some ⟨false, Dir.R, ⟨0⟩⟩
  | 2, false => some ⟨false, Dir.R, ⟨3⟩⟩
  | 2, true  => some ⟨false, Dir.R, ⟨1⟩⟩
  | 3, false => some ⟨true, Dir.L, ⟨3⟩⟩
  | 3, true  => some ⟨true, Dir.R, ⟨4⟩⟩
  | 4, false => none
  | 4, true  => some ⟨false, Dir.R, ⟨0⟩⟩
  | 5, false => some ⟨true, Dir.L, ⟨0⟩⟩
  | 5, true  => some ⟨true, Dir.L, ⟨1⟩⟩

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
      simp [rep, Nat.mul_succ, ih, List.append_assoc]

lemma rep10_of_rep01 (n : Nat) :
    [true] ++ rep [false,true] n ++ [false] = rep [true,false] (n+1) := by
  induction n with
  | zero => rfl
  | succ n ih =>
      simp [rep, ih, List.append_assoc]

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
  have hnum : 1 + 2*t = 4 + (2*t-3) := by omega
  have hsplit :
      [false,true] ++ rep [false,true] (2*t) =
        rep [false,true] 4 ++ rep [false,true] (2*t-3) := by
    calc
      [false,true] ++ rep [false,true] (2*t)
          = rep [false,true] (1+2*t) := by simp [rep]
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
  have hF1 :
      run0 raw58LF411 1
        ⟨5, [true,false,true] ++ rep [false,true] j,
          rep [false,true] (2*t+1) ++ [false]⟩ =
        some ⟨1, [false,true] ++ rep [false,true] j,
          rep [true,false] (2*t+2)⟩ := by
    have h := rep10_of_rep01 (2*t+1)
    rw [← h]
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
theorem drain (j t : Nat) :
    run0 raw58LF411 (8*j*t + 4*j*j + 10*j) (C j t) =
      some (C 0 (t+j)) := by
  induction j generalizing t with
  | zero =>
      simp [C, run0]
  | succ j ih =>
      have hfirst := inner j t
      have htail := ih (t+1)
      have hcomp := join0 hfirst htail
      have htime :
          (8*t+14) + (8*j*(t+1) + 4*j*j + 10*j) =
            8*(j+1)*t + 4*(j+1)*(j+1) + 10*(j+1) := by omega
      simpa [htime, Nat.mul_add, Nat.add_mul, Nat.add_assoc, Nat.add_left_comm,
        Nat.add_comm] using hcomp

/-- A complete growth cycle C(k,0) -> C(2k+4,0). -/
theorem grow (k : Nat) :
    run0 raw58LF411 (4*k*k + 26*k + 37) (C k 0) =
      some (C (2*k+4) 0) := by
  have hdrain := drain k 0
  have hreset := reset k
  have hcomp := join0 hdrain hreset
  have htime :
      (8*k*0 + 4*k*k + 10*k) + (16*k+37) = 4*k*k+26*k+37 := by omega
  simpa [htime] using hcomp

/-- The blank run reaches the first C-counter state. -/
theorem entry :
    run0 raw58LF411 39 ⟨0, [], []⟩ = some (C 4 0) := by
  rfl

def index : Nat → Nat
  | 0 => 4
  | n+1 => 2*index n + 4

/-- Repeated growth gives arbitrarily long finite live prefixes. -/
theorem long (n : Nat) :
    ∃ t, n ≤ t ∧ run0 raw58LF411 t ⟨0, [], []⟩ =
      some (C (index n) 0) := by
  induction n with
  | zero =>
      exact ⟨39, by omega, entry⟩
  | succ n ih =>
      obtain ⟨t, ht, hrun⟩ := ih
      have hgrow := grow (index n)
      refine ⟨t + (4*(index n)*(index n) + 26*(index n) + 37), ?_, ?_⟩
      · omega
      · have hjoin := join0 hrun hgrow
        simpa [index, Nat.mul_assoc, Nat.mul_left_comm, Nat.mul_comm,
          Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using hjoin

theorem arbitrary : Arbitrary raw58LF411 := by
  intro n
  obtain ⟨t, ht, hrun⟩ := long n
  exact ⟨t, C (index n) 0, ht, hrun⟩

/-- The 411 LF leaf cannot halt in any completion of its partial table. -/
theorem never (m : Machine) (hm : compatible raw58LF411 m) : NeverHalts m :=
  never_of_live raw58LF411 arbitrary m hm

#print axioms never
end BB6.Agent38Raw58LF411
