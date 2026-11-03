/-
Machine: 1RB1LA_1RC0RF_1RD---_0LE1RB_---0LA_1LD1RF
Two-mode abstract stack rules transcribed from
google-deepmind/cryptids BusyBeaver/BB6/Accelerations/
M_1RB1LA_1RC0RF_1RDHHH_0LE1RB_HHH0LA_1LD1RF.lean (November 2026 access).
This standalone proof imports no original DeepMind module. It is a
copy-of-rules theorem, not yet an original-source-connected theorem.
-/
import Lean
import Lean.Elab.Tactic.Omega

namespace Agent15Stack

inductive Mode | D | FR deriving DecidableEq, Repr
abbrev Cfg := Mode × List Nat × List Nat

def bump : List Nat → List Nat
  | [] => [0]
  | a :: s => (a + 1) :: s

def bumpN : Nat → List Nat → List Nat
  | 0, s => s
  | n+1, s => bumpN n (bump s)

def top : List Nat → Nat
  | [] => 0
  | a :: _ => a

def nxt : Cfg → Option Cfg
  | (.D, [], _) => none
  | (.D, a :: L, R) =>
    match a with
    | 0 =>
      match R with
      | [] => some (.D, bumpN 3 L, [])
      | 0 :: [] => some (.D, bumpN 6 L, [])
      | 0 :: _ :: _ => none
      | 1 :: T => some (.D, bumpN 4 L, bump T)
      | (d+2) :: T => some (.FR, d :: bumpN 4 L, bump T)
    | 1 => some (.D, bump L, 0 :: R)
    | a+2 => some (.FR, a :: bump L, 0 :: R)
  | (.FR, [], R) => some (.D, [], top R :: R.tail)
  | (.FR, (a :: L), R) =>
    match R with
    | [] => some (.D, a :: L, [0])
    | 0 :: T => some (.D, a :: L, bump T)
    | (d+1) :: T => some (.FR, d :: a :: L, bump T)

#eval nxt (.D,[2],[])
#eval nxt (.D,[0,0],[0])
#eval nxt (.D,[1],[0,0])
#eval nxt (.D,[0],[0,0,0])

/-- Every successful incoming edge to the immediate C1-halt predecessor
    has this single shape: the previous D left stack was [1]. -/
theorem only_bad_parent (s : Cfg) (L : List Nat) (e : Nat) (R : List Nat)
    (h : nxt s = some (.D, 0 :: L, 0 :: e :: R)) :
    s = (.D, [1], e :: R) := by
  rcases s with ⟨m, xs, ys⟩
  cases m with
  | D =>
    cases xs with
    | nil => simp [nxt] at h
    | cons a xs =>
      rcases a with _ | _ | a
      · cases ys with
        | nil => simp [nxt, bumpN, bump] at h
        | cons d ds =>
          rcases d with _ | _ | d
          · cases ds with
            | nil => simp [nxt, bumpN, bump] at h
            | cons x tail => simp [nxt] at h
          · cases xs with
            | nil => simp [nxt, bumpN, bump] at h
            | cons x tail => simp [nxt, bumpN, bump] at h
          · simp [nxt] at h
      · cases xs with
        | nil =>
          simp [nxt, bump] at h
          simp_all
        | cons x xs => simp [nxt, bump] at h
      · simp [nxt] at h
  | FR =>
    cases xs with
    | nil => simp [nxt] at h
    | cons x xs =>
      cases ys with
      | nil => simp [nxt] at h
      | cons y ys =>
        rcases y with _ | y
        · cases ys with
          | nil => simp [nxt, bump] at h
          | cons z zs => simp [nxt, bump] at h
        · simp [nxt] at h

theorem bump_nonempty (L : List Nat) : bump L ≠ [] := by
  cases L <;> simp [bump]

theorem bumpN_succ_nonempty (n : Nat) (L : List Nat) : bumpN (n+1) L ≠ [] := by
  induction n generalizing L with
  | zero => simpa [bumpN] using bump_nonempty L
  | succ n ih => simpa [bumpN] using ih (bump L)

theorem next_left_nonempty (m : Mode) (a : Nat) (L R : List Nat) (t : Cfg)
    (h : nxt (m, a :: L, R) = some t) : t.2.1 ≠ [] := by
  cases m with
  | D =>
    rcases a with _ | _ | a
    · cases R with
      | nil => simp [nxt,bumpN,bump] at h; cases h; exact bumpN_succ_nonempty 2 L
      | cons r rs =>
        rcases r with _ | _ | r
        · cases rs with
          | nil => simp [nxt,bumpN,bump] at h; cases h; exact bumpN_succ_nonempty 5 L
          | cons r rs => simp [nxt] at h
        · simp [nxt] at h; cases h; exact bumpN_succ_nonempty 3 L
        · simp [nxt] at h; cases h; simp
    · simp [nxt] at h; cases h; exact bump_nonempty L
    · simp [nxt] at h; cases h; simp
  | FR =>
    cases R with
    | nil => simp [nxt] at h; cases h; simp
    | cons r rs =>
      rcases r with _ | r
      · simp [nxt] at h; cases h; simp
      · simp [nxt] at h; cases h; simp

def run : Nat → Option Cfg
  | 0 => some (.D, [2], [])
  | n+1 => (run n).bind nxt

theorem run_left_nonempty (n : Nat) (s : Cfg)
    (h : run n = some s) : s.2.1 ≠ [] := by
  induction n generalizing s with
  | zero =>
    simp [run] at h
    cases h
    decide
  | succ n ih =>
    cases hr : run n with
    | none => simp [run, hr] at h
    | some p =>
      rcases p with ⟨m, L, R⟩
      have hp : L ≠ [] := ih (m,L,R) hr
      cases L with
      | nil => simp at hp
      | cons a L =>
        have hn : nxt (m,a::L,R)=some s := by simpa [run,hr] using h
        exact next_left_nonempty m a L R s hn

theorem next_none_source (m : Mode) (a : Nat) (L R : List Nat)
    (h : nxt (m, a :: L, R) = none) :
    m = .D ∧ a = 0 ∧ ∃ e T, R = 0 :: e :: T := by
  cases m with
  | D =>
    rcases a with _ | _ | a
    · cases R with
      | nil => simp [nxt] at h
      | cons r rs =>
        rcases r with _ | _ | r
        · cases rs with
          | nil => simp [nxt] at h
          | cons e T => exact ⟨rfl, rfl, e, T, rfl⟩
        · simp [nxt] at h
        · simp [nxt] at h
    · simp [nxt] at h
    · simp [nxt] at h
  | FR =>
    cases R with
    | nil => simp [nxt] at h
    | cons r rs =>
      cases r with
      | zero => simp [nxt] at h
      | succ r => simp [nxt] at h

theorem bad_reachable_feeder (n : Nat) (L : List Nat) (e : Nat) (R : List Nat)
    (h : run n = some (.D, 0 :: L, 0 :: e :: R)) :
    ∃ k, k < n ∧ run k = some (.D, [1], e :: R) := by
  cases n with
  | zero => simp [run] at h
  | succ n =>
    cases hr : run n with
    | none => simp [run,hr] at h
    | some p =>
      have hn : nxt p = some (.D, 0 :: L, 0 :: e :: R) := by
        simpa [run, hr] using h
      have hp := only_bad_parent p L e R hn
      exact ⟨n, by omega, by simpa [hp] using hr⟩

theorem run_none_feeder (n : Nat) (h : run n = none) :
    ∃ k, k < n ∧ ∃ e R, run k = some (.D, [1], e :: R) := by
  induction n with
  | zero => simp [run] at h
  | succ n ih =>
    cases hr : run n with
    | none =>
      obtain ⟨k,hkn,e,R,hk⟩ := ih hr
      exact ⟨k, by omega, e, R, hk⟩
    | some p =>
      rcases p with ⟨m,L,R⟩
      have hp : L ≠ [] := run_left_nonempty n (m,L,R) hr
      cases L with
      | nil => contradiction
      | cons a L =>
        have hn : nxt (m,a::L,R) = none := by simpa [run,hr] using h
        obtain ⟨rfl,rfl,e,T,rfl⟩ := next_none_source m a L R hn
        obtain ⟨k,hkn,hk⟩ := bad_reachable_feeder n L e T hr
        exact ⟨k, by omega, e, T, hk⟩

theorem feeder_halts (n e : Nat) (R : List Nat)
    (h : run n = some (.D, [1], e :: R)) : run (n+2) = none := by
  simp [run, h, nxt, bump]

/-- All-time exact halt condition of the copied two-mode macro system.
    Establishing equivalence to the unchanged external original module
    remains a separate source-connection obligation. -/
theorem blank_halts_iff_singleton_feeder :
    (∃ n, run n = none) ↔
      (∃ n e R, run n = some (.D, [1], e :: R)) := by
  constructor
  · rintro ⟨n,h⟩
    obtain ⟨k,_,e,R,hk⟩ := run_none_feeder n h
    exact ⟨k,e,R,hk⟩
  · rintro ⟨n,e,R,h⟩
    exact ⟨n+2, feeder_halts n e R h⟩

#print axioms only_bad_parent
#print axioms run_left_nonempty
#print axioms blank_halts_iff_singleton_feeder

end Agent15Stack
