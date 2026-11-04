import S4PowerGate
import Lean.Elab.Tactic.Omega

namespace S4Octet

open S4Power

/-- A single odd carry drain starting with a fixed additive head. -/
def G (c : Nat) : List Nat → Option (List Nat)
  | [] => H (c-1) []
  | b::S => H (b+c) S

theorem G_none_iff_power (c : Nat) (R : List Nat) (hc : 0<c) :
    G c R = none ↔ Pow2 (W R+c) := by
  cases R with
  | nil =>
      change H (c-1) [] = none ↔ Pow2 (W []+c)
      rw [H_none_iff_pow2]
      have h : c-1+1+2*W [] = W []+c := by simp [W]; omega
      rw [h]
  | cons b S =>
      change H (b+c) S = none ↔ Pow2 (W (b::S)+c)
      rw [H_none_iff_pow2]
      have h : b+c+1+2*W S = W (b::S)+c := by simp [W]; omega
      rw [h]

def bumpN (k : Nat) : List Nat → List Nat
  | [] => [k-1]
  | b::S => (b+k)::S

def Q (R : List Nat) : Option (List Nat) :=
  (G 107 R).bind (fun U => (G 148 U).map (bumpN 253))

theorem Q_none_iff_two_gates (R : List Nat) :
    Q R = none ↔
    Pow2 (W R+107) ∨
    ∃ U, G 107 R = some U ∧ Pow2 (W U+148) := by
  constructor
  · intro hq
    cases h107 : G 107 R with
    | none =>
        exact Or.inl ((G_none_iff_power 107 R (by omega)).mp h107)
    | some U =>
        have h148 : G 148 U = none := by
          unfold Q at hq
          simp only [h107, Option.bind_some, Option.map_eq_none_iff] at hq
          exact hq
        exact Or.inr ⟨U,rfl,(G_none_iff_power 148 U (by omega)).mp h148⟩
  · rintro (hfirst | ⟨U,hU,hsecond⟩)
    · have h107 := (G_none_iff_power 107 R (by omega)).mpr hfirst
      simp [Q,h107]
    · have h148 := (G_none_iff_power 148 U (by omega)).mpr hsecond
      simp [Q,hU,h148]

def run : Nat → List Nat → Option (List Nat)
  | 0, T => some T
  | n+1, T => (run n T).bind F

private theorem H213 (R : List Nat) :
  H 213 R = (G 107 R).map (106::·) := by
  cases R <;> simp [H,G]

private theorem H295 (R : List Nat) :
  H 295 R = (G 148 R).map (147::·) := by
  cases R <;> simp [H,G]

set_option maxHeartbeats 0

theorem step_4 (R : List Nat) :
  F (80::150::R) = (G 107 R).map (fun U => 79::106::U) := by
  rw [F]
  change (H 125 (150::R)).map bump17 = _
  rw [show H 125 (150::R) = (H 213 R).map (62::·) by simp [H], H213]
  simp [Option.map_map,Function.comp_def,bump17]

theorem step_7 (R : List Nat) :
  F (82::231::R) = (G 148 R).map (fun U => 80::147::U) := by
  rw [F]
  change (H 127 (231::R)).map bump17 = _
  rw [show H 127 (231::R) = (H 295 R).map (63::·) by simp [H], H295]
  simp [Option.map_map,Function.comp_def,bump17]

theorem safe_5 (R : List Nat) : F (79::106::R) = some (81::168::R) := by simp [F,H,bump17]
theorem safe_6 (R : List Nat) : F (81::168::R) = some (82::231::R) := by simp [F,H,bump17]
theorem safe_0 (R : List Nat) :
  F (80::147::R) = some (79::107::bumpN 105 R) := by
  cases R <;> simp [F,H,bump17,bumpN]
theorem safe_1 (R : List Nat) : F (79::107::R) = some (81::169::R) := by simp [F,H,bump17]
theorem safe_2 (R : List Nat) : F (81::169::R) = some (82::232::R) := by simp [F,H,bump17]
theorem safe_3 (R : List Nat) :
  F (82::232::R) = some (80::150::bumpN 148 R) := by
  cases R <;> simp [F,H,bump17,bumpN]

theorem bump_add (R : List Nat) :
  bumpN 148 (bumpN 105 R) = bumpN 253 R := by
  cases R with
  | nil => rfl
  | cons b S =>
      simp [bumpN]

theorem eight (R : List Nat) :
    run 8 (80::150::R) = (Q R).map (fun U => 80::150::U) := by
  cases h107 : G 107 R with
  | none =>
      simp [run,Q,h107,step_4]
  | some U =>
      cases h148 : G 148 U with
      | none =>
          simp [run,Q,h107,h148,step_4,step_7,safe_5,safe_6]
      | some V =>
          simp [run,Q,h107,h148,step_4,step_7,safe_5,safe_6,
            safe_0,safe_1,safe_2,safe_3,bump_add]

def qrun : Nat → List Nat → Option (List Nat)
  | 0, R => some R
  | n+1, R => (qrun n R).bind Q

theorem run_add (n k : Nat) (T : List Nat) :
    run (n+k) T = (run n T).bind (run k) := by
  induction k with
  | zero => simp [run]
  | succ k ih =>
      rw [Nat.add_succ]
      simp only [run,ih]
      cases h : run n T with
      | none => simp [h]
      | some U => simp [h,run]

theorem run_none_after (T : List Nat) (k j : Nat)
    (h : run k T = none) : run (k+j) T = none := by
  rw [run_add,h]
  rfl

theorem octet_conjugacy (n : Nat) (T : List Nat) :
    run (8*n) (80::150::T) =
    (qrun n T).map (fun U => 80::150::U) := by
  induction n with
  | zero => simp [run,qrun]
  | succ n ih =>
      rw [show 8*(n+1)=8*n+8 by omega,run_add,ih]
      cases h : qrun n T with
      | none => simp [qrun,h]
      | some U =>
          simp only [h, Option.map_some,Option.bind_some]
          rw [eight]
          simp [qrun,h]

set_option maxRecDepth 5000 in
theorem first13 :
    run 13 [42,12,8,5] = some [80,150,481,133,28,25] := by
  simp [run, F, H, bump17]

theorem halt_iff_qrun :
    (∃ k, run k [42,12,8,5] = none) ↔
    (∃ n, qrun n [481,133,28,25] = none) := by
  constructor
  · rintro ⟨k,hk⟩
    let n := k+1
    have hlong : run (13+8*n) [42,12,8,5] = none := by
      have heq : k+(13+8*n-k)=13+8*n := by dsimp [n]; omega
      rw [← heq]
      exact run_none_after [42,12,8,5] k (13+8*n-k) hk
    have hbridge : run (13+8*n) [42,12,8,5] =
        (qrun n [481,133,28,25]).map (fun U => 80::150::U) := by
      rw [run_add,first13]
      simp only [Option.bind_some]
      exact octet_conjugacy n [481,133,28,25]
    rw [hbridge] at hlong
    cases hn : qrun n [481,133,28,25] with
    | none => exact ⟨n,hn⟩
    | some U => simp [hn] at hlong
  · rintro ⟨n,hn⟩
    refine ⟨13+8*n, ?_⟩
    rw [run_add,first13]
    simp [octet_conjugacy,hn]

#print axioms G_none_iff_power
#print axioms Q_none_iff_two_gates
#print axioms halt_iff_qrun
#print axioms octet_conjugacy
#print axioms eight
#print axioms step_4
#print axioms step_7
end S4Octet
