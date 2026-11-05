import S4Octet
import Lean.Elab.Tactic.Omega

namespace S4Toggle
open S4Power S4Octet

private theorem first471 (S : List Nat) :
    G 107 (471::S)=some (291::bumpN 289 S) := by
  cases S with
  | nil => simp [G,H,bumpN]
  | cons b T => simp [G,H,bumpN]

private theorem second471 (S : List Nat) :
    G 148 (291::bumpN 289 S) = (G 509 S).map (219::·) := by
  cases S with
  | nil => simp [G,H,bumpN]
  | cons b T => simp [G,H,bumpN]

private theorem first472 (S : List Nat) :
    G 107 (472::S) = (G 290 S).map (289::·) := by
  cases S with
  | nil => simp [G,H,bumpN]
  | cons b T => simp [G,H]

private theorem second472 (U : List Nat) :
    G 148 (289::U) = (G 219 U).map (218::·) := by
  cases U with
  | nil => simp [G,H,bumpN]
  | cons b T => simp [G,H]

set_option maxHeartbeats 0

theorem toggle471 (S : List Nat) :
    Q (471::S) = (G 509 S).map (472::·) := by
  simp only [Q, first471, Option.bind_some, second471]
  cases h : G 509 S with
  | none => simp [h]
  | some V => simp [h, bumpN]

theorem toggle472 (S : List Nat) :
    Q (472::S) = (G 290 S).bind (fun U => (G 219 U).map (471::·)) := by
  cases h : G 290 S with
  | none => simp [Q, first472, h]
  | some U =>
    cases h2 : G 219 U with
    | none => simp [Q, first472, second472, h, h2]
    | some V => simp [Q, first472, second472, h, h2, bumpN]

/-- Triple odd-drain map in the stable two-period. -/
def P (S : List Nat) : Option (List Nat) :=
  (G 509 S).bind (fun U => (G 290 U).bind (G 219))

theorem twoStep (S : List Nat) :
    (Q (471::S)).bind Q = (P S).map (471::·) := by
  rw [toggle471]
  cases h : G 509 S with
  | none => simp [P,h]
  | some U => simp [P,h,toggle472,Function.comp_def]

def prun : Nat → List Nat → Option (List Nat)
  | 0, S => some S
  | n+1, S => (prun n S).bind P

private theorem qrun_add (n k : Nat) (S : List Nat) :
    qrun (n+k) S = (qrun n S).bind (qrun k) := by
  induction k with
  | zero => simp [qrun]
  | succ k ih =>
      rw [Nat.add_succ]
      simp only [qrun, ih]
      cases h : qrun n S with
      | none => simp [h, qrun]
      | some U => simp [h, qrun]

theorem qrun_two (S : List Nat) :
    qrun 2 (471::S) = (P S).map (471::·) := by
  change (Q (471::S)).bind Q = _
  exact twoStep S

private theorem qrun_twice (n : Nat) (S : List Nat) :
    qrun (2*n) (471::S) = (prun n S).map (471::·) := by
  induction n with
  | zero => rfl
  | succ n ih =>
      rw [show 2*(n+1) = 2*n+2 by omega, qrun_add, ih]
      cases h : prun n S with
      | none => simp [prun,h]
      | some U =>
          simp only [h, Option.map_some, Option.bind_some]
          rw [qrun_two]
          simp [prun,h]

private theorem first4 :
    qrun 4 [481,133,28,25] = some (471::[301,650,645,322,163,160]) := by
  set_option maxRecDepth 10000 in
    simp [qrun,Q,G,H,bumpN]

private theorem qrun_none_after (T : List Nat) (k j : Nat)
    (h : qrun k T = none) : qrun (k+j) T = none := by
  rw [qrun_add,h]
  rfl

theorem halt_iff_prun :
    (∃ k, qrun k [481,133,28,25]=none) ↔
    (∃ n, prun n [301,650,645,322,163,160]=none) := by
  constructor
  · rintro ⟨k,hk⟩
    let n := k+1
    have hh : qrun (4+2*n) [481,133,28,25] = none := by
      have heq : k+(4+2*n-k)=4+2*n := by dsimp [n]; omega
      rw [← heq]
      exact qrun_none_after _ k (4+2*n-k) hk
    rw [qrun_add,first4] at hh
    simp only [Option.bind_some, qrun_twice] at hh
    cases hn : prun n [301,650,645,322,163,160] with
    | none => exact ⟨n,hn⟩
    | some V => simp [hn] at hh
  · rintro ⟨n,hn⟩
    refine ⟨4+2*n, ?_⟩
    rw [qrun_add,first4]
    simp [qrun_twice, hn]

#print axioms toggle471
#print axioms toggle472
#print axioms twoStep
#print axioms qrun_twice
#print axioms halt_iff_prun

end S4Toggle
