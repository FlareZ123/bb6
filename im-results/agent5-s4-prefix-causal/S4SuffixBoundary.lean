import S4Octet
import Lean.Elab.Tactic.Omega

namespace S4Boundary
open S4Power S4Octet

def bump (d : Nat) : List Nat → List Nat
  | [] => [d-1]
  | b::S => (b+d)::S

inductive Action where
  | id
  | add (d : Nat)
  | gate (d : Nat)

def Action.eval : Action → List Nat → Option (List Nat)
  | .id, S => some S
  | .add d, S => some (bump d S)
  | .gate d, S => G d S

def split (a : Nat) : List Nat → List Nat × Action
  | [] => if a%2=0 then ([a/2+2],.add (a/2)) else ([a/2],.gate (a/2+1))
  | b::T =>
      if a%2=0 then ((a/2+2)::(b+a/2)::T,.id)
      else
        let u := split (b+a/2+1) T
        (a/2::u.1, u.2)

/-- Every positive-head odd drain factors through an arbitrary finite prefix,
 preserving the exact partial suffix halt. -/
theorem H_split (a : Nat) (P S : List Nat) (ha : 0<a) :
    H a (P ++ S) = ((split a P).2.eval S).map ((split a P).1 ++ ·) := by
  induction P generalizing a with
  | nil =>
      by_cases he : a % 2 = 0
      · cases S with
        | nil =>
            have hn : a ≠ 0 := Nat.ne_of_gt ha
            simp [H, split, Action.eval, bump, he, hn]
        | cons b T =>
            simp [H, split, Action.eval, bump, he]
      · cases S with
        | nil =>
            have hd : (a/2+1)-1 = a/2 := by omega
            have hodd : H a [] = (H (a/2) []).map (a/2 :: ·) := by
              by_cases hs : a ≤ 1
              · have ha1 : a = 1 := by omega
                subst a
                simp [H]
              · rw [H]
                simp only [he, hs, ite_false]
            simpa only [List.nil_append, split, he, ite_false, Action.eval,
              G, hd, List.cons_append] using hodd
        | cons b T =>
            have hd : b+a/2+1 = b+(a/2+1) := by omega
            simp [H, split, Action.eval, G, he, hd]
  | cons b T ih =>
      by_cases he : a % 2 = 0
      · simp [H, split, Action.eval, he, List.append_assoc]
      · have hh : 0 < b + a/2+1 := by omega
        rw [show (b::T)++S = b::(T++S) by rfl]
        rw [H, if_neg he]
        rw [ih (b+a/2+1) hh]
        simp [split, he, List.append_assoc, Option.map_map, Function.comp_def]

/-- Genuine original G on a source prefix and any suffix, with halting preserved. -/
theorem G_split (c b : Nat) (P S : List Nat) (hc : 0<c) :
    G c ((b::P) ++ S) =
      ((split (b+c) P).2.eval S).map ((split (b+c) P).1 ++ ·) := by
  change H (b+c) (P++S) = _
  exact H_split (b+c) P S (by omega)

/-- Head additions fold into the next source G operation even for the empty suffix. -/
theorem G_bump (c d : Nat) (S : List Nat) (hd : 0<d) :
    G c (bump d S) = G (c+d) S := by
  cases S with
  | nil =>
      have ha : d-1+c = (c+d)-1 := by omega
      simp [G,bump,ha]
  | cons b T =>
      simp [G,bump,Nat.add_assoc,Nat.add_comm,Nat.add_left_comm]

/-- Adjacent head additions compose even on the empty suffix. -/
theorem bump_bump (d e : Nat) (S : List Nat) (hd : 0<d) (he : 0<e) :
    bump d (bump e S) = bump (d+e) S := by
  cases S with
  | nil =>
      simp [bump]
      omega
  | cons b T =>
      simp [bump,Nat.add_assoc,Nat.add_comm,Nat.add_left_comm]

#print axioms H_split
#print axioms G_split
#print axioms G_bump
#print axioms bump_bump
end S4Boundary
