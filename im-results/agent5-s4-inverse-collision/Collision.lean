import S4SourceShape
import Lean
import Lean.Elab.Tactic.Omega

namespace S4Collision

def bumpBy (k : Nat) : List Nat → List Nat
  | [] => if k = 0 then [] else [k-1]
  | b::S => (b+k)::S

-- Reuse the prior source-shaped source H verbatim.
def H (a : Nat) (L : List Nat) : Option (List Nat) := _root_.H a L

def compactNext : List Nat → Option (List Nat)
  | [] => (H 44 []).map (bumpBy 17)
  | b::S => (H (b+45) S).map (bumpBy 17)

theorem bumpBy17_eq_source (L : List Nat) :
    bumpBy 17 L = _root_.bump17 L := by
  cases L <;> rfl

theorem compactNext_eq_source (T : List Nat) :
    compactNext T = _root_.compactNext T := by
  have he : bumpBy 17 = _root_.bump17 := funext bumpBy17_eq_source
  cases T <;> simp [compactNext, _root_.compactNext, _root_.compactInitial, H, he]

theorem odd_cons (q b : Nat) (S : List Nat) :
 H (2*q+1) (b::S) = (H (b+q+1) S).map (q::·) := by
 have hdiv : (2*q+1)/2=q := by omega
 simp [H, _root_.H, hdiv]

theorem even_cons (q b : Nat) (S : List Nat) (hq : 0 < q) :
 H (2*q) (b::S) = some ((q+2)::(b+q)::S) := by
 simp [H, _root_.H] <;> omega

theorem H_left (u v t : Nat) (S : List Nat) :
  H 125 ((150+2*u)::(481+u+2*v)::t::S) =
    some (62::(106+u)::(296+u+v)::(t+294+u+v)::S) := by
  have a : H 125 ((150+2*u)::(481+u+2*v)::t::S) =
      (H (213+2*u) ((481+u+2*v)::t::S)).map (62::·) := by
    have d : 150+2*u+62+1 = 213+2*u := by omega
    simpa only [d] using odd_cons 62 (150+2*u) ((481+u+2*v)::t::S)
  have b : H (213+2*u) ((481+u+2*v)::t::S) =
      (H (588+2*u+2*v) (t::S)).map ((106+u)::·) := by
    have e : 2*(106+u)+1 = 213+2*u := by omega
    have d : 481+u+2*v+(106+u)+1 = 588+2*u+2*v := by omega
    simpa only [e, d] using odd_cons (106+u) (481+u+2*v) (t::S)
  have c : H (588+2*u+2*v) (t::S) =
      some ((296+u+v)::(t+294+u+v)::S) := by
    have e : 2*(294+u+v) = 588+2*u+2*v := by omega
    have d : 294+u+v+2 = 296+u+v := by omega
    have f : t+(294+u+v) = t+294+u+v := by omega
    simpa only [e, d, f] using even_cons (294+u+v) t S (by omega)
  rw [a,b,c]
  rfl

theorem H_right (u v t : Nat) (S : List Nat) :
  H 125 ((145+2*u)::(192+v)::(t+294+u+v)::S) =
    some (62::(106+u)::(296+u+v)::(t+294+u+v)::S) := by
  have a : H 125 ((145+2*u)::(192+v)::(t+294+u+v)::S) =
      (H (208+2*u) ((192+v)::(t+294+u+v)::S)).map (62::·) := by
    have d : 145+2*u+62+1 = 208+2*u := by omega
    simpa only [d] using odd_cons 62 (145+2*u) ((192+v)::(t+294+u+v)::S)
  have b : H (208+2*u) ((192+v)::(t+294+u+v)::S) =
      some ((106+u)::(296+u+v)::(t+294+u+v)::S) := by
    have e : 2*(104+u) = 208+2*u := by omega
    have d : 104+u+2 = 106+u := by omega
    have f : (192+v)+(104+u) = 296+u+v := by omega
    simpa only [e,d,f] using even_cons (104+u) (192+v) ((t+294+u+v)::S) (by omega)
  rw [a,b]
  rfl

theorem collision_family (u v t : Nat) (S : List Nat) :
    compactNext (80::(150+2*u)::(481+u+2*v)::t::S) =
    compactNext (80::(145+2*u)::(192+v)::(t+294+u+v)::S) := by
  simp only [compactNext, Nat.reduceAdd]
  rw [H_left, H_right]

theorem collision_family_distinct (u v t : Nat) (S : List Nat) :
    (80::(150+2*u)::(481+u+2*v)::t::S) ≠
    (80::(145+2*u)::(192+v)::(t+294+u+v)::S) := by
  intro h
  have e : 150+2*u = 145+2*u := by
    have := congrArg List.head? (List.tail_eq_of_cons_eq h)
    simpa using this
  omega

def run : Nat → Option (List Nat) → Option (List Nat)
  | 0, x => x
  | n+1, x => (run n x).bind compactNext

#eval run 13 (some [42,12,8,5])
#eval compactNext [80,150,481,133,28,25]

set_option maxRecDepth 10000
set_option maxHeartbeats 0

example : compactNext [42,12,8,5] = some [60,30,36,5] := by
  simp [compactNext, H, _root_.H, bumpBy]

theorem actual_prefix_13 :
    run 13 (some [42,12,8,5]) = some [80,150,481,133,28,25] := by
  simp [run, compactNext, H, _root_.H, bumpBy]

theorem actual_step_collision :
    compactNext [80,150,481,133,28,25] =
      compactNext [80,145,192,427,28,25] := by
  simpa using collision_family 0 0 133 [28,25]

theorem actual_rooted_collision :
    ∃ A B : List Nat,
      run 13 (some [42,12,8,5]) = some A ∧
      A ≠ B ∧ compactNext A = compactNext B := by
  refine ⟨[80,150,481,133,28,25], [80,145,192,427,28,25], actual_prefix_13, ?_, actual_step_collision⟩
  decide

#print axioms collision_family
#print axioms collision_family_distinct
#print axioms actual_prefix_13
#print axioms actual_step_collision
#print axioms actual_rooted_collision
end S4Collision
