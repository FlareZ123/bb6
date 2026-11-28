import F321Periodicity
import Lean.Elab.Tactic.Omega

namespace BB6.Agent31F321Density

/-- Every high letter adds a factor two to the number of compatible
    residues in the uniform 4^n period; far adds one. -/
def wordWeight : List InverseLetter → Nat
 | [] => 1
 | .high::xs => 2*wordWeight xs
 | .far::xs => wordWeight xs

def weightSum : List (List InverseLetter) → Nat
 | [] => 0
 | w::ws => wordWeight w+weightSum ws

theorem weightSum_append (u v:List (List InverseLetter)) :
  weightSum (u++v)=weightSum u+weightSum v := by
 induction u with
 | nil => simp [weightSum]
 | cons w ws ih => simp [weightSum,ih,Nat.add_assoc]

theorem weightSum_high (l:List (List InverseLetter)) :
  weightSum (l.map (.high::·)) = 2*weightSum l := by
 induction l with
 | nil => simp [weightSum]
 | cons w ws ih =>
     simp [weightSum,wordWeight,ih,Nat.mul_add]

theorem weightSum_far (l:List (List InverseLetter)) :
  weightSum (l.map (.far::·)) = weightSum l := by
 induction l with
 | nil => simp [weightSum]
 | cons w ws ih => simp [weightSum,wordWeight,ih]

/-- The universal H/F inverse-word first-moment recursion has
    exact total weight 3^n; Lean 4.36.0-rc2 kernel proof, no sorry. -/
theorem word_first_moment (n:Nat) : weightSum (words n)=3^n := by
 induction n with
 | zero => decide
 | succ n ih =>
     simp only [words,weightSum_append,weightSum_high,weightSum_far]
     rw [ih,Nat.pow_succ]
     omega

#print axioms word_first_moment
end BB6.Agent31F321Density
