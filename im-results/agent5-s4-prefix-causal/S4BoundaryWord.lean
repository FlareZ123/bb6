import S4SuffixBoundary
import Lean.Elab.Tactic.Omega

namespace S4Boundary
open S4Power S4Octet

/-- The extracted source prefix always has the same number of digits. -/
theorem split_length (a : Nat) (P : List Nat) :
    (split a P).1.length = P.length + 1 := by
  induction P generalizing a with
  | nil =>
      by_cases he : a % 2 = 0 <;> simp [split, he]
  | cons b T ih =>
      by_cases he : a % 2 = 0
      · simp [split, he]
      · simpa [split, he] using congrArg Nat.succ (ih (b + a/2 + 1))

def prefixStep (c : Nat) : List Nat → List Nat
  | [] => []
  | b::P => (split (b+c) P).1

def suffixStep (c : Nat) (P S : List Nat) : Option (List Nat) :=
  match P with
  | [] => G c S
  | b::T => (split (b+c) T).2.eval S

/-- Single original G transition decomposes into exact prefix and suffix maps. -/
theorem G_prefix (c : Nat) (P S : List Nat) (hc : 0<c) :
    G c (P ++ S) = (suffixStep c P S).map (prefixStep c P ++ ·) := by
  cases P with
  | nil => simp [prefixStep, suffixStep]
  | cons b T =>
      simpa [prefixStep, suffixStep] using G_split c b T S hc

/-- A list of original G transitions, with Option short-circuiting. -/
def wholeWord : List Nat → List Nat → Option (List Nat)
  | [], T => some T
  | c::cs, T => (G c T).bind (wholeWord cs)

def prefixWord : List Nat → List Nat → List Nat
  | [], P => P
  | c::cs, P => prefixWord cs (prefixStep c P)

def suffixWord : List Nat → List Nat → List Nat → Option (List Nat)
  | [], _, S => some S
  | c::cs, P, S => (suffixStep c P S).bind (suffixWord cs (prefixStep c P))

/-- Any finite positive-offset word has a universal partial suffix-action
    factorization. This is an exact all-tails, first-event preserving identity. -/
theorem wholeWord_split (cs : List Nat) (P S : List Nat)
    (hc : ∀ c ∈ cs, 0<c) :
    wholeWord cs (P++S) =
      (suffixWord cs P S).map (prefixWord cs P ++ ·) := by
  induction cs generalizing P S with
  | nil => simp [wholeWord, suffixWord, prefixWord]
  | cons c cs ih =>
      have hc0 : 0 < c := hc c (by simp)
      have hcs : ∀ d ∈ cs, 0<d := by
        intro d hd
        exact hc d (by simp [hd])
      simp only [wholeWord, suffixWord, prefixWord]
      rw [G_prefix c P S hc0]
      cases h : suffixStep c P S with
      | none => simp [h]
      | some U =>
          simp [h]
          exact ih (prefixStep c P) U hcs

#print axioms split_length
#print axioms wholeWord_split
end S4Boundary
