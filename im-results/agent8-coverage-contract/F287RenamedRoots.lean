import F287Roots

namespace BB6.F287
open BB6Coverage

private def exchange (other : Fin 6) (q : Fin 6) : Fin 6 :=
  if q = 0 then other else if q = other then 0 else q

def exchangeD : StatePerm where
  forward := exchange dRoot
  backward := exchange dRoot
  leftInverse := by decide
  rightInverse := by decide

def exchangeE : StatePerm where
  forward := exchange eRoot
  backward := exchange eRoot
  leftInverse := by decide
  rightInverse := by decide

def dAsARoot : Machine := renameTable exchangeD expectedRLE
def eAsARoot : Machine := renameTable exchangeE expectedRLE

theorem exchangeD_blank : renameConfig exchangeD (blankAt dRoot) = blank := by
  rfl

theorem exchangeE_blank : renameConfig exchangeE (blankAt eRoot) = blank := by
  rfl

/-- A rooted source-D machine obtained by rigorously renaming its start to A. -/
theorem dAsARoot_never : NeverHalts dAsARoot := by
  intro n
  have hrun := rename_run exchangeD expectedRLE (blankAt dRoot) n
  rw [exchangeD_blank] at hrun
  change (run (renameTable exchangeD expectedRLE) n blank).isSome = true
  rw [hrun]
  cases h : run expectedRLE n (blankAt dRoot) with
  | none =>
      have hh := d_never n
      simp [h] at hh
  | some c => rfl

/-- A rooted source-E machine obtained by rigorously renaming its start to A. -/
theorem eAsARoot_never : NeverHalts eAsARoot := by
  intro n
  have hrun := rename_run exchangeE expectedRLE (blankAt eRoot) n
  rw [exchangeE_blank] at hrun
  change (run (renameTable exchangeE expectedRLE) n blank).isSome = true
  rw [hrun]
  cases h : run expectedRLE n (blankAt eRoot) with
  | none =>
      have hh := e_never n
      simp [h] at hh
  | some c => rfl

/-- 0LE0LC_1RC0RD_1LA0RB_1RB0LF_0LD0LC_0LB--- -/
def dLiteral (s : Slot) : Transition :=
  match s.1.val, s.2 with
  | 0, false => some ⟨false,false,4⟩
  | 0, true  => some ⟨false,false,2⟩
  | 1, false => some ⟨true,true,2⟩
  | 1, true  => some ⟨false,true,3⟩
  | 2, false => some ⟨true,false,0⟩
  | 2, true  => some ⟨false,true,1⟩
  | 3, false => some ⟨true,true,1⟩
  | 3, true  => some ⟨false,false,5⟩
  | 4, false => some ⟨false,false,3⟩
  | 4, true  => some ⟨false,false,2⟩
  | 5, false => some ⟨false,false,1⟩
  | 5, true  => none
  | _, _ => none

/-- 0LE0LC_1RC0RE_1LD0RB_0LA0LC_1RB0LF_0LB--- -/
def eLiteral (s : Slot) : Transition :=
  match s.1.val, s.2 with
  | 0, false => some ⟨false,false,4⟩
  | 0, true  => some ⟨false,false,2⟩
  | 1, false => some ⟨true,true,2⟩
  | 1, true  => some ⟨false,true,4⟩
  | 2, false => some ⟨true,false,3⟩
  | 2, true  => some ⟨false,true,1⟩
  | 3, false => some ⟨false,false,0⟩
  | 3, true  => some ⟨false,false,2⟩
  | 4, false => some ⟨true,true,1⟩
  | 4, true  => some ⟨false,false,5⟩
  | 5, false => some ⟨false,false,1⟩
  | 5, true  => none
  | _, _ => none

theorem d_rle_eq : dAsARoot = dLiteral := by
  funext slot
  rcases slot with ⟨q,b⟩
  have h : q = 0 ∨ q = 1 ∨ q = 2 ∨ q = 3 ∨ q = 4 ∨ q = 5 := by omega
  rcases h with h | h | h | h | h | h <;> subst q <;> cases b <;> decide

theorem e_rle_eq : eAsARoot = eLiteral := by
  funext slot
  rcases slot with ⟨q,b⟩
  have h : q = 0 ∨ q = 1 ∨ q = 2 ∨ q = 3 ∨ q = 4 ∨ q = 5 := by omega
  rcases h with h | h | h | h | h | h <;> subst q <;> cases b <;> decide

theorem d_literal_never : NeverHalts dLiteral := by
  rw [← d_rle_eq]
  exact dAsARoot_never

theorem e_literal_never : NeverHalts eLiteral := by
  rw [← e_rle_eq]
  exact eAsARoot_never

#print axioms d_literal_never
#print axioms e_literal_never
#print axioms dAsARoot_never
#print axioms eAsARoot_never
end BB6.F287
