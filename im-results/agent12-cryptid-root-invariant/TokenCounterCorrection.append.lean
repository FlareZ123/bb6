/-!
Token normalization with a decreasing pending-one count.
Append inside the pinned #85 source namespace, immediately before its final end.
No other research append fragments are required.
-/

set_option maxRecDepth 4096
set_option maxHeartbeats 4000000

private theorem a12_rep_add {α : Type} (v : α) (a b : ℕ) :
    List.replicate (a+b) v = List.replicate a v ++ List.replicate b v := by
  induction a with
  | zero => simp
  | succ a ih =>
    rw [Nat.succ_add, List.replicate_succ, List.replicate_succ, List.cons_append, ih]

private theorem a12_rep_push {α : Type} (v : α) (a : ℕ) (T : List α) :
    List.replicate a v ++ v :: T = List.replicate (a+1) v ++ T := by
  have h := congrArg (fun L : List α => L ++ T) (a12_rep_add v a 1)
  simpa [List.append_assoc] using h.symm

private theorem a12_dr_sweep (k : ℕ) (K : List ℕ)
    (W : List (ℕ × ℕ)) (L : List ℕ) :
    ReachesPlus target
      (tok_DR (2 :: K) W (List.replicate (k+1) 0 ++ L))
      (tok_DR (2 :: List.replicate (k+1) 1 ++ K) W L) := by
  induction k generalizing K L with
  | zero => simpa using tok_DR_zero K W L
  | succ k ih =>
    have h1 := tok_DR_zero K W (List.replicate (k+1) 0 ++ L)
    have h2 := ih (1 :: K) L
    have h3 := ReachesPlus.trans h1 h2
    have he := a12_rep_push (1:ℕ) (k+1) K
    simpa only [he] using h3

private theorem a12_el_sweep (k : ℕ) (K : List ℕ)
    (W : List (ℕ × ℕ)) (L : List ℕ) :
    ReachesPlus target
      (tok_EL (List.replicate (k+1) 1 ++ K) W L)
      (tok_EL K W (List.replicate (k+1) 0 ++ L)) := by
  induction k generalizing K L with
  | zero => simpa using tok_EL_1 K W L
  | succ k ih =>
    have h1 := tok_EL_1 (List.replicate (k+1) 1 ++ K) W L
    have h2 := ih K (0 :: L)
    have h3 := ReachesPlus.trans h1 h2
    rw [a12_rep_push 0 (k+1) L] at h3
    exact h3

private theorem a12_cr_sweep (k b : ℕ) (K : List ℕ)
    (W : List (ℕ × ℕ)) (L : List ℕ) :
    ReachesPlus target
      (tok_CR (b :: K) W (List.replicate (k+1) 0 ++ L))
      (tok_CR ((b+2*(k+1)) :: K) W L) := by
  induction k generalizing b L with
  | zero => simpa using tok_CR_zero b K W L
  | succ k ih =>
    have h1 := tok_CR_zero b K W (List.replicate (k+1) 0 ++ L)
    have h2 := ih (b+2) L
    have hv : b+2+2*(k+1) = b+2*(k+2) := by omega
    rw [hv] at h2
    exact ReachesPlus.trans h1 h2

private def a12H (x r : ℕ) (K : List ℕ) (W : List (ℕ × ℕ)) :
    Cfg (Fin 2) (Fin 6) :=
  tok_EL (x :: K) W (List.replicate r 0 ++ [1])

/-- One subtract-three cycle. The entire unprocessed token/context tail is preserved. -/
private theorem a12H_step (x k : ℕ) (K : List ℕ) (W : List (ℕ × ℕ)) :
    ReachesPlus target (a12H (x+3) (k+1) K W)
      (a12H x (k+5) K W) := by
  have h1 := tok_EL_add3 x K W (List.replicate (k+1) 0 ++ [1])
  have h2 := a12_dr_sweep k (x :: K) W [1]
  have h3 := tok_DR_1_nil_28 (List.replicate (k+1) 1 ++ x :: K) W
  have h4 := a12_el_sweep (k+1) (x :: K) W [0,0,0,1]
  have hz : List.replicate (k+2) (0:ℕ) ++ [0,0,0,1] =
      List.replicate (k+5) 0 ++ [1] := by
    have h := congrArg (fun L : List ℕ => L ++ [1])
      (a12_rep_add (0:ℕ) (k+2) 3)
    simpa [List.append_assoc] using h.symm
  rw [hz] at h4
  exact ReachesPlus.trans h1 (ReachesPlus.trans h2 (ReachesPlus.trans h3 h4))

/-- The zero branch consumes the following token; it does NOT restore the pending one. -/
private theorem a12H_zero_cons (v k : ℕ) (K : List ℕ) (W : List (ℕ × ℕ)) :
    ReachesPlus target (a12H 0 (k+1) (v :: K) W)
      (a12H (v+1+2*(k+1)) 3 K W) := by
  have h1 := tok_EL_0_cons v K W (List.replicate (k+1) 0 ++ [1])
  have h2 := a12_cr_sweep k (v+1) K W [1]
  have h3 := tok_CR_1_nil_33 (v+1+2*(k+1)) K W
  exact ReachesPlus.trans h1 (ReachesPlus.trans h2 h3)

private theorem a12H_batch (n x k : ℕ) (K : List ℕ) (W : List (ℕ × ℕ)) :
    ReachesPlus target (a12H (x+3*(n+1)) (k+1) K W)
      (a12H x (k+1+4*(n+1)) K W) := by
  induction n generalizing k with
  | zero => simpa using a12H_step x k K W
  | succ n ih =>
    have h1 := a12H_step (x+3*(n+1)) k K W
    have h2 := ih (k+4)
    have hx : x+3*(n+1)+3 = x+3*(n+2) := by omega
    have hr : k+4+1+4*(n+1) = k+1+4*(n+2) := by omega
    rw [hx] at h1
    rw [hr] at h2
    exact ReachesPlus.trans h1 h2

private theorem a12H_mod (x k : ℕ) (K : List ℕ) (W : List (ℕ × ℕ))
    (hx : 3 ≤ x) :
    ReachesPlus target (a12H x (k+1) K W)
      (a12H (x%3) (k+1+4*(x/3)) K W) := by
  have h := a12H_batch (x/3-1) (x%3) k K W
  have hq : x/3-1+1 = x/3 := by omega
  rw [hq] at h
  have hv : x%3+3*(x/3)=x := by omega
  rw [hv] at h
  exact h

/-- Finite token normalization: a residue-one/two sentinel state, or
a residue-zero/one/two state without a sentinel. In the former case at
most p ones remain. This is not a global nonhalting assertion. -/
private theorem a12H_normalizes (p x k : ℕ) (W : List (ℕ × ℕ)) (hx : 3 ≤ x) :
    (∃ y r q : ℕ, 0 < y ∧ y < 3 ∧ q ≤ p ∧
      ReachesPlus target (a12H x (k+1) (List.replicate p 1 ++ [0]) W)
        (a12H y (r+1) (List.replicate q 1 ++ [0]) W)) ∨
    (∃ y r : ℕ, y < 3 ∧
      ReachesPlus target (a12H x (k+1) (List.replicate p 1 ++ [0]) W)
        (a12H y (r+1) [] W)) := by
  induction p generalizing x k with
  | zero =>
    let r := k+4*(x/3)
    have h1 := a12H_mod x k [0] W hx
    have hr : k+1+4*(x/3) = r+1 := by dsimp [r]; omega
    rw [hr] at h1
    by_cases hz : x%3 = 0
    · rw [hz] at h1
      have h2 := a12H_zero_cons 0 r [] W
      have h3 := a12H_mod (0+1+2*(r+1)) 2 [] W (by omega)
      have h4 := ReachesPlus.trans h1 (ReachesPlus.trans h2 h3)
      right
      exact ⟨(0+1+2*(r+1))%3, 2+4*((0+1+2*(r+1))/3),
        by omega, by exact h4⟩
    · left
      exact ⟨x%3,r,0,by omega,by omega,by omega,by simpa using h1⟩
  | succ p ih =>
    let r := k+4*(x/3)
    have h1 := a12H_mod x k (List.replicate (p+1) 1 ++ [0]) W hx
    have hr : k+1+4*(x/3) = r+1 := by dsimp [r]; omega
    rw [hr] at h1
    by_cases hz : x%3 = 0
    · rw [hz] at h1
      have h2 := a12H_zero_cons 1 r (List.replicate p 1 ++ [0]) W
      have h := ReachesPlus.trans h1 h2
      have hn := ih (1+1+2*(r+1)) 2 (by omega)
      rcases hn with ⟨y,r',q,hy,hy',hq,h3⟩ | ⟨y,r',hy,h3⟩
      · left
        exact ⟨y,r',q,hy,hy',by omega,ReachesPlus.trans h h3⟩
      · right
        exact ⟨y,r',hy,ReachesPlus.trans h h3⟩
    · left
      exact ⟨x%3,r,p+1,by omega,by omega,by omega,h1⟩

/-- The S family in the old note loses exactly one pending one. -/
private theorem a12S_zero_consumes (r p : ℕ) (W : List (ℕ × ℕ)) :
    ReachesPlus target
      (tok_DR (2 :: 0 :: List.replicate (p+1) 1 ++ [0]) W
        (List.replicate (r+1) 0 ++ [1]))
      (tok_DR (2 :: (2*r+9) :: List.replicate p 1 ++ [0]) W [0,0,0,1]) := by
  have h1 := a12_dr_sweep r (0 :: List.replicate (p+1) 1 ++ [0]) W [1]
  have h2 := tok_DR_1_nil_28 (List.replicate (r+1) 1 ++
      0 :: List.replicate (p+1) 1 ++ [0]) W
  have h3 := a12_el_sweep (r+1) (0 :: List.replicate (p+1) 1 ++ [0]) W [0,0,0,1]
  have hz : List.replicate (r+2) (0:ℕ) ++ [0,0,0,1] =
      List.replicate (r+5) 0 ++ [1] := by
    have h := congrArg (fun L : List ℕ => L ++ [1])
      (a12_rep_add (0:ℕ) (r+2) 3)
    simpa [List.append_assoc] using h.symm
  rw [hz] at h3
  have h4 := a12H_zero_cons 1 (r+4) (List.replicate p 1 ++ [0]) W
  have hv : 1+1+2*(r+4+1) = (2*r+9)+3 := by omega
  rw [hv] at h4
  have h5 := tok_EL_add3 (2*r+9) (List.replicate p 1 ++ [0]) W [0,0,0,1]
  exact ReachesPlus.trans h1
    (ReachesPlus.trans h2 (ReachesPlus.trans h3 (ReachesPlus.trans h4 h5)))

#print axioms a12H_step
#print axioms a12H_zero_cons
#print axioms a12H_batch
#print axioms a12H_mod
#print axioms a12H_normalizes
#print axioms a12S_zero_consumes
