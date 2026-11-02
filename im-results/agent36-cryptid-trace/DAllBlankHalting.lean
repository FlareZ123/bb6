import DAllBlankSource

namespace BB6.Agent36

open CryptidBoundary

/-- The original Cryptid interpreter uses a total step with absorbing state 6,
    representing the undefined F-on-one transition. -/
def SourceHalts (c : Cfg) : Prop := ∃ n : Nat, (run n c).st = 6

theorem step_terminal (c : Cfg) (hc : c.st = 6) : step c = c := by
  rcases c with ⟨l,h,r,st⟩
  simp only at hc
  subst st
  cases h <;> rfl

theorem run_terminal (n : Nat) (c : Cfg) (hc : c.st = 6) :
    run n c = c := by
  induction n with
  | zero => rfl
  | succ n ih =>
    change step (run n c) = c
    rw [ih, step_terminal c hc]

/-- A finite prefix ending at an unhalted section preserves all-time
    blank halting iff, because the original terminal state is absorbing.
    This does not require a proof of absence of earlier halting. -/
theorem halts_after_exact_prefix (t : Nat) (c d : Cfg)
    (h : run t c = d) :
    SourceHalts c ↔ SourceHalts d := by
  constructor
  · rintro ⟨n, hn⟩
    have he : (run (n+t) c).st = 6 := by
      rw [run_add n t]
      rw [run_terminal t (run n c) hn]
      exact hn
    rw [Nat.add_comm n t, run_add t n, h] at he
    exact ⟨n,he⟩
  · rintro ⟨n,hn⟩
    refine ⟨t+n,?_⟩
    rw [run_add t n, h]
    exact hn

/-- Complete original-source all-time blank-to-unary source equivalences. -/
theorem blank_A_halts_iff_I9 :
    SourceHalts (sourceBlank (0:Fin 6)) ↔
    SourceHalts (init (List.replicate 7 true)) :=
  halts_after_exact_prefix 36 _ _ source_blank_A36

theorem blank_B_halts_iff_I5 :
    SourceHalts (sourceBlank (1:Fin 6)) ↔
    SourceHalts (init (List.replicate 3 true)) :=
  halts_after_exact_prefix 15 _ _ source_blank_B15

theorem blank_C_halts_iff_I15 :
    SourceHalts (sourceBlank (2:Fin 6)) ↔
    SourceHalts (init (List.replicate 13 true)) :=
  halts_after_exact_prefix 92 _ _ source_blank_C92

theorem blank_D_halts_iff_I5 :
    SourceHalts (sourceBlank (3:Fin 6)) ↔
    SourceHalts (init (List.replicate 3 true)) :=
  halts_after_exact_prefix 15 _ _ source_blank_D15

theorem blank_E_halts_iff_I15 :
    SourceHalts (sourceBlank (4:Fin 6)) ↔
    SourceHalts (init (List.replicate 13 true)) :=
  halts_after_exact_prefix 93 _ _ source_blank_E93

theorem blank_F_halts_iff_I39 :
    SourceHalts (sourceBlank (5:Fin 6)) ↔
    SourceHalts (init (List.replicate 37 true)) :=
  halts_after_exact_prefix 403 _ _ source_blank_F403

theorem source_blank_B_D_same_outcome :
    SourceHalts (sourceBlank (1:Fin 6)) ↔
      SourceHalts (sourceBlank (3:Fin 6)) := by
  exact blank_B_halts_iff_I5.trans blank_D_halts_iff_I5.symm

theorem source_blank_C_E_same_outcome :
    SourceHalts (sourceBlank (2:Fin 6)) ↔
      SourceHalts (sourceBlank (4:Fin 6)) := by
  exact blank_C_halts_iff_I15.trans blank_E_halts_iff_I15.symm

/-- Stronger physical trajectory merger in the head-relative list source
    representation: B/D become exactly equal after 15 primitive steps,
    while C/E become exactly equal after 92 and 93 steps respectively. -/
theorem source_blank_B_D_fuse (n : Nat) :
    run (15+n) (sourceBlank (1:Fin 6)) =
    run (15+n) (sourceBlank (3:Fin 6)) := by
  rw [run_add, run_add, source_blank_B15, source_blank_D15]

theorem source_blank_C_E_fuse (n : Nat) :
    run (92+n) (sourceBlank (2:Fin 6)) =
    run (93+n) (sourceBlank (4:Fin 6)) := by
  rw [run_add, run_add, source_blank_C92, source_blank_E93]

#print axioms step_terminal
#print axioms run_terminal
#print axioms halts_after_exact_prefix
#print axioms blank_A_halts_iff_I9
#print axioms blank_B_halts_iff_I5
#print axioms blank_C_halts_iff_I15
#print axioms blank_D_halts_iff_I5
#print axioms blank_E_halts_iff_I15
#print axioms blank_F_halts_iff_I39
#print axioms source_blank_B_D_same_outcome
#print axioms source_blank_C_E_same_outcome
#print axioms source_blank_B_D_fuse
#print axioms source_blank_C_E_fuse
end BB6.Agent36
