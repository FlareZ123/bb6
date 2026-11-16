import SourceMod16
import BB429Branch7
import Lean.Elab.Tactic.Omega

namespace BB429Branch7Source

open BusyBeaver.M_1RB0LF_1RC1RA_0RD0RB_1LEHHH_0LA1LE_1RD1LA

/-- Transport the branch-7 residue reduction through the native Cryptids
accelerator, rather than merely asserting it for the local copy. -/
theorem source_odd_reset_necessary_three (n u w : Nat)
    (h : BB429SourceLadder.sourceRun n highLevelStart = some (.J u w))
    (hg : w+3=2*u) (hlarge : 32≤u) :
    u%32=13 ∨ u%32=15 ∨ u%32=29 := by
  have hr := BB429SourceMod16.source_run_to_local n u w h
  exact BB429Branch7.rooted_odd_reset_necessary_three n u w hr hg hlarge

/-- Elementary growth bound needed to use the positive-q inverse-cylinder
exclusions on every branch-7 last-reset candidate with n>=18. -/
private theorem n_add_48_le_pow (n : Nat) (hn : 18≤n) :
    n+48≤2^(n+2) := by
  induction hn with
  | refl => norm_num
  | @step n hn ih =>
    calc
      n+1+48 = n+48+1 := by omega
      _ ≤ 2^(n+2)+1 := by omega
      _ ≤ 2^(n+2)*2 := by omega
      _ = 2^(n+1+2) := by
        rw [Nat.pow_succ]
        omega

/-- In branch 7, the exact last-reset equation is
4*x+3*n+15=3*2^(n+2). For n>=18 it forces x>=33. -/
theorem branch7_prestate_large (n x : Nat)
    (hn : 18≤n)
    (heq : 4*x+3*n+15=3*2^(n+2)) : 32≤x := by
  have hp := n_add_48_le_pow n hn
  have hmul : 3*(n+48)≤3*2^(n+2) := Nat.mul_le_mul_left 3 hp
  omega

/-- Source-level last-reset reduction: every genuine blank-root prestate
in branch 7 with final burst n>=18 has first-counter residue 13, 15, or 29
modulo 32. The other two residues are excluded by all-time inverse proofs. -/
theorem source_branch7_last_reset_three_residues
    (i n x y : Nat)
    (hroot : BB429SourceLadder.sourceRun i highLevelStart = some (.J x y))
    (hbranch7 : y+3=2*x)
    (hn : 18≤n)
    (heq : 4*x+3*n+15=3*2^(n+2)) :
    x%32=13 ∨ x%32=15 ∨ x%32=29 := by
  have hlarge := branch7_prestate_large n x hn heq
  exact source_odd_reset_necessary_three i x y hroot hbranch7 hlarge

#print axioms source_odd_reset_necessary_three
#print axioms branch7_prestate_large
#print axioms source_branch7_last_reset_three_residues

end BB429Branch7Source
