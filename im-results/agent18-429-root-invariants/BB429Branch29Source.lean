import BB429Branch7Source
import BB429Branch29Mod64
import BB429Branch29Arithmetic
import Lean.Elab.Tactic.Omega

/-!
# #429 source-connected branch-7, 29 mod 32, final-burst congruences

The original pinned Cryptids source has a blank-root connector
`BB429SourceMod16.source_run_to_local`. Composing it with the local
inverse theorem, the exact branch-7 last-reset equation and a pure
power-of-two divisibility argument restricts any length n>=18 in
the x=29 mod32 subfamily to n=895,1919,2047 modulo 2048 in the refined theorem.
Other branch-7 residues and other last-reset branches remain open.
-/

namespace BB429Branch29Source
open BusyBeaver.M_1RB0LF_1RC1RA_0RD0RB_1LEHHH_0LA1LE_1RD1LA
set_option maxHeartbeats 10000000
set_option maxRecDepth 30000

theorem source_29_q_two_of_eight (i q : Nat) (hq : 21≤q)
    (hroot : BB429SourceLadder.sourceRun i highLevelStart =
      some (.J (32*q+29) (64*q+55))) :
    q%8=2 ∨ q%8=7 := by
  have hlocal :=
    BB429SourceMod16.source_run_to_local i
      (32*q+29) (64*q+55) hroot
  exact BB429Branch29.rooted_29_q_two_of_eight q hq ⟨i,hlocal⟩

private theorem n_plus_1000_le_pow (n : Nat) (hn : 18≤n) :
    n+1000≤2^(n+2) := by
  induction hn with
  | refl => norm_num
  | @step k hk ih =>
    calc
      k+1+1000 = k+1000+1 := by omega
      _ ≤ 2^(k+2)+1 := by omega
      _ ≤ 2^(k+2)*2 := by omega
      _ = 2^(k+1+2) := by
        have he : k+1+2=(k+2)+1 := by omega
        rw [he]
        exact (Nat.pow_succ 2 (k+2)).symm

/-- In the genuine branch-7 long-burst last-reset equation, the
29 mod32 pre-reset class is compatible with only two residue classes
of final burst length modulo 1024.

This theorem is a *necessary* condition from the authentic source
blank root; it does not establish any such event exists. -/
theorem source_branch7_29_burst_mod1024
    (i n x y : Nat)
    (hroot : BB429SourceLadder.sourceRun i highLevelStart =
      some (.J x y))
    (hbranch : y+3=2*x)
    (h29 : x%32=29)
    (hn : 18≤n)
    (heq : 4*x+3*n+15=3*2^(n+2)) :
    n%1024=895 ∨ n%1024=1023 := by
  let q := x/32
  have hx : x=32*q+29 := by dsimp [q]; omega
  have hy : y=64*q+55 := by omega
  have hb := n_plus_1000_le_pow n hn
  have hmul : 3*(n+1000)≤3*2^(n+2) :=
    Nat.mul_le_mul_left 3 hb
  have hxl : 701≤x := by omega
  have hq : 21≤q := by omega
  have hsrc := hroot
  rw [hx,hy] at hsrc
  have hqmod := source_29_q_two_of_eight i q hq hsrc
  have hpow : 2^(n+2)=1024*2^(n-8) := by
    have hsplit : n+2=10+(n-8) := by omega
    rw [hsplit, pow_add]
    norm_num
  have hmod : (4*x+3*n+15)%1024=0 := by
    rw [heq,hpow]
    omega
  rcases hqmod with h2 | h7
  · left
    omega
  · right
    omega


/-- The genuine original-source blank-root branch29 bound: q mod16
must belong to exactly three necessary parameter classes. -/
theorem source_29_q_three_mod16 (i q : Nat) (hq : 21≤q)
    (hroot : BB429SourceLadder.sourceRun i highLevelStart =
      some (.J (32*q+29) (64*q+55))) :
    q%16=2 ∨ q%16=10 ∨ q%16=15 := by
  have hlocal :=
    BB429SourceMod16.source_run_to_local i
      (32*q+29) (64*q+55) hroot
  exact BB429Branch29Mod16.rooted_29_q_three_mod16 q hq ⟨i,hlocal⟩

/-- Source-root last-reset branch7, x mod32=29: odd final burst
length n>=18 must be 895,1919 or 2047 modulo 2048.
This necessary condition does not establish a halting witness. -/
theorem source_branch7_29_burst_mod2048
    (i n x y : Nat)
    (hroot : BB429SourceLadder.sourceRun i highLevelStart =
      some (.J x y))
    (hbranch : y+3=2*x)
    (h29 : x%32=29)
    (hn : 18≤n)
    (heq : 4*x+3*n+15=3*2^(n+2)) :
    n%2048=895 ∨ n%2048=1919 ∨ n%2048=2047 := by
  let q := x/32
  have hx : x=32*q+29 := by dsimp [q]; omega
  have hy : y=64*q+55 := by omega
  have hb := n_plus_1000_le_pow n hn
  have hmul : 3*(n+1000)≤3*2^(n+2) :=
    Nat.mul_le_mul_left 3 hb
  have hq : 21≤q := by omega
  have hsrc := hroot
  rw [hx,hy] at hsrc
  have hqmod := source_29_q_three_mod16 i q hq hsrc
  have hpow : 2^(n+2)=2048*2^(n-9) := by
    have hsplit : n+2=11+(n-9) := by omega
    rw [hsplit, pow_add]
    norm_num
  have hmod : (4*x+3*n+15)%2048=0 := by
    rw [heq,hpow]
    omega
  rcases hqmod with h2 | h10 | h15
  · exact Or.inr (Or.inl (by omega))
  · exact Or.inl (by omega)
  · exact Or.inr (Or.inr (by omega))


/-- Eight necessary parameter classes modulo 64 for the original,
pinned Cryptids-source blank root in the 29 mod32 odd-reset feeder. -/
theorem source_29_q_eight_mod64 (i q : Nat) (hq : 21≤q)
    (hroot : BB429SourceLadder.sourceRun i highLevelStart =
      some (.J (32*q+29) (64*q+55))) :
    q%64=2 ∨ q%64=10 ∨ q%64=15 ∨ q%64=18 ∨
    q%64=31 ∨ q%64=47 ∨ q%64=58 ∨ q%64=63 := by
  have hlocal :=
    BB429SourceMod16.source_run_to_local i
      (32*q+29) (64*q+55) hroot
  exact BB429Branch29Mod64.rooted_29_q_eight_mod64 q hq ⟨i,hlocal⟩

/-- Exact necessary original-source last-reset burst restriction at
modulus 8192. Every class of the eight-way disjunction is traced
through the valid blank-root source connector and the exponential
last-reset equation, not sampled from a finite trajectory. -/
theorem source_branch7_29_burst_mod8192
    (i n x y : Nat)
    (hroot : BB429SourceLadder.sourceRun i highLevelStart =
      some (.J x y))
    (hbranch : y+3=2*x)
    (h29 : x%32=29)
    (hn : 18≤n)
    (heq : 4*x+3*n+15=3*2^(n+2)) :
    n%8192=8063 ∨ n%8192=4991 ∨ n%8192=2047 ∨
    n%8192=1919 ∨ n%8192=4095 ∨ n%8192=6143 ∨
    n%8192=2943 ∨ n%8192=8191 := by
  let q := x/32
  have hx : x=32*q+29 := by dsimp [q]; omega
  have hy : y=64*q+55 := by omega
  have hb := n_plus_1000_le_pow n hn
  have hmul : 3*(n+1000)≤3*2^(n+2) :=
    Nat.mul_le_mul_left 3 hb
  have hq : 21≤q := by omega
  have hsrc := hroot
  rw [hx,hy] at hsrc
  have hqmod := source_29_q_eight_mod64 i q hq hsrc
  have hpow : 2^(n+2)=8192*2^(n-11) := by
    have hsplit : n+2=13+(n-11) := by omega
    rw [hsplit,pow_add]
    norm_num
  have hmod : (4*x+3*n+15)%8192=0 := by
    rw [heq,hpow]
    omega
  rcases hqmod with h2 | h10 | h15 | h18 | h31 | h47 | h58 | h63
  · omega
  · omega
  · omega
  · omega
  · omega
  · omega
  · omega
  · omega


/-- Pinned original Cryptids blank-source version of the stronger
necessary branch-7 last-burst 16384 residue restriction. The genuine
raw source root is transported by the trusted source-to-local theorem,
then the all-time rooted twelve-q-class result is applied directly
to the exact final-burst Diophantine equation. -/
theorem source_branch7_29_burst_mod16384
    (i n x y : Nat)
    (hroot : BB429SourceLadder.sourceRun i highLevelStart =
      some (.J x y))
    (hbranch : y+3=2*x)
    (h29 : x%32=29)
    (hn : 18≤n)
    (heq : 4*x+3*n+15=3*2^(n+2)) :
    n%16384=16255 ∨ n%16384=4991 ∨ n%16384=10239 ∨
    n%16384=14335 ∨ n%16384=2943 ∨ n%16384=8191 ∨
    n%16384=13183 ∨ n%16384=2047 ∨ n%16384=1919 ∨
    n%16384=6143 ∨ n%16384=11135 ∨ n%16384=16383 := by
  let q := x/32
  have hx : x=32*q+29 := by dsimp [q]; omega
  have hy : y=64*q+55 := by omega
  have hb := n_plus_1000_le_pow n hn
  have hmul : 3*(n+1000)≤3*2^(n+2) :=
    Nat.mul_le_mul_left 3 hb
  have hq : 21≤q := by omega
  have hsrc := hroot
  rw [hx,hy] at hsrc
  have hlocal := BB429SourceMod16.source_run_to_local i
      (32*q+29) (64*q+55) hsrc
  have heq' : 128*q+3*n+131=3*2^(n+2) := by omega
  exact BB429Branch29Arithmetic.local_branch29_burst_mod16384
    q n hq hn ⟨i,hlocal⟩ heq'

#print axioms source_branch7_29_burst_mod16384

#print axioms source_29_q_eight_mod64
#print axioms source_branch7_29_burst_mod8192

#print axioms source_29_q_three_mod16
#print axioms source_branch7_29_burst_mod2048

#print axioms source_29_q_two_of_eight
#print axioms source_branch7_29_burst_mod1024
end BB429Branch29Source
