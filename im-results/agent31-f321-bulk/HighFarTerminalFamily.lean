import F321BackwardBarrier
import BulkRuns
import Lean.Elab.Tactic.Omega

/-!
An infinite source-faithful mixed terminal-suffix family for F321.

This does not claim that any of the displayed anchors is reachable from the
blank root.  It identifies an exact infinite family of anchors from which a
valid High^n/Far suffix reaches a terminal gate, including a subfamily that
passes the currently accepted mod-384 terminal gate and coarse anchor-residue
necessary conditions.
-/

namespace BB6.Agent31F321HighFarFamily
open BB6.Agent31F321Density
open BB6.Agent2F321Bulk

/-- A uniform sufficient condition for n consecutive High moves.  The theorem
    also records subtraction-free exact endpoint coordinates. -/
theorem highRun_of_bound : ∀ {n a d : Nat},
    2^n * (d+3) ≤ a+d+4 →
    ∃ A D, HighRun n a d A D ∧
      A + 2^n*(d+3) = a+d+n+3 ∧
      D + 3 = 2^n*(d+3) := by
  intro n
  induction n with
  | zero =>
      intro a d hb
      exact ⟨a,d,HighRun.nil a d,by simp <;> omega,by simp⟩
  | succ n ih =>
      intro a d hb
      have hpow2 : 2 ≤ 2^(n+1) := by
        rw [Nat.pow_succ]
        have h1 : 1 ≤ 2^n := Nat.one_le_pow n 2 (by omega)
        omega
      have hmul : 2*(d+3) ≤ 2^(n+1)*(d+3) :=
        Nat.mul_le_mul_right (d+3) hpow2
      have hg : d+2≤a := by omega
      have hpoweq : 2^n * ((2*d+3)+3) = 2^(n+1)*(d+3) := by
        have hd : (2*d+3)+3 = 2*(d+3) := by omega
        rw [hd, Nat.pow_succ]
        ac_rfl
      have hb' : 2^n*((2*d+3)+3) ≤ (a-d-2)+(2*d+3)+4 := by
        rw [hpoweq]
        omega
      rcases ih hb' with ⟨A,D,hr,hA,hD⟩
      refine ⟨A,D,HighRun.step hg hr,?_,?_⟩
      · rw [← hpoweq]
        omega
      · rw [← hpoweq]
        exact hD

/-- Exponential domination needed by the mixed family. -/
theorem exp_linear_bound : ∀ n : Nat, 4 ≤ n → 7*n+1 ≤ 2^(n+2) := by
  intro n hn
  obtain ⟨k,rfl⟩ : ∃ k, n=4+k := by exact ⟨n-4, by omega⟩
  induction k with
  | zero => decide
  | succ k ih =>
      have hp : 2^(4+k+1+2) = 2 * 2^(4+k+2) := by
        rw [show 4+k+1+2=(4+k+2)+1 by omega, Nat.pow_succ]
        ac_rfl
      change 7*(4+(k+1))+1 ≤ 2^(4+k+1+2)
      rw [hp]
      have hi := ih (by omega)
      omega

theorem counterReach_append_local
    {sa sd n a d m A D : Nat}
    (h1 : CounterReach sa sd n a d)
    (h2 : CounterReach a d m A D) :
    CounterReach sa sd (n+m) A D := by
  induction h2 with
  | nil => simpa using h1
  | step hr hm ih => simpa [Nat.add_assoc] using CounterReach.step ih hm

theorem highRun_counterReach_local {k a d A D : Nat}
    (h : HighRun k a d A D) : CounterReach a d k A D := by
  induction h with
  | nil a d => exact CounterReach.nil
  | @step k a d A D hg tail ih =>
      have hfirst : CounterReach a d 1 (a-d-2) (2*d+3) :=
        CounterReach.step CounterReach.nil (CounterMove.high a d hg)
      simpa [Nat.add_comm] using counterReach_append_local hfirst ih

/-- Generic source-faithful terminal suffix criterion.  If the terminal
    parameter t and anchor first counter R satisfy the two displayed exact
    equations, then n High moves followed by one Far move reach (t+1,t). -/
theorem high_far_terminal_family {n t R : Nat}
    (hn : 4 ≤ n)
    (ht : 7*t = 2^(n+4)+3)
    (hR : R+n+6 = 2*t) :
    CounterReach R 1 (n+1) (t+1) t := by
  have hEpow : 2^(n+4) = 4 * 2^(n+2) := by
    rw [show n+4=(n+2)+2 by omega, Nat.pow_add]
    change 2^(n+2)*4 = 4*2^(n+2)
    ac_rfl
  have hlin := exp_linear_bound n hn
  have hE : 2^(n+2) ≤ R+5 := by
    rw [hEpow] at ht
    omega
  have h4pow : 2^n * (1+3) = 2^(n+2) := by
    rw [Nat.pow_add]
  have hb : 2^n*(1+3) ≤ R+1+4 := by
    rw [h4pow]
    omega
  rcases highRun_of_bound hb with ⟨A,D,hh,hA,hD⟩
  have ht' : 7*t = 4*2^(n+2)+3 := by
    rw [← hEpow]
    exact ht
  have htpos : 1≤t := by
    have hp : 1≤2^(n+4) := Nat.one_le_pow (n+4) 2 (by omega)
    omega
  have hDA : D = 3*A+t := by omega
  have hlt : A<D := by omega
  have hguard : 3*A+1≤D := by omega
  have houtA : 4*A+6=t+1 := by omega
  have houtD : D-3*A=t := by omega
  have hfar0 : CounterMove A D (4*A+6) (D-3*A) :=
    CounterMove.far A D hlt hguard
  have hfar : CounterMove A D (t+1) t := by
    simpa [houtA,houtD] using hfar0
  exact CounterReach.step (highRun_counterReach_local hh) hfar

def highFarN (m:Nat) : Nat := 3*m+4

def highFarT : Nat → Nat
  | 0 => 37
  | m+1 => 8*highFarT m - 3

theorem highFarT_pos (m:Nat) : 1 ≤ highFarT m := by
  induction m with
  | zero => decide
  | succ m ih =>
      simp [highFarT]
      omega

/-- Closed Diophantine identity for the infinite H^n/F terminal family. -/
theorem highFarT_equation (m:Nat) :
    7*highFarT m = 2^(highFarN m+4)+3 := by
  induction m with
  | zero => decide
  | succ m ih =>
      have hp : 2^(highFarN (m+1)+4) =
          8*2^(highFarN m+4) := by
        unfold highFarN
        rw [show 3*(m+1)+4+4=(3*m+4+4)+3 by omega, Nat.pow_add]
        change 2^(3*m+4+4) * 8 = 8*2^(3*m+4+4)
        ac_rfl
      rw [hp]
      simp only [highFarT]
      have hpos := highFarT_pos m
      omega

/-- Every member of the recurrence gives an actual source-map terminal suffix
    from its explicit anchor. -/
theorem high_far_infinite_family (m:Nat) :
    let n := highFarN m
    let t := highFarT m
    let R := 2*t-(n+6)
    CounterReach R 1 (n+1) (t+1) t := by
  dsimp only
  let n := highFarN m
  let t := highFarT m
  have hn : 4≤n := by
    dsimp [n, highFarN]
    omega
  have heq : 7*t=2^(n+4)+3 := by
    dsimp [n,t]
    exact highFarT_equation m
  have hlin := exp_linear_bound n hn
  have hEpow : 2^(n+4)=4*2^(n+2) := by
    rw [show n+4=2+(n+2) by omega, Nat.pow_add]
  have hbound : n+6≤2*t := by
    rw [hEpow] at heq
    omega
  have hR : (2*t-(n+6))+n+6=2*t := by omega
  exact high_far_terminal_family hn heq hR

theorem highFarT_mod384 (m:Nat) :
    (m%2=0 ∧ highFarT m %384=37) ∨
    (m%2=1 ∧ highFarT m %384=293) := by
  induction m with
  | zero => left; decide
  | succ m ih =>
      have hp := highFarT_pos m
      simp only [highFarT]
      rcases ih with h0 | h1
      · right
        constructor <;> omega
      · left
        constructor <;> omega

/-- The subfamily n=24k+22 is especially important for the root problem:
    every member has terminal residue 37 mod 384 and anchor residue 22 mod 24,
    hence it survives the already accepted coarse terminal and anchor residue
    necessary conditions. -/
theorem high_far_root_residue_subfamily (k:Nat) :
    let m := 8*k+6
    let n := 24*k+22
    let t := highFarT m
    let R := 2*t-(n+6)
    CounterReach R 1 (n+1) (t+1) t ∧
      t%384=37 ∧ R%24=22 := by
  dsimp only
  let m := 8*k+6
  let n := 24*k+22
  let t := highFarT m
  let R := 2*t-(n+6)
  have hN : highFarN m = n := by
    dsimp [m,n,highFarN]
    omega
  have hr0 := high_far_infinite_family m
  dsimp only at hr0
  rw [hN] at hr0
  have hm2 : m%2=0 := by dsimp [m]; omega
  have hmod := highFarT_mod384 m
  have ht384 : t%384=37 := by
    dsimp [t]
    rcases hmod with h0 | h1
    · exact h0.2
    · omega
  have hn4 : 4≤n := by dsimp [n]; omega
  have heq : 7*t=2^(n+4)+3 := by
    dsimp [t]
    rw [← hN]
    exact highFarT_equation m
  have hlin := exp_linear_bound n hn4
  have hEpow : 2^(n+4)=4*2^(n+2) := by
    rw [show n+4=2+(n+2) by omega, Nat.pow_add]
  have hbound : n+6≤2*t := by
    rw [hEpow] at heq
    omega
  have hRrel : R+n+6=2*t := by
    dsimp [R]
    omega
  have ht24 : t%24=13 := by omega
  have hR24 : R%24=22 := by
    dsimp [n] at hRrel
    omega
  exact ⟨hr0,ht384,hR24⟩

#eval highFarT 6

#print axioms highRun_of_bound
#print axioms high_far_terminal_family
#print axioms highFarT_equation
#print axioms high_far_infinite_family
#print axioms highFarT_mod384
#print axioms high_far_root_residue_subfamily
end BB6.Agent31F321HighFarFamily
