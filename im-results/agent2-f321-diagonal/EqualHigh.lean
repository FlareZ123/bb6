import Phase12
import Phase6Bridge
import BulkRuns
import F321BackwardBarrier
import Lean.Elab.Tactic.Omega

namespace BB6.Agent2F321EqualHigh
open BB6.Agent31F321Density
open BB6.Agent2F321Diagonal
open BB6.Agent2F321Bulk
open BB6.Agent2F321Phase6Bridge
open BB6.Agent2F321Phase12

theorem counterReach_append
    {sa sd n a d m A D : Nat}
    (h1 : CounterReach sa sd n a d)
    (h2 : CounterReach a d m A D) :
    CounterReach sa sd (n+m) A D := by
  induction h2 with
  | nil => simpa using h1
  | step hr hm ih =>
      have hs := CounterReach.step ih hm
      simpa [Nat.add_assoc] using hs

theorem highRun_counterReach {k a d A D : Nat}
    (h : HighRun k a d A D) :
    CounterReach a d k A D := by
  induction h with
  | nil a d => exact CounterReach.nil
  | @step k a d A D hg tail ih =>
      have hfirst : CounterReach a d 1 (a-d-2) (2*d+3) :=
        CounterReach.step CounterReach.nil (CounterMove.high d hg)
      simpa using counterReach_append hfirst ih

theorem reachable_equal_mod12 {n a : Nat}
    (hn : 0 < n)
    (hr : CounterReach 1 1 n a a) :
    a % 12 = 5 ∨ a % 12 = 2 := by
  have hp := root_phase12 (counterReach_to_reach hr)
  rcases hp with hseed | hp
  · omega
  · unfold Phase12 at hp
    rcases hp with hodd | h40 | h42
    · exact Or.inl (by omega)
    · omega
    · rcases h42.2 with hd1 | hd2
      · omega
      · exact Or.inr (by omega)

theorem reachable_equal_anchor_mod24 {n a : Nat}
    (hn : 0 < n)
    (hr : CounterReach 1 1 n a a) :
    (2*a+4) % 24 = 14 ∨ (2*a+4) % 24 = 8 := by
  rcases reachable_equal_mod12 hn hr with h5 | h2
  · left; omega
  · right; omega

theorem equal_high_terminal_length_mod24
    {n k a A D : Nat}
    (hn : 0 < n)
    (hr : CounterReach 1 1 n a a)
    (hh : HighRun k (2*a+4) 1 A D)
    (ht : A = D + 1) :
    k % 24 = 12 ∨ k % 24 = 18 := by
  have hanchor : CounterReach 1 1 (n+1) (2*a+4) 1 :=
    CounterReach.step hr (CounterMove.equal a)
  have htail := highRun_counterReach hh
  have hroot : CounterReach 1 1 ((n+1)+k) A D :=
    counterReach_append hanchor htail
  have hD6 : D % 6 = 1 := by
    apply counterReach_terminal_mod6 (n:=((n+1)+k)) (d:=D)
    · omega
    · simpa [ht] using hroot
  have hterm := high_run_terminal_equation hh ht
  have hcoord := (high_run_coordinates hh).2
  unfold X Y at hterm hcoord
  have hparam : D + 3 = 4 * 2^k := by
    omega
  have hp3 : (2^k) % 3 = 1 := by
    omega
  have hk3 : k % 3 = 0 := by
    have hR := reachable_equal_anchor_mod24 hn hr
    rcases hR with h14 | h8
    · omega
    · omega
  have hR := reachable_equal_anchor_mod24 hn hr
  rcases hR with h14 | h8
  · left
    omega
  · right
    omega

theorem equal_high_terminal_parameter
    {k a A D : Nat}
    (hh : HighRun k (2*a+4) 1 A D)
    (ht : A = D + 1) :
    D + 3 = 4 * 2^k := by
  have hcoord := (high_run_coordinates hh).2
  unfold Y at hcoord
  omega

#print axioms reachable_equal_mod12
#print axioms equal_high_terminal_length_mod24
#print axioms equal_high_terminal_parameter
end BB6.Agent2F321EqualHigh
