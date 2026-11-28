import TerminalWordLastFar
import AnchorEpoch
import Phase12
import Lean.Elab.Tactic.Omega

/-!
Root-specific endpoint sharpening for the F321 last-anchor decomposition.

The generic AnchorEpoch endpoint theorem records only that the small second
counter is 1 or 2 and gives weak congruences on the first counter. Here we
transport the already proved root Phase6/Phase12 invariants to the predecessor
of the final anchor move and obtain a substantially sharper residue condition.
-/

namespace BB6.Agent31F321AnchorShape
open BB6.Agent31F321Density
open BB6.Agent2F321AnchorEpoch
open BB6.Agent2F321Phase6
open BB6.Agent2F321Phase6Bridge
open BB6.Agent2F321Phase12

theorem counterReach_append_local
    {sa sd n a d m A D : Nat}
    (h₁ : CounterReach sa sd n a d)
    (h₂ : CounterReach a d m A D) :
    CounterReach sa sd (n+m) A D := by
  induction h₂ with
  | nil => simpa using h₁
  | step hr hm ih =>
      simpa [Nat.add_assoc] using CounterReach.step ih hm

theorem six_reach_to_root
    {n A D : Nat}
    (h : CounterReach 6 1 n A D) :
    CounterReach 1 1 (n+1) A D := by
  have hseed : CounterReach 1 1 1 6 1 :=
    CounterReach.step CounterReach.nil (CounterMove.equal 1)
  have hall := counterReach_append_local hseed h
  simpa [Nat.add_comm] using hall

/-- Every abstract AnchorChain from the canonical post-seed anchor is backed by
    a genuine source-counter reachability path. -/
theorem anchorChain_six_reach
    {q R c : Nat}
    (h : AnchorChain q 6 1 R c) :
    ∃ n, CounterReach 6 1 n R c := by
  induction h with
  | nil =>
      exact ⟨0, CounterReach.nil⟩
  | @step q _ _ A e B f hchain hepoch ih =>
      rcases ih with ⟨n,hr⟩
      rcases hepoch with ⟨m,a,d,hhf,ha⟩
      have hhfr : CounterReach A e m a d := hfRun_counterReach hhf
      have hpre : CounterReach 6 1 (n+m) a d :=
        counterReach_append_local hr hhfr
      have hlast : CounterReach a d 1 B f :=
        CounterReach.step CounterReach.nil (anchorMove_source ha)
      have hall := counterReach_append_local hpre hlast
      exact ⟨n+m+1, by simpa [Nat.add_assoc] using hall⟩

/-- Sharp necessary residue classes for a genuine root-reachable anchor output.

For c=1, an Equal anchor lands at R mod 24 in {14,8}, except the initial
post-seed anchor R=6; a MiddleOdd anchor always lands at R=6 mod 8.
For c=2, the Phase12 predecessor split gives R=2 mod 8 or R=14 mod 16.
-/
theorem reachable_anchor_output_strong
    {n a d R c : Nat}
    (hr : CounterReach 1 1 n a d)
    (ha : AnchorMove a d R c) :
    (c=1 ∧ (R%8=6 ∨ R%24=14 ∨ R%24=8)) ∨
    (c=2 ∧ (R%8=2 ∨ R%16=14)) := by
  unfold AnchorMove at ha
  rcases ha with hE | hM
  · rcases hE with ⟨rfl,rfl,rfl⟩
    left
    constructor
    · rfl
    · have hp := root_phase12 (counterReach_to_reach hr)
      rcases hp with hseed | hp
      · left
        omega
      · unfold Phase12 at hp
        rcases hp with hodd | h40 | h42
        · right; left
          omega
        · omega
        · rcases h42.2 with hd1 | hd2
          · omega
          · right; right
            omega
  · rcases hM with hEven | hOdd
    · rcases hEven with ⟨hlo,hhi,hp,rfl,rfl⟩
      right
      constructor
      · rfl
      · have hs := reachable_middleEven_shape
          (counterReach_to_reach hr) hlo hp
        rcases hs with hodd | h42
        · left
          omega
        · right
          omega
    · rcases hOdd with ⟨hlo,hhi,hp,rfl,rfl⟩
      left
      constructor
      · rfl
      · left
        have hs := counterReach_middleOdd_shape hr hlo hp
        omega

/-- Every last anchor appearing in the canonical root chain satisfies the
    sharper residue classification above. -/
theorem root_anchorChain_strong_shape
    {q R c : Nat}
    (h : AnchorChain q 6 1 R c) :
    (c=1 ∧ (R%8=6 ∨ R%24=14 ∨ R%24=8)) ∨
    (c=2 ∧ (R%8=2 ∨ R%16=14)) := by
  cases h with
  | nil =>
      left
      exact ⟨rfl, Or.inl (by decide)⟩
  | @step q _ _ A e B f hchain hepoch =>
      rcases hepoch with ⟨m,a,d,hhf,ha⟩
      rcases anchorChain_six_reach hchain with ⟨n,hr6⟩
      have hrA : CounterReach 1 1 (n+1) A e :=
        six_reach_to_root hr6
      have hhfr : CounterReach A e m a d := hfRun_counterReach hhf
      have hrpre : CounterReach 1 1 ((n+1)+m) a d :=
        counterReach_append_local hrA hhfr
      exact reachable_anchor_output_strong hrpre ha

/-- Integrated terminal normal form: the exact final inverse word reaches a
    genuine root anchor in one of the sharp residue classes. -/
theorem terminal_last_anchor_strong_shape
    {n D : Nat}
    (h : CounterReach 1 1 (n+1) (D+1) D) :
    ∃ q R c m w,
      AnchorChain q 6 1 R c ∧
      (c=1 ∨ c=2) ∧
      w.length=m ∧
      FormalInversePath (D:Int) w (R:Int) (c:Int) ∧
      ((c=1 ∧ (R%8=6 ∨ R%24=14 ∨ R%24=8)) ∨
       (c=2 ∧ (R%8=2 ∨ R%16=14))) := by
  rcases terminal_has_last_anchor_formal_word h with
    ⟨q,R,c,m,w,hchain,hc,hlen,hw⟩
  exact ⟨q,R,c,m,w,hchain,hc,hlen,hw,
    root_anchorChain_strong_shape hchain⟩

#print axioms reachable_anchor_output_strong
#print axioms anchorChain_six_reach
#print axioms root_anchorChain_strong_shape
#print axioms terminal_last_anchor_strong_shape
end BB6.Agent31F321AnchorShape
