import F321BackwardBarrier
import LastFarExact
import Lean.Elab.Tactic.Omega

namespace BB6.Agent2F321TerminalFeeder
open BB6.Agent31F321Density
open BB6.Agent2F321Bulk
open BB6.Agent2F321Diagonal
open BB6.Agent2F321LastFarExact

/-- The four non-High branches, with all guards retained. -/
inductive NonHigh : Nat → Nat → Nat → Nat → Prop where
  | equal (a : Nat) : NonHigh a a (2*a+4) 1
  | far (a d : Nat) (h1 : a<d) (h2 : 3*a+1≤d) :
      NonHigh a d (4*a+6) (d-3*a)
  | middleEven (a d : Nat) (h1 : a<d) (h2 : d<3*a+1) (hp : (d-a)%2=0) :
      NonHigh a d (4*a+6) 2
  | middleOdd (a d : Nat) (h1 : a<d) (h2 : d<3*a+1) (hp : (d-a)%2=1) :
      NonHigh a d (4*a+6) 1

theorem NonHigh.move {a d A D : Nat} (h : NonHigh a d A D) : CounterMove a d A D := by
  cases h with
  | equal => exact CounterMove.equal a
  | far d h1 h2 => exact CounterMove.far a d h1 h2
  | middleEven d h1 h2 hp => exact CounterMove.middleEven a d h1 h2 hp
  | middleOdd d h1 h2 hp => exact CounterMove.middleOdd a d h1 h2 hp

theorem highRun_snoc {n a d A D : Nat} (h : HighRun n a d A D) (hg : D+2≤A) :
    HighRun (n+1) a d (A-D-2) (2*D+3) := by
  induction h with
  | nil a d => exact HighRun.step hg (HighRun.nil _ _)
  | step hg0 _ ih => exact HighRun.step hg0 (ih hg)

theorem highRun_append {s r n b a d A D : Nat}
    (hr : CounterReach s r n a d) (hh : HighRun b a d A D) :
    CounterReach s r (n+b) A D := by
  induction hh generalizing n with
  | nil => simpa using hr
  | @step b a d A D hg _ ih =>
      have h := ih (CounterReach.step hr (CounterMove.high a d hg))
      simpa [Nat.add_assoc, Nat.add_comm 1 b] using h

/-- Every run either consists solely of High steps, or has a last non-High
    branch followed by a pure High suffix. The time equation is exact. -/
theorem last_nonHigh {s r n A D : Nat} (hr : CounterReach s r n A D) :
    HighRun n s r A D ∨
    ∃ m b a d C E, n=m+1+b ∧ CounterReach s r m a d ∧
      NonHigh a d C E ∧ HighRun b C E A D := by
  induction hr with
  | nil => exact Or.inl (HighRun.nil _ _)
  | @step n a d A D hr hm ih =>
      cases hm with
      | high d hg =>
          rcases ih with hh | ⟨m,b,u,v,C,E,hn,hpre,hnon,hh⟩
          · exact Or.inl (highRun_snoc hh hg)
          · exact Or.inr ⟨m,b+1,u,v,C,E,by omega,hpre,hnon,highRun_snoc hh hg⟩
      | equal =>
          exact Or.inr ⟨n,0,a,a,2*a+4,1,by omega,hr,NonHigh.equal a,HighRun.nil _ _⟩
      | far d h1 h2 =>
          exact Or.inr ⟨n,0,a,d,4*a+6,d-3*a,by omega,hr,NonHigh.far a d h1 h2,HighRun.nil _ _⟩
      | middleEven d h1 h2 hp =>
          exact Or.inr ⟨n,0,a,d,4*a+6,2,by omega,hr,NonHigh.middleEven a d h1 h2 hp,HighRun.nil _ _⟩
      | middleOdd d h1 h2 hp =>
          exact Or.inr ⟨n,0,a,d,4*a+6,1,by omega,hr,NonHigh.middleOdd a d h1 h2 hp,HighRun.nil _ _⟩

/-- Exactly the last-branch possibilities for an arbitrary terminal target. -/
def TerminalFeeder (b a d t : Nat) : Prop :=
  (a=d ∧ t+3=2^b*4 ∧ 2*a+b+4=2*t) ∨
  Feeder b a d t ∨
  (a<d ∧ d<3*a+1 ∧ (d-a)%2=0 ∧ t+3=2^b*5 ∧ 4*a+b+7=2*t) ∨
  (a<d ∧ d<3*a+1 ∧ (d-a)%2=1 ∧ t+3=2^b*4 ∧ 4*a+b+6=2*t)

theorem terminalFeeder_iff (b a d t : Nat) : TerminalFeeder b a d t ↔
    ∃ C E, NonHigh a d C E ∧ HighRun b C E (t+1) t := by
  constructor
  · intro h
    rcases h with h | h | h | h
    · rcases h with ⟨rfl,ht,hs⟩
      exact ⟨_,_,NonHigh.equal _,highRun_of_balances (by omega) ht⟩
    · exact ⟨_,_,NonHigh.far _ _ h.1 h.2.1,h.2.2⟩
    · rcases h with ⟨h1,h2,hp,ht,hs⟩
      exact ⟨_,_,NonHigh.middleEven _ _ h1 h2 hp,highRun_of_balances (by omega) ht⟩
    · rcases h with ⟨h1,h2,hp,ht,hs⟩
      exact ⟨_,_,NonHigh.middleOdd _ _ h1 h2 hp,highRun_of_balances (by omega) ht⟩
  · rintro ⟨C,E,hn,hh⟩
    have hc := high_run_coordinates hh
    unfold X Y at hc
    cases hn with
    | equal =>
        left
        have hd : t+3=2^b*4 := by
          have he : 2^b* (2*(1+3))=2*(2^b*4) := by omega
          rw [he] at hc
          omega
        exact ⟨rfl,hd,by omega⟩
    | far d h1 h2 => exact Or.inr (Or.inl ⟨h1,h2,hh⟩)
    | middleEven d h1 h2 hp =>
        right; right; left
        have hd : t+3=2^b*5 := by
          have he : 2^b*(2*(2+3))=2*(2^b*5) := by omega
          rw [he] at hc
          omega
        exact ⟨h1,h2,hp,hd,by omega⟩
    | middleOdd d h1 h2 hp =>
        right; right; right
        have hd : t+3=2^b*4 := by
          have he : 2^b*(2*(1+3))=2*(2^b*4) := by omega
          rw [he] at hc
          omega
        exact ⟨h1,h2,hp,hd,by omega⟩

/-- Full equivalence, for each authentic root-terminal time, with a reachable
    last-non-High feeder. No bounded-depth condition or guessed branch occurs. -/
theorem root_terminal_iff (n t : Nat) : CounterReach 1 1 n (t+1) t ↔
    ∃ m b a d, n=m+1+b ∧ CounterReach 1 1 m a d ∧ TerminalFeeder b a d t := by
  constructor
  · intro hr
    rcases last_nonHigh hr with hh | ⟨m,b,a,d,C,E,hn,hpre,hnon,hh⟩
    · cases hh with
      | step hg _ => omega
    · exact ⟨m,b,a,d,hn,hpre,(terminalFeeder_iff b a d t).mpr ⟨C,E,hnon,hh⟩⟩
  · rintro ⟨m,b,a,d,rfl,hpre,hf⟩
    rcases (terminalFeeder_iff b a d t).mp hf with ⟨C,E,hnon,hh⟩
    exact highRun_append (CounterReach.step hpre hnon.move) hh

/-- Outside the two small-reset dyadic spines, every possible terminal path
    has a unique candidate Far feeder at each trailing High length. -/
theorem root_terminal_far_off_spines {n t : Nat}
    (hr : CounterReach 1 1 n (t+1) t)
    (h4 : ∀ b : Nat, t+3≠2^b*4) (h5 : ∀ b : Nat, t+3≠2^b*5) :
    ∃ m b a d, n=m+1+b ∧ CounterReach 1 1 m a d ∧ Feeder b a d t := by
  rcases (root_terminal_iff n t).mp hr with ⟨m,b,a,d,hn,hpre,hf⟩
  refine ⟨m,b,a,d,hn,hpre,?_⟩
  rcases hf with h | h | h | h
  · exact False.elim (h4 b h.2.1)
  · exact h
  · exact False.elim (h5 b h.2.2.2.1)
  · exact False.elim (h4 b h.2.2.2.1)

#print axioms last_nonHigh
#print axioms terminalFeeder_iff
#print axioms root_terminal_iff
#print axioms root_terminal_far_off_spines
end BB6.Agent2F321TerminalFeeder
