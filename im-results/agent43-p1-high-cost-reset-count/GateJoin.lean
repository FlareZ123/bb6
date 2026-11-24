import EarlyGate
import ResetGate
import ForwardHalt
namespace BB6.Agent43GateJoin
open BB6.Agent1 BB6.Agent43Early BB6.Agent28Forward

def gate (n : Nat) := 14*2^n-2*n-10
def clock (n : Nat) := 7*2^n-n-3
def excluded (n : Nat) : Prop := ¬ Reach 2 (gate n)
def survivor (n : Nat) : Bool := [30,286,350,1614,2990,3342].contains n

theorem no_odd_gate (n : Nat) (ho : n%2=1) : excluded n := by
  by_cases hsmall : n≤12
  · exact no_small_gate n hsmall
  · intro hr
    obtain ⟨hd,hmod,hgap⟩ := odd_gate_arithmetic n (by omega) ho
    obtain ⟨j,hj⟩ := reset_four_power (gate n) hr hd hmod
    exact hgap j hj

theorem macro_gate_to_reset (n : Nat) (h : MacroReach (clock n) 1) : Reach 2 (gate n) := by
  have hv := macro_reach_valid h
  unfold valid at hv
  have hw := right_three (clock n) (by omega)
  have hr := hw.reach (macro_reach_source h)
  change Reach 2 (2*(clock n-2)) at hr
  have he : 2*(clock n-2)=gate n := by unfold clock gate; omega
  rwa [he] at hr

/-- Compose any certified even-index prefix with the all-odd/small proof.
    The missing quantifier is exactly the remaining critical indices. -/
theorem halt_iff_remaining (B : Nat)
    (hcover : ∀ n, 14≤n → n≤B → n%2=0 → excluded n) :
    SourceHalt (2,1) ↔ ∃ n, B<n ∧ n%2=0 ∧ MacroReach (clock n) 1 := by
  constructor
  · intro h
    obtain ⟨n,hn⟩ := blank_critical_clock_iff.mp h
    change MacroReach (clock n) 1 at hn
    have hr := macro_gate_to_reset n hn
    have he : n%2=0 := by
      by_cases he : n%2=0
      · exact he
      · exact False.elim (no_odd_gate n (by omega) hr)
    have hsmall : 14≤n := by
      by_cases h : 14≤n
      · exact h
      · exact False.elim (no_small_gate n (by omega) hr)
    have hlarge : B<n := by
      by_cases h : B<n
      · exact h
      · exact False.elim (hcover n hsmall (by omega) he hr)
    exact ⟨n,hlarge,he,hn⟩
  · rintro ⟨n,_,_,hn⟩
    exact blank_critical_clock_iff.mpr ⟨n,hn⟩

/-- Exact logical combination of the modular screen and six full-P results.
    The premises are the actual theorem interfaces, not Boolean verdicts. -/
theorem full_finite_cover
    (hmod : ∀ n, 14≤n → n≤10000 → n%2=0 → survivor n=false → excluded n)
    (h30 : excluded 30) (h286 : excluded 286) (h350 : excluded 350)
    (h1614 : excluded 1614) (h2990 : excluded 2990) (h3342 : excluded 3342) :
    ∀ n, 14≤n → n≤10000 → n%2=0 → excluded n := by
  intro n hlo hhi he
  by_cases hs : survivor n=false
  · exact hmod n hlo hhi he hs
  · have ht : survivor n=true := by cases h : survivor n <;> simp_all
    simp [survivor] at ht
    rcases ht with rfl|rfl|rfl|rfl|rfl|rfl
    · exact h30
    · exact h286
    · exact h350
    · exact h1614
    · exact h2990
    · exact h3342

#print axioms no_odd_gate
#print axioms macro_gate_to_reset
#print axioms halt_iff_remaining
#print axioms full_finite_cover
end BB6.Agent43GateJoin
