import ForwardBlock
import ForwardHalt
namespace BB6.Agent43ForwardSource
open BB6.Agent28Forward
abbrev B := BB6.Agent43ForwardBlock.run
abbrev R := BB6P1Unit.run
abbrev bit := BB6P1Unit.bit
abbrev unit := BB6P1Unit.unit

theorem run_eq (q v k : Nat) : B q v k = R q v k := by
  induction k with
  | zero => rfl
  | succ k ih =>
    simp only [BB6.Agent43ForwardBlock.run, BB6P1Unit.run, ih]
    rfl

/-- Expanded orbit states either are actual source macro boundaries or are
    ordinary zero-wrap prefixes of the next genuine regular macro. -/
inductive Expanded : Nat → Nat → Prop where
  | boundary {q v : Nat} : MacroReach q v → Expanded q v
  | pending {q v : Nat} (i : Nat) : MacroReach q v → 3≤v →
      (∀ j, j<i → bit (q+j) (R q v j)=0) →
      Expanded (q+i) (R q v i)

theorem prefix_advance {q v : Nat} (i : Nat) (hr : MacroReach q v)
    (hv : 3≤v) (hz : ∀ j, j<i → bit (q+j) (R q v j)=0) :
    Expanded (q+i+1) (unit (q+i) (R q v i)) := by
  by_cases h : bit (q+i) (R q v i)=0
  · have hz' : ∀ j, j<i+1 → bit (q+j) (R q v j)=0 := by
      intro j hj
      by_cases he : j=i
      · subst j; exact h
      · exact hz j (by omega)
    have hp := Expanded.pending (i+1) hr hv hz'
    simpa only [Nat.add_assoc,BB6P1Unit.run] using hp
  · have hb : bit (q+i) (R q v i)=1 := by
      unfold BB6P1Unit.bit at *
      split at h <;> simp_all
    have hf : firstWrap q v (i+1) := by
      refine ⟨by omega,?_,?_⟩
      · intro j hj; exact hz j (by omega)
      · simpa using hb
    have hw : Wrap q v (q+(i+1)) (R q v (i+1)) := ⟨i+1,hf,rfl,rfl⟩
    have hn : Next q v (some (q+(i+1),R q v (i+1))) := by
      simp only [Next,show v≠0 by omega,show v≠1 by omega,show v≠2 by omega,if_false]
      exact ⟨_,_,hw,rfl⟩
    have he := Expanded.boundary (MacroReach.next q v _ _ hr hn)
    simpa only [Nat.add_assoc,BB6P1Unit.run] using he

theorem expanded_step {q v : Nat} (he : Expanded q v) (hv : 3≤v) :
    Expanded (q+1) (unit q v) := by
  cases he with
  | boundary hr =>
    have h := prefix_advance 0 hr hv (by intro j hj; omega)
    simpa only [Nat.add_zero,BB6P1Unit.run] using h
  | pending i hr hv' hz => exact prefix_advance i hr hv' hz

theorem small_is_boundary {q v : Nat} (he : Expanded q v) (hv : v≤2) :
    MacroReach q v := by
  cases he with
  | boundary hr => exact hr
  | @pending q v i hr hv' hz =>
    have hvq := macro_reach_valid hr
    unfold valid at hvq
    have hp := BB6P1Unit.run_zero_prefix q v i (by omega) hz
    have hpos := Nat.two_pow_pos i
    have hm := Nat.mul_le_mul_right v (show 1≤2^i by omega)
    simp only [Nat.one_mul] at hm
    omega

theorem expanded_block {q v : Nat} (he : Expanded q v) (k : Nat)
    (hs : ∀ i, i<k → 3≤R q v i) :
    Expanded (q+k) (R q v k) := by
  induction k with
  | zero => simpa only [Nat.add_zero,BB6P1Unit.run] using he
  | succ k ih =>
    have hp := ih (fun i hi => hs i (by omega))
    have hn := expanded_step hp (hs k (by omega))
    simpa only [Nat.add_assoc,BB6P1Unit.run] using hn

theorem fast_block {q v k : Nat} (he : Expanded q v) (hq : 0<q)
    (hv : v<q) (hv3 : 3≤v) (hf : 2^(k+1)≤q)
    (hs : BB6.Agent43ForwardBlock.fastWord q v k=0 ∨
      ∃ r a, BB6.Agent43ForwardBlock.fastWord q v k=2^r*(2*a+1) ∧
        2*2^r<BB6.Agent43ForwardBlock.fastRun q v k) :
    Expanded (q+k) (BB6.Agent43ForwardBlock.fastRun q v k) := by
  have hw := BB6.Agent43ForwardBlock.fastWord_eq q v k hq hv hf
  have hr := BB6.Agent43ForwardBlock.fastRun_eq q v k hq hv hf
  have hall : ∀ i, 0<i → i≤k → 2<B q v i := by
    rcases hs with h|⟨r,a,h,h'⟩
    · exact BB6.Agent43ForwardBlock.no_small_of_zero_word q v k hq hv hv3 (hw ▸ h)
    · exact BB6.Agent43ForwardBlock.no_small_of_lowbit q v k r a hf (hw ▸ h) (hr ▸ h')
  rw [hr,run_eq]
  apply expanded_block he
  intro i hi
  by_cases h : i=0
  · subst i; exact hv3
  · have hh := hall i (by omega) (by omega)
    rw [run_eq] at hh
    omega

#print axioms run_eq
#print axioms prefix_advance
#print axioms expanded_step
#print axioms small_is_boundary
#print axioms expanded_block
#print axioms fast_block
end BB6.Agent43ForwardSource
