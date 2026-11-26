import NeedleAllOrderGrowth
import NeedleGrowthScan

namespace BB6.Agent20.SpaceNeedleAllOrder
open BusyBeaver.M_1RB1LA_1LC0RE_1LF1LD_0RB0LA_1RC1RE_HHH0LD
open BB6.Agent48.SpaceNeedle
open BB6.Agent20.SpaceNeedleGrowthScan
open BB6.Agent20.SpaceNeedleGrowth

private def rootRun (n : Nat) : Option HighLevelState :=
  runFrom (some highLevelStart) n

private theorem rootRun_iter (n : Nat) :
    rootRun n = Nat.iterate
      (fun z : Option HighLevelState => z.bind highLevelNext)
      n (some highLevelStart) := by
  induction n with
  | zero => rfl
  | succ n ih =>
      change (rootRun n).bind highLevelNext = _
      rw [ih]
      rw [Nat.add_comm n 1, Function.iterate_add_apply]
      rfl

private theorem rootRun_prefix (n : Nat) :
    ∀ i, i≤n → (∃ d, rootRun n=some (.N d)) →
      ∃ d, rootRun i=some (.N d) := by
  induction n with
  | zero =>
    intro i hi hd
    have heq : i=0 := by omega
    subst i
    exact hd
  | succ n ih =>
    intro i hi hd
    by_cases heq : i=n+1
    · simpa [heq] using hd
    · obtain ⟨d,hdn⟩ := hd
      have hprev : ∃ p, rootRun n=some (.N p) := by
        change (rootRun n).bind highLevelNext=some (.N d) at hdn
        cases hr : rootRun n with
        | none => simp [hr] at hdn
        | some st => cases st with | N p => exact ⟨p,rfl⟩
      exact ih i (by omega) hprev

private def counterAt (i : Nat) : Nat :=
  match rootRun i with
  | some (.N d) => d
  | none => 0

private theorem counterAt_spec (i d : Nat)
    (hr : rootRun i=some (.N d)) : counterAt i=d := by
  simp [counterAt,hr]

private theorem root_edge_exists (d n : Nat)
    (hr : rootRun n=some (.N d)) (i : Nat) (hi : i<n) :
    ∃ v, NeedleTerminalExtension.Edge v (counterAt i+2) (counterAt (i+1)+2) := by
  obtain ⟨p,hp⟩ := rootRun_prefix n i (by omega) ⟨d,hr⟩
  obtain ⟨e,he⟩ := rootRun_prefix n (i+1) (by omega) ⟨d,hr⟩
  have hs : highLevelNext (.N p)=some (.N e) := by
    have hh := he
    change (rootRun i).bind highLevelNext=some (.N e) at hh
    rw [hp] at hh
    simpa using hh
  obtain ⟨q,v,hx,hy⟩ := original_edge p e hs
  rw [counterAt_spec i p hp,counterAt_spec (i+1) e he]
  exact ⟨v,q,hx,hy⟩

/-- Every authentic blank-root return to a specified d has a rigorous
subexponential high-level transition cutoff in its bit length. -/
theorem original_iterate_all_order_bound (d n : Nat)
    (hr : Nat.iterate (fun z : Option HighLevelState => z.bind highLevelNext)
      n (some highLevelStart)=some (.N d)) :
    n<NeedleAllOrderGrowth.targetFuel d := by
  have hrr : rootRun n=some (.N d) := by rwa [rootRun_iter]
  let v : Nat→Nat := fun i => if hi : i<n then Classical.choose (root_edge_exists d n hrr i hi) else 0
  have he : ∀ i, i<n → NeedleTerminalExtension.Edge (v i) (counterAt i+2) (counterAt (i+1)+2) := by
    intro i hi
    simpa [v,hi] using Classical.choose_spec (root_edge_exists d n hrr i hi)
  exact NeedleAllOrderGrowth.prefix_target_fuel v (fun i=>counterAt i+2) d n
    (by omega) he (by rw [counterAt_spec n d hrr])

/-- Exact executable root membership with the all-order growth bound. -/
def allOrderScan (d : Nat) : Bool :=
  scan d (NeedleAllOrderGrowth.targetFuel d) (some highLevelStart)

theorem allOrderScan_spec (d : Nat) : allOrderScan d=true ↔ ReachN d := by
  rw [allOrderScan,scan_spec]
  constructor
  · rintro ⟨n,_,hn⟩
    refine ⟨n,?_⟩
    change Nat.iterate (fun z : Option HighLevelState => z.bind highLevelNext)
      n (some highLevelStart)=some (.N d)
    rw [←rootRun_iter]
    exact hn
  · rintro ⟨n,hn⟩
    refine ⟨n,original_iterate_all_order_bound d n hn,?_⟩
    change rootRun n=some (.N d)
    rw [rootRun_iter]
    exact hn

#print axioms original_iterate_all_order_bound
#print axioms allOrderScan_spec
end BB6.Agent20.SpaceNeedleAllOrder
