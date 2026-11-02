import SpaceNeedleClosed
import Lean.Elab.Tactic.Omega

namespace BB6.Agent48.SpaceNeedle
open BusyBeaver
open BusyBeaver.M_1RB1LA_1LC0RE_1LF1LD_0RB0LA_1RC1RE_HHH0LD

private theorem iterate_bind_right {S : Type} (f : S → Option S)
    (n : Nat) (x : Option S) :
    Nat.iterate (fun z : Option S => z.bind f) (n+1) x =
      (Nat.iterate (fun z : Option S => z.bind f) n x).bind f := by
  rw [Nat.add_comm n 1, Function.iterate_add_apply]
  rfl

private theorem generic_collatz_terminal {S : Type} (f : S → Option S) (s₀ : S) :
    CollatzHalts f s₀ ↔
      ∃ s, CollatzReachesStar f s₀ s ∧ f s=none := by
  constructor
  · rintro ⟨n,hn⟩
    induction n with
    | zero => simp [Nat.iterate,Option.isNone] at hn
    | succ n ih =>
        rw [iterate_bind_right] at hn
        cases hr : Nat.iterate (fun z : Option S => z.bind f) n (some s₀) with
        | none =>
            have hprev : (Nat.iterate (fun z : Option S => z.bind f) n (some s₀)).isNone := by
              simp [hr]
            exact ih hprev
        | some s =>
            refine ⟨s,⟨n,?_⟩,?_⟩
            · exact hr
            · cases hf : f s with
              | none => rfl
              | some t => simp [hr,hf] at hn
  · rintro ⟨s,⟨n,hr⟩,hf⟩
    refine ⟨n+1,?_⟩
    rw [iterate_bind_right,hr]
    simp [hf]

def ReachN (d : Nat) : Prop :=
  CollatzReachesStar highLevelNext highLevelStart (.N d)

/-- The exact high-level halting criterion identifies the first attempted
power-of-two terminal state on the actual blank-entry orbit. -/
theorem highLevel_halts_iff_power :
    CollatzHalts highLevelNext highLevelStart ↔
    ∃ d k : Nat, ReachN d ∧ d+2=2^(k+1) := by
  rw [generic_collatz_terminal]
  constructor
  · rintro ⟨s,hs,hn⟩
    cases s with
    | N d =>
        have hnil : scanEven d 0=none := hn
        rcases (scanEven_none_iff d 0).mp hnil with ⟨k,hk⟩
        refine ⟨d,k,hs,?_⟩
        rw [hk]
        exact haltTower_power k
  · rintro ⟨d,k,hd,hpower⟩
    have htarget : d=haltTower k := by
      have hsize := haltTower_power k
      omega
    refine ⟨.N d,hd,?_⟩
    change scanEven d 0=none
    apply (scanEven_none_iff d 0).mpr
    exact ⟨k,htarget⟩

/-- The real six-state blank-tape halting problem is equivalent to reaching
one of the exact power-of-two target counters in the published certified
one-counter acceleration. -/
theorem original_raw_halts_iff_power :
    IsHalt target ↔ ∃ d k : Nat, ReachN d ∧ d+2=2^(k+1) :=
  isHalt_iff_highLevel_acceleration.trans highLevel_halts_iff_power

#print axioms generic_collatz_terminal
#print axioms highLevel_halts_iff_power
#print axioms original_raw_halts_iff_power
end BB6.Agent48.SpaceNeedle
