import Mass

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace CascadeManyShield
open CascadeSource

/-- The remaining two modulo-six source-episode fatal reset classes. -/
def fatal (n : Nat) : Nat := 4*2^n-n-4

def badThrough (bound : Nat) (s : Nat × Nat) : Bool :=
  decide (s.2 = 0) && (List.range (bound+1)).any (fun i =>
    decide (4 ≤ i ∧ (i%6=4 ∨ i%6=5) ∧ s.1=fatal i))

/-- Check a prefix until its strictly monotone mass exceeds the entire
    bounded target family. The checker never assumes orbit totality. -/
def shieldMany (bad : Nat × Nat → Bool) (cap : Nat) : Nat → Nat × Nat → Bool
  | 0, s => decide (cap < mass s)
  | fuel+1, s =>
    if bad s then false
    else if cap < mass s then true
    else match Cstep s.1 s.2 with
      | none => true
      | some u => shieldMany bad cap fuel u

/-- Any successfully checked prefix excludes all predicate targets below cap
    from the *entire* orbit, by strict mass monotonicity. -/
theorem shieldMany_sound (bad : Nat × Nat → Bool) (cap : Nat) :
    ∀ fuel s t, bad t = true → mass t ≤ cap →
      shieldMany bad cap fuel s = true → ¬Orbit s t := by
  intro fuel
  induction fuel with
  | zero =>
    intro s t hb hm hc ho
    have hc' : cap < mass s := by
      simpa [shieldMany] using hc
    have hg := orbit_mass_mono ho
    omega
  | succ fuel ih =>
    intro s t hb hm hc ho
    have hbad : bad s = false := by
      by_cases hs : bad s = true
      · simp [shieldMany, hs] at hc
      · cases hb' : bad s <;> simp_all
    by_cases hcut : cap < mass s
    · have hg := orbit_mass_mono ho
      omega
    · cases hstep : Cstep s.1 s.2 with
      | none =>
        cases ho with
        | refl => simp [hb] at hbad
        | step he _ => simp [hstep] at he
      | some u =>
        have hchild : shieldMany bad cap fuel u = true := by
          simpa [shieldMany, hbad, hcut, hstep] using hc
        cases ho with
        | refl => simp [hb] at hbad
        | step he htail =>
          rw [hstep] at he
          have hEq := Option.some.inj he
          rcases u with ⟨u1,u2⟩
          cases hEq
          exact ih _ _ hb hm hchild htail

/-- All surviving-class fatal heights through index 100 are globally absent
    from the actual post-initial copied-source C(2,0) orbit. -/
theorem blank_excludes_surviving_fatal_through_100 (n : Nat)
    (hn : 4 ≤ n) (ht : n ≤ 100) (hres : n%6=4∨n%6=5) :
    ¬Orbit (2,0) (fatal n,0) := by
  have hbad : badThrough 100 (fatal n,0) = true := by
    have hall : ∀ i : Fin 101, (4 ≤ i.val) →
        (i.val%6=4∨i.val%6=5) →
        badThrough 100 (fatal i.val,0)=true := by decide
    exact hall ⟨n,by omega⟩ hn hres
  have hmass : mass (fatal n,0) ≤ 2*fatal 100 := by
    have hall : ∀ i : Fin 101, mass (fatal i.val,0) ≤ 2*fatal 100 := by decide
    exact hall ⟨n,by omega⟩
  exact shieldMany_sound (badThrough 100) (2*fatal 100) 7000 (2,0)
    (fatal n,0) hbad hmass (by decide)

#print axioms shieldMany_sound
#print axioms blank_excludes_surviving_fatal_through_100
end CascadeManyShield
