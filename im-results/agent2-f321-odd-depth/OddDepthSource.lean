import F321BackwardBarrier
import Lean.Elab.Tactic.Omega

/-!
A source-counter (not original-TM) uniform inverse obstruction for the
previously missing odd-depth base-four digit-1 terminal ray of F321.
The type CounterMove below is the *existing* source map, not a new
independently chosen dynamical system.
-/

namespace BB6.Agent2F321OddDepth
open BB6.Agent31F321Density

def coeff : Nat → Nat
  | 0 => 13
  | n+1 => 4*coeff n+9

def shift : Nat → Nat
  | 0 => 0
  | n+1 => shift n+2*coeff n

def twos : Nat → Nat → Nat
  | 0,k => k
  | n+1,k => 4*twos n k+2

theorem coeff_ge (n:Nat) : 13 ≤ coeff n := by
  induction n with
  | zero => decide
  | succ n ih =>
    change 13 ≤ 4*coeff n+9
    omega

theorem coeff_mod4 (n:Nat) : coeff n % 4 = 1 := by
  induction n with
  | zero => decide
  | succ n ih =>
    change (4*coeff n+9)%4=1
    omega

theorem shift_mod4 (n:Nat) : shift n % 4 = 2*(n%2) := by
  induction n with
  | zero => decide
  | succ n ih =>
    change (shift n+2*coeff n)%4=2*((n+1)%2)
    have hc := coeff_mod4 n
    omega

theorem twos_pos (n k:Nat) (hk:1≤k) : 1 ≤ twos n k := by
  induction n with
  | zero => simpa [twos] using hk
  | succ n ih =>
    change 1 ≤ 4*twos n k + 2
    omega

/-- No authentic source-counter orbit can visit an output with odd first
coordinate and second coordinate 3 mod 4: its sole inverse is an
odd/even, predecessor-free pair, not the seed. -/
theorem odd_three_dead (A D:Nat)
    (ha:A%2=1) (hd:D%4=3) :
    ∀ n, ¬ CounterReach 1 1 n A D := by
  intro n hr
  cases hr with
  | nil => omega
  | step hr hm =>
    have hlarge : 3 ≤ D := by omega
    rcases large_second_only_high_far hm hlarge with hh | hf
    · cases hr with
      | nil => omega
      | step hr2 hm2 =>
        cases hm2 with
        | high hg => omega
        | equal => omega
        | far h1 h2 => omega
        | middleEven h1 h2 hp => omega
        | middleOdd h1 h2 hp => omega
    · omega

/-- A 3 mod 8 terminal gate can only have a seed ancestry through Q0(k).
    This is a complete two-step inverse, not a sampled root trace. -/
theorem gate_to_Q0 (k:Nat) (hk:1≤k) :
    ∀ n, CounterReach 1 1 n (8*k+4) (8*k+3) →
      ∃ m, CounterReach 1 1 m (3*k) (13*k) := by
  intro n hr
  cases hr with
  | nil => omega
  | step hr hm =>
    have hlarge : 3 ≤ 8*k+3 := by omega
    rcases large_second_only_high_far hm hlarge with hh | hf
    · cases hr with
      | nil => omega
      | step hr2 hm2 =>
        have hmid : 3 ≤ 4*k := by omega
        rcases large_second_only_high_far hm2 hmid with hh2 | hf2
        · omega
        ·          refine ⟨_, ?_⟩
          convert hr2 using 1 <;> omega
    · omega

/-- A Q_i(4k+2) output has a single far predecessor Q_(i+1)(k). -/
theorem peel (i k:Nat) :
    ∀ n, CounterReach 1 1 n (3*(4*k+2))
       (coeff i*(4*k+2)+shift i) →
       ∃ m, CounterReach 1 1 m (3*k)
         ((4*coeff i+9)*k+(shift i+2*coeff i)) := by
  intro n hr
  have hge : 13 ≤ coeff i := coeff_ge i
  have hd : 3 ≤ coeff i*(4*k+2)+shift i := by
    have hmul : 2*coeff i ≤ (4*k+2)*coeff i :=
      Nat.mul_le_mul_right (coeff i) (by omega)
    omega
  have heven : (coeff i*(4*k+2)+shift i)%2=0 := by
    have hc := shift_mod4 i
    have he : (4*k+2)%2=0 := by omega
    simp [Nat.add_mod, Nat.mul_mod, he]
    omega
  cases hr with
  | nil => omega
  | step hp hm =>
    rcases large_second_only_high_far hm hd with hh | hf
    · omega
    · have hpoly :
        (4*coeff i+9)*k+(shift i+2*coeff i) =
           coeff i*(4*k+2)+shift i+9*k := by
        simp [Nat.add_mul, Nat.mul_add, Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm]
        omega
      refine ⟨_, ?_⟩
      convert hp using 1 <;> omega

/-- All t forced low base-four digit-2 inversions are valid exactly as
    symbolic source-counter transformations. -/
theorem peel_twos (i t k:Nat) :
    ∀ n, CounterReach 1 1 n (3*twos t k)
         (coeff i*twos t k+shift i) →
      ∃ m, CounterReach 1 1 m (3*k)
        (coeff (i+t)*k+shift (i+t)) := by
  induction t generalizing i with
  | zero =>
    intro n hr
    exact ⟨n, by simpa [twos] using hr⟩
  | succ t ih =>
    intro n hr
    have hstep : CounterReach 1 1 n (3*(4*twos t k+2))
      (coeff i*(4*twos t k+2)+shift i) := by simpa [twos] using hr
    obtain ⟨m,hm⟩ := peel i (twos t k) n hstep
    have hnext : CounterReach 1 1 m (3*twos t k)
      (coeff (i+1)*twos t k+shift (i+1)) := by
      simpa only [coeff,shift] using hm
    obtain ⟨p,hp⟩ := ih (i+1) m hnext
    exact ⟨p, by simpa [Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using hp⟩

/-- Exact new infinite counter-gate exclusion: odd t and base-four
    digits 2^t followed by 1. Not a complete F321 machine decision. -/
theorem odd_depth_gate_never (t m:Nat) (ht:t%2=1) :
   ∀ n, ¬ CounterReach 1 1 n
      (8*twos t (4*m+1)+4) (8*twos t (4*m+1)+3) := by
  intro n hr
  let k := twos t (4*m+1)
  have hk : 1≤k := twos_pos t (4*m+1) (by omega)
  obtain ⟨p,hp⟩ := gate_to_Q0 k hk n (by simpa [k] using hr)
  have h0 : CounterReach 1 1 p (3*twos t (4*m+1))
      (coeff 0*twos t (4*m+1)+shift 0) := by
    simpa [k,coeff,shift] using hp
  obtain ⟨q,hq⟩ := peel_twos 0 t (4*m+1) p h0
  have hc : coeff t % 4 = 1 := coeff_mod4 t
  have hs : shift t % 4 = 2 := by
    have he := shift_mod4 t
    omega
  have hA : (3*(4*m+1))%2 = 1 := by omega
  have hD : (coeff t*(4*m+1)+shift t)%4=3 := by
    rw [Nat.add_mod,Nat.mul_mod]
    omega
  have hq' : CounterReach 1 1 q (3*(4*m+1))
       (coeff t*(4*m+1)+shift t) := by
    simpa using hq
  exact odd_three_dead _ _ hA hD q hq'

#print axioms odd_depth_gate_never

end BB6.Agent2F321OddDepth
