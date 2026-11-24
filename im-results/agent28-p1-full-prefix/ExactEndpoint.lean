import FullPrefix

/-!
# Exact terminal-carry semantics of the original P1 CountCone

One source inverse edge of depth t is represented by one selected bit
followed by exactly t omitted bits. This retains the endpoint (d-1)/2,
unlike the modular-prefix obstruction alone.
-/
namespace BB6.Agent28FullPrefix

open BB6.Agent28 BB6.Agent1Quarter BB6.Agent1UpperTail BB6.Agent47P1
open BB6.Agent43LastResetStrength

theorem fullCarryStates_add (Q j : Nat) (cs : List Nat) (a b : Nat) :
    fullCarryStates Q j cs (a+b) =
      fullCarryStates Q (j+a) (fullCarryStates Q j cs a) b := by
  induction a generalizing j cs with
  | zero => simp [fullCarryStates]
  | succ a ih =>
      rw [Nat.succ_add, fullCarryStates, ih, fullCarryStates]
      congr 1
      omega

theorem fullCarryStates_singleton (Q j : Nat) (cs : List Nat) (v k u : Nat)
    (hv : v ∈ cs) (hu : u ∈ fullCarryStates Q j [v] k) :
    u ∈ fullCarryStates Q j cs k := by
  apply fullCarryStates_mono Q j [v] cs _ k u hu
  intro x hx
  simp at hx
  simpa [hx] using hv

theorem fullCarry_omit_power (Q j u t : Nat) :
    u ∈ fullCarryStates Q j [2^t*u] t := by
  induction t generalizing j with
  | zero => simp [fullCarryStates]
  | succ t ih =>
      have hp : 2^(t+1)*u = 2*(2^t*u) := by
        rw [Nat.pow_succ]
        ac_rfl
      have hm : 2^t*u ∈ fullCarryStep Q j [2^(t+1)*u] := by
        simp [hp, fullCarryStep]
      exact fullCarryStates_singleton Q (j+1) _ _ t u hm (ih (j+1))

theorem fullCarry_block (Q j v u t : Nat)
    (h : v+(Q-j)=2^(t+1)*u) :
    u ∈ fullCarryStates Q j [v] (t+1) := by
  have hp : v+(Q-j)=2*(2^t*u) := by
    rw [h, Nat.pow_succ]
    ac_rfl
  have hm : 2^t*u ∈ fullCarryStep Q j [v] := by
    simp [fullCarryStep, hp]
  exact fullCarryStates_singleton Q (j+1) _ _ t u hm (fullCarry_omit_power Q (j+1) u t)

theorem fullCarry_append_block (Q m v u t : Nat)
    (hprev : v ∈ fullCarryStates Q 0 [1] m)
    (h : v+(Q-m)=2^(t+1)*u) :
    u ∈ fullCarryStates Q 0 [1] (m+t+1) := by
  have hb := fullCarry_block Q m v u t h
  have hm := fullCarryStates_singleton Q m _ v (t+1) u hprev hb
  rw [show m+t+1=m+(t+1) by omega, fullCarryStates_add]
  simpa using hm

/-- Every legal source inverse block determines an exact bit-carry block. -/
theorem exact_endpoint_block_equation (n b d m t c : Nat)
    (hb4 : b%4=0) (hd : d%2=1) (hc : c%2=1)
    (hmass : b+d+2*m+2*n+13=14*2^n)
    (hpower : d+b/2+3=2^t*(c+3)) :
    (d-1)/2 + ((7*2^n-(n+3))-m) = 2^(t+1)*((c+3)/2) := by
  have hpow2 : 2*(d+b/2+3)=2^(t+1)*(c+3) := by
    rw [hpower, Nat.pow_succ]
    ac_rfl
  have hrec : (d-1)+14*2^n = 2^(t+1)*(c+3)+2*(m+n+3) := by
    rw [← hpow2]
    omega
  have hv : d-1=2*((d-1)/2) := by omega
  have hu : c+3=2*((c+3)/2) := by omega
  have hmul : 2^(t+1)*(2*((c+3)/2))=2*(2^(t+1)*((c+3)/2)) := by ac_rfl
  rw [hv, hu, hmul] at hrec
  omega

/-- Exact endpoint transport for every original CountCone, at all costs
    and depths. A right-five endpoint must occur as carry 2, not merely
    satisfy a modular prefix. -/
theorem source_full_carry_endpoint (n b d m z : Nat) (hn : 14≤n)
    (h : CountCone (14*2^n-2*n-16) 3 b d m z) :
    (d-1)/2 ∈ fullCarryStates (7*2^n-(n+3)) 0 [1] m := by
  induction h with
  | root => simp [fullCarryStates]
  | parent bp dp mp zp t k c hp hb hb4 hd hi hk hc ih =>
      have hodd : OddCone (14*2^n-2*n-16) 3 bp dp mp :=
        counted_to_odd_cone _ _ _ _ _ _ hp
      have hmass0 := odd_cone_mass _ _ bp dp mp hodd
      have hroot : (14*2^n-2*n-16)+3+2*n+13=14*2^n := by omega
      have hmass : bp+dp+2*mp+2*n+13=14*2^n := by omega
      have hpower := (inverseAt_iff_power_mass bp dp t k c
        (by omega) hb4 hd).mp hi
      have heq := exact_endpoint_block_equation n bp dp mp t c hb4 hd hc hmass hpower.1
      have hcarry := fullCarry_append_block _ mp _ _ t ih heq
      simpa only [show c+4-1=c+3 by omega] using hcarry

/-- The exact finite certificate interface for the entire critical
    right-five gate. An empty layer plus exclusion of carry 2 at each
    earlier layer rules out every original-source history with d=5.
    Neither the depth dichotomy nor the shifted-wall test is needed. -/
theorem source_no_right_five_of_no_two (n b m z K : Nat)
    (hn : 14≤n) (hK : 0<K)
    (hempty : fullCarryStates (7*2^n-(n+3)) 0 [1] K = [])
    (hno : ∀ j<K, 2 ∉ fullCarryStates (7*2^n-(n+3)) 0 [1] j) :
    ¬ CountCone (14*2^n-2*n-16) 3 b 5 m z := by
  intro h
  have hlt := source_countcone_cost_lt_full n b 5 m z K hn h hK
    (noFullPrefix_of_emptyCarry _ _ hempty)
  have hc := source_full_carry_endpoint n b 5 m z hn h
  exact hno m hlt (by simpa using hc)

#print axioms fullCarryStates_add
#print axioms fullCarry_block
#print axioms fullCarry_append_block
#print axioms exact_endpoint_block_equation
#print axioms source_full_carry_endpoint
#print axioms source_no_right_five_of_no_two

end BB6.Agent28FullPrefix
