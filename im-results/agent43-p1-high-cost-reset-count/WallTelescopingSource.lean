import CountedWallStrongGateSource
import ThreeResetCore

namespace BB6.Agent43WallTelescoping

open BB6.Agent28 BB6.Agent1Quarter BB6.Agent1UpperTail BB6.Agent47P1
open BB6.Agent43LastResetStrength

/-- Sum of powers over a finite list of inverse-edge costs. -/
def costPowSum : List Nat → Nat
  | [] => 0
  | s :: A => 2^s + costPowSum A

/-- Weighted sum of inverse-edge costs in the wall identity. -/
def costWeightedSum (n : Nat) : List Nat → Nat
  | [] => 0
  | s :: A => (n+3+s)*2^s + costWeightedSum n A

/-- The path-weighted source invariant.  S is the sum of 2^s over inverse-edge
    starting costs s, and U is the sum of (n+3+s)2^s over the same starts.
    The witnesses are built inductively from the actual CountCone history. -/
theorem source_weighted_sum_invariant
    (n b d m z : Nat) (hn : 14 ≤ n)
    (h : CountCone (14*2^n-2*n-16) 3 b d m z) :
    ∃ S U : Nat,
      2 + 14*2^n*S = 2^m*(d-1) + 2*U := by
  induction h with
  | root =>
      exact ⟨0, 0, by simp⟩
  | parent bp dp mp zp t k c hp hb hb4 hd hi hk hc ih =>
      obtain ⟨S, U, hInv⟩ := ih
      have hodd : OddCone (14*2^n-2*n-16) 3 bp dp mp :=
        counted_to_odd_cone _ _ _ _ _ _ hp
      have hmass0 := odd_cone_mass _ _ bp dp mp hodd
      have hroot : (14*2^n-2*n-16)+3+2*n+13 = 14*2^n := by omega
      have hmass : bp+dp+2*mp+2*n+13 = 14*2^n := by omega
      have hpower := (inverseAt_iff_power_mass bp dp t k c
        (by omega) hb4 hd).mp hi
      have hbpEven : bp = 2*(bp/2) := by omega
      have hpower2 : 2*(dp+bp/2+3) = 2^(t+1)*(c+3) := by
        calc
          2*(dp+bp/2+3) = 2*(2^t*(c+3)) := by rw [hpower.1]
          _ = 2^(t+1)*(c+3) := by
            rw [Nat.pow_succ]
            ac_rfl
      have hpowmass :
          2^(t+1)*(c+3)+2*mp+2*n+7 = dp+14*2^n := by
        calc
          _ = 2*(dp+bp/2+3)+2*mp+2*n+7 := by rw [← hpower2]
          _ = dp+(bp+dp+2*mp+2*n+13) := by omega
          _ = dp+14*2^n := by rw [hmass]
      have hdpPos : 1 ≤ dp := by omega
      have hrec :
          (dp-1)+14*2^n =
            2^(t+1)*(c+3)+2*(mp+n+3) := by omega
      have hrecMul :
          2^mp*(dp-1)+14*2^n*2^mp =
            2^(mp+t+1)*(c+3)+2*(mp+n+3)*2^mp := by
        calc
          _ = 2^mp*((dp-1)+14*2^n) := by
            rw [Nat.mul_add]
            ac_rfl
          _ = 2^mp*(2^(t+1)*(c+3)+2*(mp+n+3)) := by rw [hrec]
          _ = 2^mp*(2^(t+1)*(c+3))+2^mp*(2*(mp+n+3)) := by
            exact Nat.mul_add _ _ _
          _ = 2^(mp+t+1)*(c+3)+2*(mp+n+3)*2^mp := by
            have hpows : 2^mp * 2^(t+1) = 2^(mp+t+1) := by
              rw [← Nat.pow_add]
              rfl
            have hfirst :
                2^mp*(2^(t+1)*(c+3)) = 2^(mp+t+1)*(c+3) := by
              rw [← Nat.mul_assoc, hpows]
            have hsecond :
                2^mp*(2*(mp+n+3)) = 2*(mp+n+3)*2^mp := by ac_rfl
            rw [hfirst, hsecond]
      refine ⟨S+2^mp, U+(n+3+mp)*2^mp, ?_⟩
      calc
        2+14*2^n*(S+2^mp) =
            (2+14*2^n*S)+14*2^n*2^mp := by
          rw [Nat.mul_add]
          ac_rfl
        _ = 2^mp*(dp-1)+2*U+14*2^n*2^mp := by rw [hInv]
        _ = 2^mp*(dp-1)+14*2^n*2^mp+2*U := by ac_rfl
        _ = 2^(mp+t+1)*(c+3)+2*(mp+n+3)*2^mp+2*U := by
          rw [hrecMul]
        _ = 2^(mp+t+1)*(c+3)+2*(U+(n+3+mp)*2^mp) := by
          have hcoeff :
              2*(mp+n+3)*2^mp = 2*((n+3+mp)*2^mp) := by ac_rfl
          rw [hcoeff]
          calc
            _ = 2^(mp+t+1)*(c+3)+(2*((n+3+mp)*2^mp)+2*U) := by ac_rfl
            _ = 2^(mp+t+1)*(c+3)+2*(U+(n+3+mp)*2^mp) := by
              rw [← Nat.mul_add]
              ac_rfl
        _ = 2^(mp+t+1)*((c+4)-1)+2*(U+(n+3+mp)*2^mp) := by
          have hcd : c+3 = (c+4)-1 := by omega
          rw [hcd]

/-- Exact source-wall telescoping identity in subtraction-free Nat form.
    The first witness is the sum of 2^s over edge-start costs; the second
    includes the terminal cost m as well. -/
theorem source_wall_cost_identity
    (n b d m z : Nat) (hn : 14 ≤ n)
    (h : CountCone (14*2^n-2*n-16) 3 b d m z)
    (hw : b+4*m+4*n+20 = 12*2^n) :
    ∃ S U : Nat, 1+7*2^n*S = 2^n*2^m+U := by
  obtain ⟨S, U, hInv⟩ := source_weighted_sum_invariant n b d m z hn h
  have hodd : OddCone (14*2^n-2*n-16) 3 b d m :=
    counted_to_odd_cone _ _ _ _ _ _ h
  have hmass0 := odd_cone_mass _ _ b d m hodd
  have hroot : (14*2^n-2*n-16)+3+2*n+13 = 14*2^n := by omega
  have hmass : b+d+2*m+2*n+13 = 14*2^n := by omega
  have hdEq : d = 2*2^n+2*m+2*n+7 := by omega
  have hdMinus : d-1 = 2*2^n+2*m+2*n+6 := by omega
  have hInv' :
      2+14*2^n*S =
        2^m*(2*2^n+2*m+2*n+6)+2*U := by
    simpa [hdMinus] using hInv
  have hfactor :
      2^m*(2*2^n+2*m+2*n+6) =
        2*(2^m*(2^n+m+n+3)) := by
    have hlin : 2*2^n+2*m+2*n+6 = 2*(2^n+m+n+3) := by omega
    rw [hlin]
    ac_rfl
  have hdouble :
      2*(1+7*2^n*S) =
        2*(2^m*(2^n+m+n+3)+U) := by
    calc
      2*(1+7*2^n*S) = 2+14*2^n*S := by
        calc
          _ = 2*1+2*(7*2^n*S) := by rw [Nat.mul_add]
          _ = 2+(2*7)*2^n*S := by ac_rfl
          _ = 2+14*2^n*S := by simp
      _ = 2^m*(2*2^n+2*m+2*n+6)+2*U := hInv'
      _ = 2*(2^m*(2^n+m+n+3)+U) := by
        rw [hfactor]
        exact (Nat.mul_add 2 (2^m*(2^n+m+n+3)) U).symm
  have hfinal :
      1+7*2^n*S = 2^m*(2^n+m+n+3)+U :=
    Nat.eq_of_mul_eq_mul_left (by decide : 0 < 2) hdouble
  refine ⟨S, 2^m*(m+n+3)+U, ?_⟩
  calc
    1+7*2^n*S = 2^m*(2^n+m+n+3)+U := hfinal
    _ = 2^n*2^m+(2^m*(m+n+3)+U) := by
      have hsplit : 2^n+m+n+3 = 2^n+(m+n+3) := by omega
      rw [hsplit, Nat.mul_add]
      ac_rfl


/-- The same source induction, now exposing the actual finite set of
    cumulative edge-start costs.  This is the interface needed by the
    dyadic carry DP: no duplicate costs are possible, because every new
    start is strictly larger than every previous one. -/
theorem source_weighted_cost_list_invariant
    (n b d m z : Nat) (hn : 14 ≤ n)
    (h : CountCone (14*2^n-2*n-16) 3 b d m z) :
    ∃ A : List Nat,
      A.Nodup ∧
      (∀ s ∈ A, s < m) ∧
      (m = 0 → A = []) ∧
      (0 < m → 0 ∈ A) ∧
      2 + 14*2^n*(costPowSum A) =
        2^m*(d-1) + 2*(costWeightedSum n A) := by
  induction h with
  | root =>
      refine ⟨[], ?_, ?_, ?_, ?_, ?_⟩
      · simp
      · intro s hs
        simp at hs
      · intro hm
        rfl
      · intro hm
        omega
      · simp [costPowSum, costWeightedSum]
  | parent bp dp mp zp t k c hp hb hb4 hd hi hk hc ih =>
      obtain ⟨A, hnodup, hlt, hzero, hstart, hInv⟩ := ih
      have hodd : OddCone (14*2^n-2*n-16) 3 bp dp mp :=
        counted_to_odd_cone _ _ _ _ _ _ hp
      have hmass0 := odd_cone_mass _ _ bp dp mp hodd
      have hroot : (14*2^n-2*n-16)+3+2*n+13 = 14*2^n := by omega
      have hmass : bp+dp+2*mp+2*n+13 = 14*2^n := by omega
      have hpower := (inverseAt_iff_power_mass bp dp t k c
        (by omega) hb4 hd).mp hi
      have hbpEven : bp = 2*(bp/2) := by omega
      have hpower2 : 2*(dp+bp/2+3) = 2^(t+1)*(c+3) := by
        calc
          2*(dp+bp/2+3) = 2*(2^t*(c+3)) := by rw [hpower.1]
          _ = 2^(t+1)*(c+3) := by
            rw [Nat.pow_succ]
            ac_rfl
      have hpowmass :
          2^(t+1)*(c+3)+2*mp+2*n+7 = dp+14*2^n := by
        calc
          _ = 2*(dp+bp/2+3)+2*mp+2*n+7 := by rw [← hpower2]
          _ = dp+(bp+dp+2*mp+2*n+13) := by omega
          _ = dp+14*2^n := by rw [hmass]
      have hdpPos : 1 ≤ dp := by omega
      have hrec :
          (dp-1)+14*2^n =
            2^(t+1)*(c+3)+2*(mp+n+3) := by omega
      have hrecMul :
          2^mp*(dp-1)+14*2^n*2^mp =
            2^(mp+t+1)*(c+3)+2*(mp+n+3)*2^mp := by
        calc
          _ = 2^mp*((dp-1)+14*2^n) := by
            rw [Nat.mul_add]
            ac_rfl
          _ = 2^mp*(2^(t+1)*(c+3)+2*(mp+n+3)) := by rw [hrec]
          _ = 2^mp*(2^(t+1)*(c+3))+2^mp*(2*(mp+n+3)) := by
            exact Nat.mul_add _ _ _
          _ = 2^(mp+t+1)*(c+3)+2*(mp+n+3)*2^mp := by
            have hpows : 2^mp * 2^(t+1) = 2^(mp+t+1) := by
              rw [← Nat.pow_add]
              rfl
            have hfirst :
                2^mp*(2^(t+1)*(c+3)) = 2^(mp+t+1)*(c+3) := by
              rw [← Nat.mul_assoc, hpows]
            have hsecond :
                2^mp*(2*(mp+n+3)) = 2*(mp+n+3)*2^mp := by ac_rfl
            rw [hfirst, hsecond]
      have hnot : mp ∉ A := by
        intro hmem
        have := hlt mp hmem
        omega
      have hS : costPowSum (mp :: A) = costPowSum A + 2^mp := by
        change 2^mp + costPowSum A = costPowSum A + 2^mp
        exact Nat.add_comm _ _
      have hU :
          costWeightedSum n (mp :: A) =
            costWeightedSum n A + (n+3+mp)*2^mp := by
        change (n+3+mp)*2^mp + costWeightedSum n A =
          costWeightedSum n A + (n+3+mp)*2^mp
        exact Nat.add_comm _ _
      refine ⟨mp :: A, ?_, ?_, ?_, ?_, ?_⟩
      · exact List.nodup_cons.mpr ⟨hnot, hnodup⟩
      · intro s hs
        rcases List.mem_cons.mp hs with hsEq | hsA
        · subst s
          omega
        · exact Nat.lt_trans (hlt s hsA) (by omega)
      · intro hm
        exfalso
        omega
      · intro hm
        by_cases hmp : mp=0
        · subst mp
          simp
        · have h0 := hstart (by omega)
          simp [h0]
      · calc
          2+14*2^n*(costPowSum (mp :: A)) =
              2+14*2^n*((costPowSum A)+2^mp) := by rw [hS]
          _ = (2+14*2^n*(costPowSum A))+14*2^n*2^mp := by
            rw [Nat.mul_add]
            ac_rfl
          _ = 2^mp*(dp-1)+2*(costWeightedSum n A)+14*2^n*2^mp := by
            rw [hInv]
          _ = 2^mp*(dp-1)+14*2^n*2^mp+
                2*(costWeightedSum n A) := by ac_rfl
          _ = 2^(mp+t+1)*(c+3)+2*(mp+n+3)*2^mp+
                2*(costWeightedSum n A) := by
            rw [hrecMul]
          _ = 2^(mp+t+1)*(c+3)+
                2*(costWeightedSum n A)+2*((n+3+mp)*2^mp) := by
            have hcoeff : 2*(mp+n+3)*2^mp =
                2*((n+3+mp)*2^mp) := by
              have hlin : mp+n+3 = n+3+mp := by omega
              rw [hlin, Nat.mul_assoc]
            rw [hcoeff]
            ac_rfl
          _ = 2^(mp+t+1)*(c+3)+
                2*((costWeightedSum n A)+(n+3+mp)*2^mp) := by
            have hdist :
                2*((costWeightedSum n A)+(n+3+mp)*2^mp) =
                  2*(costWeightedSum n A)+2*((n+3+mp)*2^mp) := by
              ring
            calc
              _ = 2^(mp+t+1)*(c+3)+
                    (2*(costWeightedSum n A)+2*((n+3+mp)*2^mp)) := by ac_rfl
              _ = 2^(mp+t+1)*(c+3)+
                    2*((costWeightedSum n A)+(n+3+mp)*2^mp) := by
                exact congrArg
                  (fun x => 2^(mp+t+1)*(c+3)+x) hdist.symm
          _ = 2^(mp+t+1)*((c+4)-1)+
                2*(costWeightedSum n (mp :: A)) := by
            rw [hU]
            have hcd : c+3 = (c+4)-1 := by omega
            rw [hcd]

/-- Source-certified finite-set form of the wall identity.  The set A contains
    every inverse-edge starting cost; the terminal cost m is the additional
    final element in the complete wall subset. -/
theorem source_wall_cost_list_identity
    (n b d m z : Nat) (hn : 14 ≤ n)
    (h : CountCone (14*2^n-2*n-16) 3 b d m z)
    (hw : b+4*m+4*n+20 = 12*2^n) :
    ∃ A : List Nat,
      A.Nodup ∧
      (∀ s ∈ A, s < m) ∧
      (m = 0 → A = []) ∧
      (0 < m → 0 ∈ A) ∧
      1+7*2^n*(costPowSum A) =
        2^n*2^m + (costWeightedSum n A) + (n+3+m)*2^m := by
  obtain ⟨A, hnodup, hlt, hzero, hstart, hInv⟩ :=
    source_weighted_cost_list_invariant n b d m z hn h
  let S : Nat := costPowSum A
  let U : Nat := costWeightedSum n A
  have hodd : OddCone (14*2^n-2*n-16) 3 b d m :=
    counted_to_odd_cone _ _ _ _ _ _ h
  have hmass0 := odd_cone_mass _ _ b d m hodd
  have hroot : (14*2^n-2*n-16)+3+2*n+13 = 14*2^n := by omega
  have hmass : b+d+2*m+2*n+13 = 14*2^n := by omega
  have hdEq : d = 2*2^n+2*m+2*n+7 := by omega
  have hdMinus : d-1 = 2*2^n+2*m+2*n+6 := by omega
  have hInv' :
      2+14*2^n*S =
        2^m*(2*2^n+2*m+2*n+6)+2*U := by
    simpa [S, U, hdMinus] using hInv
  have hfactor :
      2^m*(2*2^n+2*m+2*n+6) =
        2*(2^m*(2^n+m+n+3)) := by
    have hlin : 2*2^n+2*m+2*n+6 = 2*(2^n+m+n+3) := by omega
    rw [hlin]
    ac_rfl
  have hdouble :
      2*(1+7*2^n*S) =
        2*(2^m*(2^n+m+n+3)+U) := by
    calc
      2*(1+7*2^n*S) = 2+14*2^n*S := by
        calc
          _ = 2*1+2*(7*2^n*S) := by rw [Nat.mul_add]
          _ = 2+(2*7)*2^n*S := by ac_rfl
          _ = 2+14*2^n*S := by simp
      _ = 2^m*(2*2^n+2*m+2*n+6)+2*U := hInv'
      _ = 2*(2^m*(2^n+m+n+3)+U) := by
        rw [hfactor]
        exact (Nat.mul_add 2 (2^m*(2^n+m+n+3)) U).symm
  have hfinal :
      1+7*2^n*S = 2^m*(2^n+m+n+3)+U :=
    Nat.eq_of_mul_eq_mul_left (by decide : 0 < 2) hdouble
  refine ⟨A, hnodup, hlt, hzero, hstart, ?_⟩
  calc
    1+7*2^n*S = 2^m*(2^n+m+n+3)+U := hfinal
    _ = 2^n*2^m+U+(n+3+m)*2^m := by
      have hsplit : 2^n+m+n+3 = 2^n+(m+n+3) := by omega
      have hterm : 2^m*(m+n+3) = (n+3+m)*2^m := by
        have hlin : m+n+3 = n+3+m := by omega
        rw [hlin]
        ac_rfl
      rw [hsplit, Nat.mul_add, hterm]
      ac_rfl


private theorem pow_two_mod2 (k : Nat) (hk : 0 < k) : 2^k % 2 = 0 := by
  cases k with
  | zero => omega
  | succ k =>
    rw [Nat.pow_succ]
    have hdiv : 2 ∣ 2^k * 2 := by
      refine ⟨2^k, ?_⟩
      ac_rfl
    exact Nat.mod_eq_zero_of_dvd hdiv

private theorem pow_two_mod16 (k : Nat) (hk : 4 ≤ k) : 2^k % 16 = 0 := by
  cases k with
  | zero => omega
  | succ k =>
    cases k with
    | zero => omega
    | succ k =>
      cases k with
      | zero => omega
      | succ k =>
        cases k with
        | zero => omega
        | succ k =>
          rw [Nat.pow_succ, Nat.pow_succ, Nat.pow_succ, Nat.pow_succ]
          omega

private theorem terminalTerm_mod16 (n m : Nat) (hnEven : n%2=0)
    (hm3 : 3≤m) : (n+3+m)*2^m % 16 = 0 := by
  by_cases hm4 : 4≤m
  · have hpow := pow_two_mod16 m hm4
    rw [Nat.mul_mod, hpow]
    simp
  · have hmEq : m=3 := by omega
    subst m
    have hEven : (n+6)%2=0 := by omega
    omega

private theorem costPowSum_ge_one_of_zero_mem (A : List Nat) (h0 : 0 ∈ A) :
    1 ≤ costPowSum A := by
  induction A with
  | nil => simp at h0
  | cons s A ih =>
    simp only [costPowSum]
    rcases List.mem_cons.mp h0 with hs | htail
    · subst s
      simp
    · have htail' := ih htail
      exact Nat.le_trans htail' (Nat.le_add_left (costPowSum A) (2^s))

private theorem costWeightedSum_le_two (n : Nat) :
    ∀ A : List Nat, A.Nodup →
      (∀ s ∈ A, s < 2) →
      costWeightedSum n A ≤ 3*n+11 := by
  intro A
  induction A with
  | nil =>
      intro hnd hlt
      simp [costWeightedSum]
  | cons s A ih =>
      intro hnd hlt
      have hnd' := List.nodup_cons.mp hnd
      have hslt : s < 2 := hlt s (by simp)
      have htailLt : ∀ t ∈ A, t < 2 := by
        intro t ht
        exact hlt t (by simp [ht])
      by_cases hs0 : s = 0
      · subst s
        have hnot0 : 0 ∉ A := hnd'.1
        have htail1 : ∀ t ∈ A, t = 1 := by
          intro t ht
          have htlt := htailLt t ht
          have htne : t ≠ 0 := by
            intro hEq
            subst t
            exact hnot0 ht
          omega
        cases A with
        | nil =>
            simp [costWeightedSum]
            omega
        | cons t T =>
            have ht1 := htail1 t (by simp)
            subst t
            have hnot1 : 1 ∉ T := (List.nodup_cons.mp hnd'.2).1
            have hTnil : T = [] := by
              cases T with
              | nil => rfl
              | cons u U =>
                  have hu1 := htail1 u (by simp)
                  subst u
                  exact False.elim (hnot1 (by simp))
            simp [costWeightedSum, hTnil]
            omega
      · have hs1 : s = 1 := by omega
        subst s
        have hnot1 : 1 ∉ A := hnd'.1
        have htail0 : ∀ t ∈ A, t = 0 := by
          intro t ht
          have htlt := htailLt t ht
          have htne : t ≠ 1 := by
            intro hEq
            subst t
            exact hnot1 ht
          omega
        cases A with
        | nil =>
            simp [costWeightedSum]
            omega
        | cons t T =>
            have ht0 := htail0 t (by simp)
            subst t
            have hnot0 : 0 ∉ T := (List.nodup_cons.mp hnd'.2).1
            have hTnil : T = [] := by
              cases T with
              | nil => rfl
              | cons u U =>
                  have hu0 := htail0 u (by simp)
                  subst u
                  exact False.elim (hnot0 (by simp))
            simp [costWeightedSum, hTnil]
            omega

private theorem costWeightedSum_mod2_pos (n : Nat) :
    ∀ A : List Nat, (∀ s ∈ A, 0 < s) →
      costWeightedSum n A % 2 = 0 := by
  intro A
  induction A with
  | nil =>
      intro hpos
      simp [costWeightedSum]
  | cons s A ih =>
      intro hpos
      have hs : 0 < s := hpos s (by simp)
      have htail : ∀ t ∈ A, 0 < t := by
        intro t ht
        exact hpos t (by simp [ht])
      have hpow : 2^s % 2 = 0 := by
        cases s with
        | zero => omega
        | succ s =>
          rw [Nat.pow_succ]
          omega
      have hterm : ((n+3+s)*2^s) % 2 = 0 := by
        rw [Nat.mul_mod, hpow]
        simp
      have hA := ih htail
      simp [costWeightedSum, Nat.add_mod, hterm, hA]

private theorem costWeightedSum_mod2_zero_mem (n : Nat) :
    ∀ A : List Nat, A.Nodup → 0 ∈ A →
      costWeightedSum n A % 2 = (n+3)%2 := by
  intro A
  induction A with
  | nil =>
      intro hnd h0
      simp at h0
  | cons s A ih =>
      intro hnd h0
      have hnd' := List.nodup_cons.mp hnd
      by_cases hs : s = 0
      · subst s
        have hpos : ∀ t ∈ A, 0 < t := by
          intro t ht
          have hne : t ≠ 0 := by
            intro hEq
            subst t
            exact hnd'.1 ht
          omega
        have htail := costWeightedSum_mod2_pos n A hpos
        simp [costWeightedSum, Nat.add_mod, htail]
      · have h0s : 0 ≠ s := by omega
        have h0A : 0 ∈ A := by simpa [h0s] using h0
        have htail := ih hnd'.2 h0A
        have hpow : 2^s % 2 = 0 := by
          cases s with
          | zero => omega
          | succ s =>
            rw [Nat.pow_succ]
            omega
        have hterm : ((n+3+s)*2^s) % 2 = 0 := by
          rw [Nat.mul_mod, hpow]
          simp
        simp [costWeightedSum, Nat.add_mod, hterm, htail]

private theorem costWeightedSum_mod16_zero_mem (n : Nat) (hnEven : n%2=0) :
    ∀ A : List Nat, A.Nodup →
      costWeightedSum n A % 16 =
        ((if 0 ∈ A then n+3 else 0) +
         (if 1 ∈ A then 2*(n+4) else 0) +
         (if 2 ∈ A then 4*(n+5) else 0)) % 16 := by
  intro A
  induction A with
  | nil =>
      intro hnd
      simp [costWeightedSum]
  | cons s A ih =>
      intro hnd
      have hnd' := List.nodup_cons.mp hnd
      have htail := ih hnd'.2
      by_cases hs0 : s=0
      · subst s
        have hnot0 : 0 ∉ A := hnd'.1
        simp [costWeightedSum, hnot0, htail, Nat.add_mod] <;> omega
      · by_cases hs1 : s=1
        · subst s
          have hnot1 : 1 ∉ A := hnd'.1
          simp [costWeightedSum, hnot1, htail, Nat.add_mod] <;> omega
        · by_cases hs2 : s=2
          · subst s
            have hnot2 : 2 ∉ A := hnd'.1
            simp [costWeightedSum, hnot2, htail, Nat.add_mod] <;> omega
          · have hterm : ((n+3+s)*2^s)%16=0 := by
              by_cases hs3 : s=3
              · subst s
                have hEven : (n+6)%2=0 := by omega
                omega
              · have hs4 : 4≤s := by omega
                have hpow := pow_two_mod16 s hs4
                rw [Nat.mul_mod, hpow]
                simp
            have h0s : 0 ≠ s := by omega
            have h1s : 1 ≠ s := by omega
            have h2s : 2 ≠ s := by omega
            simp [costWeightedSum, Nat.add_mod, hterm, h0s, h1s, h2s, htail] <;> omega

/-- On the exact shifted source wall, at least three reset-cost units are
forced. The proof uses the duplicate-free cost list and its first two
possible entries. -/
theorem source_wall_forces_m_ge_three
    (n b d m z : Nat) (hn : 14 ≤ n)
    (h : CountCone (14*2^n-2*n-16) 3 b d m z)
    (hw : b+4*m+4*n+20=12*2^n) : 3 ≤ m := by
  obtain ⟨A, hnd, hlt, hzero, hstart, hId⟩ :=
    source_wall_cost_list_identity n b d m z hn h hw
  by_cases hm3 : 3≤m
  · exact hm3
  · have hmCases : m=0 ∨ m=1 ∨ m=2 := by omega
    rcases hmCases with hm0 | hm1 | hm2
    · have hA : A=[] := hzero hm0
      rw [hm0, hA] at hId
      simp [costPowSum, costWeightedSum] at hId
      omega
    · subst m
      have h0 := hstart (by omega)
      have hS := costPowSum_ge_one_of_zero_mem A h0
      have hU := costWeightedSum_le_two n A hnd (by
        intro s hs
        have hslt := hlt s hs
        omega)
      have hP1100 : 1100*n ≤ 2^n :=
        (BB6.ThreeResetCore.three_reset_numeric_bounds n (2^n) hn rfl).1
      have hL : 1+7*2^n ≤ 1+7*2^n*costPowSum A := by
        have hmul := Nat.mul_le_mul_left (7*2^n) hS
        omega
      have hR : 2^n*2 + costWeightedSum n A + (n+4)*2 ≤ 2*2^n+5*n+19 := by omega
      omega
    · subst m
      have h0 := hstart (by omega)
      have hS := costPowSum_ge_one_of_zero_mem A h0
      have hU := costWeightedSum_le_two n A hnd (by
        intro s hs
        have hslt := hlt s hs
        omega)
      have hP1100 : 1100*n ≤ 2^n :=
        (BB6.ThreeResetCore.three_reset_numeric_bounds n (2^n) hn rfl).1
      have hL : 1+7*2^n ≤ 1+7*2^n*costPowSum A := by
        have hmul := Nat.mul_le_mul_left (7*2^n) hS
        omega
      have hR : 2^n*4 + costWeightedSum n A + (n+5)*4 ≤ 4*2^n+7*n+31 := by omega
      omega

/-- Every source CountCone prefix on the exact shifted 12*2^n wall has
n congruent to 2 or 14 modulo 16. The first two positive reset-cost entries
must have opposite membership in the former case and equal membership in
the latter. -/
theorem source_wall_forces_n_mod16
    (n b d m z : Nat) (hn : 14 ≤ n)
    (h : CountCone (14*2^n-2*n-16) 3 b d m z)
    (hw : b+4*m+4*n+20=12*2^n) :
    ∃ A : List Nat,
      A.Nodup ∧ (∀ s∈A, s<m) ∧ 0∈A ∧
      (n%16=2 ∧ ((1∈A ∧ 2∉A) ∨ (1∉A ∧ 2∈A)) ∨
       n%16=14 ∧ ((1∈A ∧ 2∈A) ∨ (1∉A ∧ 2∉A))) := by
  obtain ⟨A, hnd, hlt, hzero, hstart, hId⟩ :=
    source_wall_cost_list_identity n b d m z hn h hw
  have hm3 := source_wall_forces_m_ge_three n b d m z hn h hw
  have h0 : 0∈A := hstart (by omega)
  have hnEven : n%2=0 := by
    have hU := costWeightedSum_mod2_zero_mem n A hnd h0
    have hpowN := pow_two_mod2 n (by omega)
    have hpowM := pow_two_mod2 m (by omega)
    have hleft : (1+7*2^n*costPowSum A)%2=1 := by
      simp [Nat.add_mod, Nat.mul_mod, hpowN]
    have hright :
        (2^n*2^m+costWeightedSum n A+(n+3+m)*2^m)%2 =
          costWeightedSum n A%2 := by
      simp [Nat.add_mod, Nat.mul_mod, hpowN, hpowM]
    have hmod := congrArg (fun x => x%2) hId
    rw [hleft, hright, hU] at hmod
    omega
  have hU16 := costWeightedSum_mod16_zero_mem n hnEven A hnd
  have hpowN16 := pow_two_mod16 n (by omega)
  have htermM16 := terminalTerm_mod16 n m hnEven hm3
  have hleft16 : (1+7*2^n*costPowSum A)%16=1 := by
    simp [Nat.add_mod, Nat.mul_mod, hpowN16]
  have hright16 :
      (2^n*2^m+costWeightedSum n A+(n+3+m)*2^m)%16 =
        costWeightedSum n A%16 := by
    simp [Nat.add_mod, Nat.mul_mod, hpowN16, htermM16]
  have hmod16 := congrArg (fun x => x%16) hId
  rw [hleft16, hright16, hU16] at hmod16
  by_cases h1 : 1∈A <;> by_cases h2 : 2∈A
  · have hcase := hmod16
    simp [h0, h1, h2] at hcase
    have hn14 : n%16=14 := by omega
    exact ⟨A,hnd,hlt,h0, Or.inr ⟨hn14, Or.inl ⟨h1,h2⟩⟩⟩
  · have hcase := hmod16
    simp [h0, h1, h2] at hcase
    have hn2 : n%16=2 := by omega
    exact ⟨A,hnd,hlt,h0, Or.inl ⟨hn2, Or.inl ⟨h1,h2⟩⟩⟩
  · have hcase := hmod16
    simp [h0, h1, h2] at hcase
    have hn2 : n%16=2 := by omega
    exact ⟨A,hnd,hlt,h0, Or.inl ⟨hn2, Or.inr ⟨h1,h2⟩⟩⟩
  · have hcase := hmod16
    simp [h0, h1, h2] at hcase
    have hn14 : n%16=14 := by omega
    exact ⟨A,hnd,hlt,h0, Or.inr ⟨hn14, Or.inr ⟨h1,h2⟩⟩⟩

#print axioms BB6.Agent43WallTelescoping.source_wall_forces_m_ge_three
#print axioms BB6.Agent43WallTelescoping.source_wall_forces_n_mod16

#print axioms BB6.Agent43WallTelescoping.source_weighted_sum_invariant
#print axioms BB6.Agent43WallTelescoping.source_wall_cost_identity
#print axioms BB6.Agent43WallTelescoping.source_weighted_cost_list_invariant
#print axioms BB6.Agent43WallTelescoping.source_wall_cost_list_identity

end BB6.Agent43WallTelescoping
