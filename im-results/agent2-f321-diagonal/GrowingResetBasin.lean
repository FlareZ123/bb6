import BasinSource

namespace BB6.Agent2F321GrowingBasin
open BB6.Agent2F321Basin
open BB6.Agent2F321BasinDensity
open BB6.Agent2F321BasinSource

/-- The reset budget is monotone, without assuming eventual reset existence. -/
theorem basin_succ {j R c} (hb : Basin j R c) : Basin (j+1) R c := by
  rcases basin_counted hb with ⟨i,hi,n,t,hr⟩
  exact counted_basin (basin_small hb) (by omega) hr

theorem basin_mono {j s R c} (hjs : j≤s) (hb : Basin j R c) : Basin s R c := by
  rcases basin_counted hb with ⟨i,hi,n,t,hr⟩
  exact counted_basin (basin_small hb) (by omega) hr

private theorem pow_two_lower (n : Nat) : n+1≤2^n := by
  induction n with
  | zero => decide
  | succ n ih => rw [Nat.pow_succ]; omega

/-- The exponent cost from all prefactors is eventually smaller than
    half the saved exponential gap. -/
theorem poly_exponent_le (s : Nat) (hs : 6≤s) :
    16+12*s+(4*s+5)*s≤2^(2*s-3) := by
  induction s with
  | zero => omega
  | succ s ih =>
      by_cases hs' : 6≤s
      · have ih := ih hs'
        have he : 2*(s+1)-3=(2*s-3)+2 := by omega
        rw [he,Nat.pow_add]
        change 16+12*(s+1)+(4*(s+1)+5)*(s+1)≤2^(2*s-3)*4
        have hsq : 4*(s+1)+5=4*s+5+4 := by omega
        rw [hsq,Nat.add_mul,Nat.mul_add (4*s+5),Nat.mul_add 4]
        omega
      · have he : s=5 := by omega
        subst s
        decide

/-- A uniform count for logarithmically growing reset budgets. If the
    counter bit-scale k lies in [2^(4s),2^(4(s+1))), at most s resets
    are allowed. The fraction of possible halting anchors is bounded
    by 2^(-2^(2s-3)), which tends to zero with k. -/
theorem growing_basin_count (s k : Nat) (hs : 6≤s)
    (hlo : 2^(4*s)≤k) (hhi : k<2^(4*(s+1)))
    (xs : List (Nat×Nat)) (hnd : xs.Nodup)
    (hall : ∀ p∈xs, p.1≤2^k ∧ Basin s p.1 p.2) :
    xs.length≤2^(k-2^(2*s-3)) := by
  have hs0 : 2≤4*s := by omega
  have hk : 2≤k := by have h := Nat.pow_le_pow_right (n:=2) (by decide) hs0; omega
  have hcount := basin_count_dyadic s k hk xs hnd hall
  have hpow : 4*s+1≤2^(4*s) := pow_two_lower _
  have hbase : k+4*s+1≤2^(4*s+5) := by
    rw [show 4*s+5=4*(s+1)+1 by omega,Nat.pow_succ]
    have hsmall : 2^(4*s)≤2^(4*(s+1)) := Nat.pow_le_pow_right (by decide) (by omega)
    omega
  have hpoly : scalePoly s k≤2^((4*s+5)*s) := by
    unfold scalePoly
    have h := Nat.pow_le_pow_left hbase s
    rw [←Nat.pow_mul] at h
    exact h
  have hCpoly := Nat.mul_le_mul_left (C s) hpoly
  unfold C at hCpoly
  rw [←Nat.pow_add] at hCpoly
  have hpref := Nat.le_trans hCpoly (Nat.pow_le_pow_right (by decide) (poly_exponent_le s hs))
  have hdiv : 2^(2*s-2)≤gap s k := by
    unfold gap
    apply (Nat.le_div_iff_mul_le (Nat.pow_pos (by decide : 0<4))).mpr
    rw [show (4:Nat)=2^2 by decide,←Nat.pow_mul,←Nat.pow_add]
    have he : (2*s-2)+2*(s+1)=4*s := by omega
    rwa [he]
  have hgapk : gap s k≤k := Nat.div_le_self _ _
  have hgapHalf : 2^(2*s-2)=2*2^(2*s-3) := by
    rw [show 2*s-2=(2*s-3)+1 by omega,Nat.pow_succ,Nat.mul_comm]
  have hexp : 2^(2*s-3)+(k-gap s k)≤k-2^(2*s-3) := by omega
  have hmul := Nat.mul_le_mul_right (2^(k-gap s k)) hpref
  rw [←Nat.pow_add] at hmul
  exact Nat.le_trans hcount (Nat.le_trans hmul (Nat.pow_le_pow_right (by decide) hexp))

/-- Source-level version permits any number of completed resets at most s. -/
theorem growing_source_count (s k : Nat) (hs : 6≤s)
    (hlo : 2^(4*s)≤k) (hhi : k<2^(4*(s+1)))
    (xs : List (Nat×Nat)) (hnd : xs.Nodup)
    (hall : ∀ p∈xs, p.1≤2^k ∧ (p.2=1∨p.2=2) ∧
      ∃ i≤s, ∃ n t, CountedRun i n p.1 p.2 (t+1) t) :
    xs.length≤2^(k-2^(2*s-3)) := by
  apply growing_basin_count s k hs hlo hhi xs hnd
  intro p hp
  rcases hall p hp with ⟨hR,hc,i,hi,n,t,hr⟩
  exact ⟨hR,counted_basin hc hi hr⟩

#print axioms growing_basin_count
#print axioms growing_source_count
end BB6.Agent2F321GrowingBasin
