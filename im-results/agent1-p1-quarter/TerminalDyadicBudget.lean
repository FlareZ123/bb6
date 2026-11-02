import UniversalSmallLeft

namespace BB6.Agent1Bottleneck

/-- Exact dyadic remainder obstruction. With positive D,
D + 2^t(c+3) = 7*2^n implies 2^t ≤ 2D. -/
theorem dyadic_defect_gap (n t c D : Nat)
    (hD : D + 2^t*(c+3) = 7*2^n)
    (hDpos : 0 < D) :
    2^t ≤ 2*D := by
  have hbase : 0 < 2^n := Nat.two_pow_pos n
  by_cases htn : t ≤ n
  · have hdiv : 2^t ∣ 7*2^n := by
      have hd : 2^t ∣ 2^n := Nat.pow_dvd_pow 2 htn
      obtain ⟨z,hz⟩ := hd
      refine ⟨7*z, ?_⟩
      rw [hz]
      simp only [Nat.mul_assoc, Nat.mul_left_comm, Nat.mul_comm]
    have hs : 2^t ∣ 2^t*(c+3) := ⟨c+3,rfl⟩
    have hsub : 2^t ∣ (7*2^n-2^t*(c+3)) := Nat.dvd_sub hdiv hs
    have hsubeq : 7*2^n - 2^t*(c+3) = D := by omega
    rw [hsubeq] at hsub
    have hle := Nat.le_of_dvd hDpos hsub
    omega
  · have hgt : n+1 ≤ t := by omega
    by_cases heq : t ≤ n+1
    · have ht : t=n+1 := by omega
      subst t
      have hp : 2^(n+1) = 2*2^n := by rw [Nat.pow_succ]; omega
      have hct : c=0 := by
        by_cases hc0 : c=0
        · exact hc0
        have hcz : 1≤c := by omega
        have hmul := Nat.mul_le_mul_left (2^(n+1)) (show 4≤c+3 by omega)
        rw [hp] at hmul
        rw [hp] at hD
        omega
      subst c
      rw [hp] at hD ⊢
      omega
    · have hlarge : n+2 ≤ t := by omega
      have hp : 2^(n+2) ≤ 2^t := Nat.pow_le_pow_right (by decide : 0 < (2:Nat)) hlarge
      have hpp : 2^(n+2)=4*2^n := by
        rw [Nat.pow_add]
        have hz : (2:Nat)^2=4 := by decide
        rw [hz]
        omega
      have hmul := Nat.mul_le_mul_left (2^t) (show 3≤c+3 by omega)
      omega

/-- Under the exact two-feeder mass, every narrow-left inverse source
has a logarithmic bound on its final dyadic inverse depth. -/
theorem source_small_left_dyadic_budget
    (q u b d m t c e : Nat)
    (he : e=3 ∨ e=5)
    (hu : u+4*q+3=7*2^(16*q))
    (hmass : b+d+2*m=8*u+e)
    (hb4 : b%4=0)
    (hinverse : d+b/2+3=2^t*(c+3))
    (hsmall : b ≤ 4*m+192*q+40) :
    2^t ≤ 256*q+8*m+76 := by
  let D := 56*2^(16*q) - (d+b/2+3)
  have hscaled : 8*u+32*q+24=56*2^(16*q) := by omega
  have hsBound : d+b/2+3 < 56*2^(16*q) := by
    rcases he with he | he <;> omega
  have hdsum : D+(d+b/2+3)=56*2^(16*q) := by
    dsimp [D]
    omega
  have hDpositive : 0 < D := by
    dsimp [D]
    omega
  have hDbound : D ≤ 32*q+18+2*m+b/2 := by
    rcases he with he | he <;> omega
  have hp : 7*2^(16*q+3)=56*2^(16*q) := by
    rw [Nat.pow_add]
    have hz : (2:Nat)^3=8 := by decide
    rw [hz]
    omega
  have hg : D+2^t*(c+3)=7*2^(16*q+3) := by
    rw [hp]
    omega
  have hh:=dyadic_defect_gap (16*q+3) t c D hg hDpositive
  omega

#print axioms source_small_left_dyadic_budget

open BB6.Agent47P1
open BB6.Agent1Quarter
open BB6.Agent45TwoRoot
open BB6.Agent1ShortCone

theorem reachable_even_terminal_logdepth
    (q b d m t k c : Nat) (root : Bool)
    (hq : 1 ≤ q)
    (hcone : OddCone
      (if root then 4*u2 q-4 else 6*u2 q-2)
      (if root then 4*u2 q+9 else 2*u2 q+5) b d m)
    (hb : 8 ≤ b) (hb4 : b%4=0) (hd : d%2=1)
    (hi : inverseAt b d t = some (k,c))
    (hc : c%2=0) (hk : 2 ≤ k)
    (hr : BB6.Agent1.Reach (2*k-4) (c+4)) :
    2^t ≤ 256*q+8*m+76 := by
  let u := u2 q
  have hdom := pow16_dom q hq
  have hu : u+4*q+3=7*2^(16*q) := by dsimp [u,u2]; omega
  have hinverse := inverseAt_power b d t k c hi
  have hsmall := reachable_even_terminal_small_left q b d m t k c root hq hcone hb hb4 hd hi hc hk hr
  cases root with
  | false =>
    have hm:=odd_cone_mass (6*u-2) (2*u+5) b d m (by simpa [u] using hcone)
    have hmass:b+d+2*m=8*u+3 := by omega
    exact source_small_left_dyadic_budget q u b d m t c 3 (Or.inl rfl) hu hmass hb4 hinverse hsmall
  | true =>
    have hm:=odd_cone_mass (4*u-4) (4*u+9) b d m (by simpa [u] using hcone)
    have hmass:b+d+2*m=8*u+5 := by omega
    exact source_small_left_dyadic_budget q u b d m t c 5 (Or.inr rfl) hu hmass hb4 hinverse hsmall

#print axioms reachable_even_terminal_logdepth

#print axioms dyadic_defect_gap
end BB6.Agent1Bottleneck
