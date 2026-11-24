import WallTelescopingSource
import wall_prefix_carry_cylinders

namespace BB6.Agent9WallCarryBridge

open BB6.Agent43WallTelescoping
open BB6.Agent28 BB6.Agent1Quarter BB6.Agent1UpperTail BB6.Agent47P1
open BB6WallCarry

/-- Sum the wall weights over the *membership set* of indices below K.
    Unlike costWeightedSum, each index is counted at most once. -/
def membershipPrefixWeight (n : Nat) : Nat → List Nat → Nat
  | 0, _ => 0
  | k+1, A =>
      membershipPrefixWeight n k A +
        (if k ∈ A then (n+3+k)*2^k else 0)

/-- The positive-index part of the same membership sum, with the factor
    2 removed so that it matches sumBits. -/
def membershipTailWeight (n : Nat) : Nat → List Nat → Nat
  | 0, _ => 0
  | k+1, A =>
      membershipTailWeight n k A +
        (if k+1 ∈ A then (n+3+(k+1))*2^k else 0)

/-- The characteristic bits of A at costs 1,...,K, in increasing order. -/
def prefixBits (A : List Nat) : Nat → List Bool
  | 0 => []
  | k+1 => prefixBits A k ++ [decide ((k+1) ∈ A)]

theorem prefixBits_length (A : List Nat) :
    ∀ K, (prefixBits A K).length = K := by
  intro K
  induction K with
  | zero => simp [prefixBits]
  | succ K ih => simp [prefixBits, ih]

/-- Prepending a fresh list element changes the membership-prefix sum by
    exactly its one weight, if that index is inside the prefix. -/
theorem membershipPrefixWeight_cons (n : Nat) :
    ∀ K s (A : List Nat), s ∉ A →
      membershipPrefixWeight n K (s :: A) =
        membershipPrefixWeight n K A +
          (if s < K then (n+3+s)*2^s else 0) := by
  intro K
  induction K with
  | zero =>
      intro s A hs
      simp [membershipPrefixWeight]
  | succ K ih =>
      intro s A hs
      by_cases hEq : s = K
      · subst s
        have ih' := ih K A hs
        simp [membershipPrefixWeight, ih', hs]
      · by_cases hlt : s < K
        · have hmem : (K ∈ s :: A) ↔ K ∈ A := by simp [hEq]
          have ih' := ih s A hs
          simp [membershipPrefixWeight, ih', hlt, hmem]
        · have hgt : K < s := by omega
          have hmem : (K ∈ s :: A) ↔ K ∈ A := by simp [hgt]
          have ih' := ih s A hs
          simp [membershipPrefixWeight, ih', hgt, hmem]

/-- Duplicate-freeness is exactly what permits the list fold to be replaced
    by the membership-prefix sum modulo 2^K. Terms with s>=K vanish. -/
theorem costWeightedSum_mod_prefix (n K : Nat) :
    ∀ A : List Nat, A.Nodup →
      costWeightedSum n A % 2^K =
        membershipPrefixWeight n K A % 2^K := by
  intro A
  induction A with
  | nil =>
      intro hnd
      simp [costWeightedSum, membershipPrefixWeight]
  | cons s A ih =>
      intro hnd
      rcases List.nodup_cons.mp hnd with ⟨hnot, htail⟩
      have hih := ih htail
      rw [costWeightedSum, membershipPrefixWeight_cons n K s A hnot]
      by_cases hs : s < K
      · simp [Nat.add_mod, hih, Nat.add_comm, Nat.add_left_comm, Nat.add_assoc]
      · have hdiv : 2^K ∣ (n+3+s)*2^s := by
          refine ⟨(n+3+s)*2^(s-K), ?_⟩
          have hsplit : s = K + (s-K) := by omega
          rw [hsplit, Nat.pow_add]
          ac_rfl
        have hterm : ((n+3+s)*2^s)%2^K = 0 :=
          Nat.mod_eq_zero_of_dvd hdiv
        simp [hs, Nat.add_mod, hterm, hih]

/-- Append-one formula for the carry file's weighted Boolean fold. -/
theorem sumBits_append_single (n j : Nat) (xs : List Bool) (b : Bool) :
    sumBits n j (xs ++ [b]) =
      sumBits n j xs +
        2^xs.length * (if b then n+3+j+xs.length else 0) := by
  induction xs generalizing j with
  | nil =>
      simp [sumBits]
  | cons a xs ih =>
      simp only [List.cons_append, List.length_cons, sumBits]
      rw [ih (j+1)]
      have hidx : n+3+(j+1)+xs.length = n+3+j+(xs.length+1) := by omega
      cases a <;> cases b <;>
        simp [hidx, Nat.pow_succ, Nat.mul_add,
          Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] <;> ac_rfl

theorem sumBits_prefixBits (n : Nat) (A : List Nat) :
    ∀ K, sumBits n 1 (prefixBits A K) =
      membershipTailWeight n K A := by
  intro K
  induction K with
  | zero =>
      simp [prefixBits, sumBits, membershipTailWeight]
  | succ K ih =>
      simp only [prefixBits]
      rw [sumBits_append_single]
      rw [prefixBits_length]
      rw [ih]
      simp [membershipTailWeight, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]

theorem membershipPrefixWeight_eq_tail (n : Nat) (A : List Nat) :
    ∀ K, membershipPrefixWeight n (K+1) A =
      (if 0 ∈ A then n+3 else 0) +
        2 * membershipTailWeight n K A := by
  intro K
  induction K with
  | zero =>
      simp [membershipPrefixWeight, membershipTailWeight]
  | succ K ih =>
      simp [membershipPrefixWeight, membershipTailWeight, ih,
        Nat.pow_succ, Nat.mul_add, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]

theorem membershipPrefixWeight_eq_bitExpr
    (n K : Nat) (A : List Nat) (h0 : 0 ∈ A) :
    membershipPrefixWeight n (K+1) A =
      bitExpr n (prefixBits A K) := by
  rw [membershipPrefixWeight_eq_tail n A K]
  rw [← sumBits_prefixBits n A K]
  simp [bitExpr, h0]

theorem one_add_mod_of_dvd (K x : Nat) (hK : 1 ≤ K)
    (hdiv : 2^K ∣ x) :
    (1+x)%2^K = 1 := by
  have hpow : 1 < 2^K := by
    cases K with
    | zero => omega
    | succ K =>
        have hpos : 0 < 2^K := by
          induction K with
          | zero => simp
          | succ K ih =>
              rw [Nat.pow_succ]
              exact Nat.mul_pos ih (by decide)
        rw [Nat.pow_succ]
        omega
  have hx : x%2^K = 0 := Nat.mod_eq_zero_of_dvd hdiv
  rw [Nat.add_mod, Nat.mod_eq_of_lt hpow, hx]
  omega

/-- A genuine source CountCone history reaching the shifted wall yields a
    Boolean prefix satisfying the carry congruence whenever K<=n,m. -/
theorem sourceWall_prefix_bitExpr
    (n b d m z K : Nat)
    (hn : 14 ≤ n)
    (hsrc : CountCone (14*2^n-2*n-16) 3 b d m z)
    (hw : b+4*m+4*n+20 = 12*2^n)
    (hK : 1 ≤ K) (hKn : K ≤ n) (hKm : K ≤ m) :
    ∃ rest : List Bool,
      rest.length = K-1 ∧ bitExpr n rest % 2^K = 1 := by
  obtain ⟨A, hnd, hlt, hzero, hstart, hId⟩ :=
    source_wall_cost_list_identity n b d m z hn hsrc hw
  have hmpos : 0 < m := by omega
  have h0 : 0 ∈ A := hstart hmpos
  let rest : List Bool := prefixBits A (K-1)
  have hlen : rest.length = K-1 := by
    simp [rest, prefixBits_length]
  have hbitExact : membershipPrefixWeight n K A = bitExpr n rest := by
    have h := membershipPrefixWeight_eq_bitExpr n (K-1) A h0
    simpa [rest, Nat.sub_add_cancel hK] using h
  have hcost := costWeightedSum_mod_prefix n K A hnd
  have hdivL : 2^K ∣ 7*2^n*costPowSum A := by
    refine ⟨7*2^(n-K)*costPowSum A, ?_⟩
    have hsplit : n = K+(n-K) := by omega
    have hsub : K+(n-K)-K = n-K := by omega
    rw [hsplit, Nat.pow_add, hsub]
    ac_rfl
  have hleft := one_add_mod_of_dvd K (7*2^n*costPowSum A) hK hdivL
  have hdivN : 2^K ∣ 2^n*2^m := by
    refine ⟨2^(n-K)*2^m, ?_⟩
    have hsplit : n = K+(n-K) := by omega
    have hsub : K+(n-K)-K = n-K := by omega
    rw [hsplit, Nat.pow_add, hsub]
    ac_rfl
  have hdivM : 2^K ∣ (n+3+m)*2^m := by
    refine ⟨(n+3+m)*2^(m-K), ?_⟩
    have hsplit : m = K+(m-K) := by omega
    have hsub : K+(m-K)-K = m-K := by omega
    rw [hsplit, Nat.pow_add, hsub]
    ac_rfl
  have htermN : (2^n*2^m)%2^K = 0 := Nat.mod_eq_zero_of_dvd hdivN
  have htermM : ((n+3+m)*2^m)%2^K = 0 := Nat.mod_eq_zero_of_dvd hdivM
  have hright :
      (2^n*2^m + costWeightedSum n A + (n+3+m)*2^m)%2^K =
        costWeightedSum n A %2^K := by
    simp [Nat.add_mod, htermN, htermM]
  have hmod := congrArg (fun x => x%2^K) hId
  rw [hleft, hright] at hmod
  have hprefixmod : membershipPrefixWeight n K A %2^K = 1 := by
    calc
      membershipPrefixWeight n K A %2^K =
          costWeightedSum n A %2^K := hcost.symm
      _ = 1 := hmod.symm
  refine ⟨rest, hlen, ?_⟩
  rw [← hbitExact]
  exact hprefixmod

theorem sourceWall_noPrefix_of_carry
    (n b d m z K : Nat)
    (hn : 14 ≤ n)
    (hsrc : CountCone (14*2^n-2*n-16) 3 b d m z)
    (hw : b+4*m+4*n+20 = 12*2^n)
    (hK : 1 ≤ K) (hKn : K ≤ n) (hKm : K ≤ m)
    (hcarry : ¬ ∃ rest : List Bool,
      rest.length = K-1 ∧ bitExpr n rest % 2^K = 1) :
    False := by
  obtain ⟨rest, hlen, hbit⟩ :=
    sourceWall_prefix_bitExpr n b d m z K hn hsrc hw hK hKn hKm
  exact hcarry ⟨rest, hlen, hbit⟩

theorem sourceWall_excludes_familyI_h1
    (t b d m z u : Nat)
    (hU : 1058*u+636 = 17*2^(5362+595056*(1+2^56*t)))
    (hM : m = 14*u-2*(5362+595056*(1+2^56*t))-3)
    (hsrc : CountCone
      (14*2^(5362+595056*(1+2^56*t))-2*(5362+595056*(1+2^56*t))-16)
      3 b d m z)
    (hw : b+4*m+4*(5362+595056*(1+2^56*t))+20 =
      12*2^(5362+595056*(1+2^56*t))) : False := by
  let n := 5362+595056*(1+2^56*t)
  have hn : 14 ≤ n := by dsimp [n]; omega
  have hU' : 1058*u+636 = 17*2^n := by simpa [n] using hU
  have hM' : m = 14*u-2*n-3 := by simpa [n] using hM
  have hsrc' : CountCone (14*2^n-2*n-16) 3 b d m z := by
    simpa [n] using hsrc
  have hw' : b+4*m+4*n+20 = 12*2^n := by simpa [n] using hw
  have hmge : n ≤ m := by
    rw [hM']
    exact familyI_terminal_m_ge_n n u hn hU'
  have hKn : 60 ≤ n := by dsimp [n]; omega
  have hKm : 60 ≤ m := by omega
  have hcarry : ¬ ∃ rest : List Bool,
      rest.length = 60-1 ∧ bitExpr n rest % 2^60 = 1 := by
    simpa [n] using noPrefix_familyI_h1 t
  exact sourceWall_noPrefix_of_carry n b d m z 60 hn hsrc' hw'
    (by decide) hKn hKm hcarry

theorem sourceWall_excludes_familyI_h2
    (t b d m z u : Nat)
    (hU : 1058*u+636 = 17*2^(5362+595056*(2+2^8*t)))
    (hM : m = 14*u-2*(5362+595056*(2+2^8*t))-3)
    (hsrc : CountCone
      (14*2^(5362+595056*(2+2^8*t))-2*(5362+595056*(2+2^8*t))-16)
      3 b d m z)
    (hw : b+4*m+4*(5362+595056*(2+2^8*t))+20 =
      12*2^(5362+595056*(2+2^8*t))) : False := by
  let n := 5362+595056*(2+2^8*t)
  have hn : 14 ≤ n := by dsimp [n]; omega
  have hU' : 1058*u+636 = 17*2^n := by simpa [n] using hU
  have hM' : m = 14*u-2*n-3 := by simpa [n] using hM
  have hsrc' : CountCone (14*2^n-2*n-16) 3 b d m z := by
    simpa [n] using hsrc
  have hw' : b+4*m+4*n+20 = 12*2^n := by simpa [n] using hw
  have hmge : n ≤ m := by
    rw [hM']
    exact familyI_terminal_m_ge_n n u hn hU'
  have hKn : 12 ≤ n := by dsimp [n]; omega
  have hKm : 12 ≤ m := le_trans hKn hmge
  have hcarry : ¬ ∃ rest : List Bool,
      rest.length = 12-1 ∧ bitExpr n rest % 2^12 = 1 := by
    simpa [n] using noPrefix_familyI_h2 t
  exact sourceWall_noPrefix_of_carry n b d m z 12 hn hsrc' hw'
    (by decide) hKn hKm hcarry

theorem sourceWall_excludes_familyII_h1
    (t b d m z u : Nat)
    (hU : 1198*u+712 = 87*2^(9538+703248*(1+2^10*t)))
    (hM : m = 14*u-2*(9538+703248*(1+2^10*t))-3)
    (hsrc : CountCone
      (14*2^(9538+703248*(1+2^10*t))-2*(9538+703248*(1+2^10*t))-16)
      3 b d m z)
    (hw : b+4*m+4*(9538+703248*(1+2^10*t))+20 =
      12*2^(9538+703248*(1+2^10*t))) : False := by
  let n := 9538+703248*(1+2^10*t)
  have hn : 14 ≤ n := by dsimp [n]; omega
  have hU' : 1198*u+712 = 87*2^n := by simpa [n] using hU
  have hM' : m = 14*u-2*n-3 := by simpa [n] using hM
  have hsrc' : CountCone (14*2^n-2*n-16) 3 b d m z := by
    simpa [n] using hsrc
  have hw' : b+4*m+4*n+20 = 12*2^n := by simpa [n] using hw
  have hmge : n ≤ m := by
    rw [hM']
    exact familyII_terminal_m_ge_n n u hn hU'
  have hKn : 14 ≤ n := by dsimp [n]; omega
  have hKm : 14 ≤ m := le_trans hKn hmge
  have hcarry : ¬ ∃ rest : List Bool,
      rest.length = 14-1 ∧ bitExpr n rest % 2^14 = 1 := by
    simpa [n] using noPrefix_familyII_h1 t
  exact sourceWall_noPrefix_of_carry n b d m z 14 hn hsrc' hw'
    (by decide) hKn hKm hcarry

theorem sourceWall_excludes_familyII_h2
    (t b d m z u : Nat)
    (hU : 1198*u+712 = 87*2^(9538+703248*(2+2^18*t)))
    (hM : m = 14*u-2*(9538+703248*(2+2^18*t))-3)
    (hsrc : CountCone
      (14*2^(9538+703248*(2+2^18*t))-2*(9538+703248*(2+2^18*t))-16)
      3 b d m z)
    (hw : b+4*m+4*(9538+703248*(2+2^18*t))+20 =
      12*2^(9538+703248*(2+2^18*t))) : False := by
  let n := 9538+703248*(2+2^18*t)
  have hn : 14 ≤ n := by dsimp [n]; omega
  have hU' : 1198*u+712 = 87*2^n := by simpa [n] using hU
  have hM' : m = 14*u-2*n-3 := by simpa [n] using hM
  have hsrc' : CountCone (14*2^n-2*n-16) 3 b d m z := by
    simpa [n] using hsrc
  have hw' : b+4*m+4*n+20 = 12*2^n := by simpa [n] using hw
  have hmge : n ≤ m := by
    rw [hM']
    exact familyII_terminal_m_ge_n n u hn hU'
  have hKn : 22 ≤ n := by dsimp [n]; omega
  have hKm : 22 ≤ m := le_trans hKn hmge
  have hcarry : ¬ ∃ rest : List Bool,
      rest.length = 22-1 ∧ bitExpr n rest % 2^22 = 1 := by
    simpa [n] using noPrefix_familyII_h2 t
  exact sourceWall_noPrefix_of_carry n b d m z 22 hn hsrc' hw'
    (by decide) hKn hKm hcarry

#print axioms sourceWall_prefix_bitExpr
#print axioms sourceWall_noPrefix_of_carry
#print axioms sourceWall_excludes_familyI_h1
#print axioms sourceWall_excludes_familyI_h2
#print axioms sourceWall_excludes_familyII_h1
#print axioms sourceWall_excludes_familyII_h2

end BB6.Agent9WallCarryBridge
