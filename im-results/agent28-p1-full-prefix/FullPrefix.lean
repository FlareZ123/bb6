import WallListSource

/-!
# Endpoint-independent full-P 2-adic prefix obstruction for P1 CountCone histories

The source CostWitness identity implies a Boolean prefix condition at every
modulus 2^K with K no larger than the history cost m. Unlike the simpler
(n+3+s)-prefix, this full-P version has no K <= n restriction.
-/

namespace BB6.Agent28FullPrefix

open BB6.Agent28
open BB6.Agent1Quarter
open BB6.Agent1UpperTail
open BB6.Agent47P1
open BB6.Agent43WallListCore
open BB6.Agent43WallListSource
open BB6.Agent43LastResetStrength

def fullWeight (Q s : Nat) : Nat := (Q-s)*2^s

def fullWeightedSum (Q : Nat) : List Nat → Nat
  | [] => 0
  | s :: A => fullWeight Q s + fullWeightedSum Q A

def fullSumBits (Q j : Nat) : List Bool → Nat
  | [] => 0
  | bit :: bits =>
      (if bit then Q-j else 0) + 2*fullSumBits Q (j+1) bits

def fullPrefixSum (Q j : Nat) (A : List Nat) : Nat → Nat
  | 0 => 0
  | k+1 =>
      (if j ∈ A then fullWeight Q j else 0) +
        fullPrefixSum Q (j+1) A k

theorem fullPrefixSum_cons (Q j k a : Nat) (A : List Nat)
    (ha : a ∉ A) :
    fullPrefixSum Q j (a::A) k =
      fullPrefixSum Q j A k +
        (if j ≤ a ∧ a < j+k then fullWeight Q a else 0) := by
  induction k generalizing j with
  | zero =>
      have hh : ¬ (j ≤ a ∧ a < j+0) := by omega
      rw [if_neg hh]
      simp [fullPrefixSum]
  | succ k ih =>
      rw [fullPrefixSum, fullPrefixSum, ih (j+1)]
      by_cases h : j = a
      · subst j
        have hn : ¬ a+1 ≤ a := by omega
        simp [ha, hn, Nat.add_comm]
      · have he : (j ≤ a ∧ a < j+(k+1)) ↔
            (j+1 ≤ a ∧ a < j+1+k) := by omega
        simp [List.mem_cons, h, he, Nat.add_assoc]

theorem fullPrefixSum_nil (Q j k : Nat) :
    fullPrefixSum Q j [] k = 0 := by
  induction k generalizing j with
  | zero => rfl
  | succ k ih => simp [fullPrefixSum, ih]

theorem fullPrefix_bits (Q j k : Nat) (A : List Nat) :
    fullPrefixSum Q j A k =
      2^j * fullSumBits Q j (BB6WallBridge.bits A j k) := by
  induction k generalizing j with
  | zero => simp [fullPrefixSum, fullSumBits, BB6WallBridge.bits]
  | succ k ih =>
      rw [fullPrefixSum, BB6WallBridge.bits, fullSumBits.eq_def,
        ih (j+1), Nat.mul_add, Nat.pow_succ]
      by_cases h : j ∈ A <;>
        simp [h, fullWeight] <;> ac_rfl

theorem fullWeighted_mod_prefix (Q K : Nat) (A : List Nat)
    (hnd : A.Nodup) :
    fullWeightedSum Q A % 2^K =
      fullPrefixSum Q 0 A K % 2^K := by
  induction A with
  | nil => simp [fullWeightedSum, fullPrefixSum_nil]
  | cons a A ih =>
      obtain ⟨ha, hn⟩ := List.nodup_cons.mp hnd
      rw [fullWeightedSum,
        fullPrefixSum_cons Q 0 K a A ha]
      by_cases h : a < K
      · simp only [if_pos (by omega : 0 ≤ a ∧ a < 0+K)]
        rw [Nat.add_mod, ih hn]
        simp [Nat.add_mod, Nat.add_comm]
      · have hpow : 2^K ∣ 2^a := by
          refine ⟨2^(a-K), ?_⟩
          rw [← Nat.pow_add, Nat.add_sub_of_le (by omega)]
        have hz : fullWeight Q a % 2^K = 0 := by
          apply Nat.mod_eq_zero_of_dvd
          obtain ⟨r, hr⟩ := hpow
          refine ⟨(Q-a)*r, ?_⟩
          rw [fullWeight, hr]
          ac_rfl
        have hcond : (if 0 ≤ a ∧ a < 0+K then fullWeight Q a else 0)=0 := by
          simp [h]
        rw [hcond, Nat.add_mod, hz, ih hn]
        simp

theorem fullWeighted_mod_bits (Q K : Nat) (A : List Nat)
    (hnd : A.Nodup) :
    ∃ xs : List Bool, xs.length = K ∧
      fullWeightedSum Q A % 2^K =
        fullSumBits Q 0 xs % 2^K := by
  refine ⟨BB6WallBridge.bits A 0 K,
    BB6WallBridge.bits_length A 0 K, ?_⟩
  rw [fullWeighted_mod_prefix Q K A hnd, fullPrefix_bits]
  simp

theorem fullSum_add_weighted (n Q : Nat) (A : List Nat)
    (hnp : n+3 ≤ 7*2^n)
    (hQ : Q = 7*2^n-(n+3))
    (hs : ∀ s ∈ A, s ≤ Q) :
    fullWeightedSum Q A + costWeightedSum n A =
      7*2^n*costPowSum A := by
  induction A with
  | nil => simp [fullWeightedSum, costWeightedSum, costPowSum]
  | cons s A ih =>
      have hs0 : s ≤ Q := hs s (by simp)
      have hstail : ∀ t ∈ A, t ≤ Q := by
        intro t ht
        exact hs t (by simp [ht])
      have hcoeff : (Q-s)+(n+3+s)=7*2^n := by
        rw [hQ]
        omega
      have hterm :
          (Q-s)*2^s + (n+3+s)*2^s = 7*2^n*2^s := by
        rw [← Nat.add_mul, hcoeff]
      change (Q-s)*2^s + fullWeightedSum Q A +
          ((n+3+s)*2^s + costWeightedSum n A) =
          7*2^n*(2^s+costPowSum A)
      calc
        _ = ((Q-s)*2^s+(n+3+s)*2^s) +
              (fullWeightedSum Q A+costWeightedSum n A) := by ac_rfl
        _ = 7*2^n*2^s + 7*2^n*costPowSum A := by
              rw [hterm, ih hstail]
        _ = 7*2^n*(2^s+costPowSum A) := by
              rw [Nat.mul_add]

def fullCarryStep (Q j : Nat) (cs : List Nat) : List Nat :=
  cs.flatMap fun c =>
    (if c % 2 = 0 then [c/2] else []) ++
    (if (c+(Q-j)) % 2 = 0 then [(c+(Q-j))/2] else [])

def fullCarryStates (Q j : Nat) (cs : List Nat) : Nat → List Nat
  | 0 => cs
  | k+1 => fullCarryStates Q (j+1) (fullCarryStep Q j cs) k

inductive FullCarryPath (Q : Nat) : Nat → List Bool → Nat → Nat → Prop
  | nil (j c : Nat) : FullCarryPath Q j [] c c
  | cons (j c c' q : Nat) (bit : Bool) (bits : List Bool)
      (hstep : c + (if bit then Q-j else 0) = 2*c')
      (htail : FullCarryPath Q (j+1) bits c' q) :
      FullCarryPath Q j (bit::bits) c q

theorem fullCarryPath_of_sum (Q : Nat) :
    ∀ (xs : List Bool) (j c q : Nat),
      c + fullSumBits Q j xs = 2^xs.length*q →
        FullCarryPath Q j xs c q := by
  intro xs
  induction xs with
  | nil =>
      intro j c q h
      simp [fullSumBits] at h
      subst q
      exact FullCarryPath.nil j c
  | cons bit bits ih =>
      intro j c q h
      let t := if bit then Q-j else 0
      have hEq : c+t+2*fullSumBits Q (j+1) bits =
          2*(2^bits.length*q) := by
        calc
          c+t+2*fullSumBits Q (j+1) bits =
              c + fullSumBits Q j (bit::bits) := by
                simp [fullSumBits, t]
                omega
          _ = 2^((bit::bits).length)*q := h
          _ = 2*(2^bits.length*q) := by
                simp [Nat.pow_succ]
                ac_rfl
      have hEven : (c+t)%2=0 := by omega
      have hStep : c+t=2*((c+t)/2) := by omega
      have hTail : (c+t)/2+fullSumBits Q (j+1) bits =
          2^bits.length*q := by omega
      refine FullCarryPath.cons j c ((c+t)/2) q bit bits ?_ ?_
      · simpa [t] using hStep
      · exact ih (j+1) ((c+t)/2) q hTail

theorem fullCarryStep_mono (Q j : Nat) {cs1 cs2 : List Nat}
    (hsub : ∀ x, x ∈ cs1 → x ∈ cs2) :
    ∀ y, y ∈ fullCarryStep Q j cs1 → y ∈ fullCarryStep Q j cs2 := by
  intro y hy
  simp only [fullCarryStep, List.mem_flatMap] at hy ⊢
  rcases hy with ⟨c, hc, hopt⟩
  exact ⟨c, hsub c hc, hopt⟩

theorem fullCarryStates_mono (Q j : Nat) (cs1 cs2 : List Nat)
    (hsub : ∀ x, x ∈ cs1 → x ∈ cs2) :
    ∀ k y, y ∈ fullCarryStates Q j cs1 k →
      y ∈ fullCarryStates Q j cs2 k := by
  intro k
  induction k generalizing j cs1 cs2 with
  | zero =>
      intro y hy
      simpa [fullCarryStates] using hsub y hy
  | succ k ih =>
      intro y hy
      apply ih (j+1) (fullCarryStep Q j cs1) (fullCarryStep Q j cs2)
        (fullCarryStep_mono Q j hsub) y
      simpa [fullCarryStates] using hy

theorem FullCarryPath.mem_fullCarryStates {Q j : Nat} {xs : List Bool}
    {c q : Nat} (h : FullCarryPath Q j xs c q) :
    q ∈ fullCarryStates Q j [c] xs.length := by
  induction h with
  | nil j c =>
      simp [fullCarryStates]
  | @cons j c c' q bit bits hstep htail ih =>
      have hmem : c' ∈ fullCarryStep Q j [c] := by
        cases bit with
        | false =>
            have hs : c=2*c' := by simpa using hstep
            have hEven : c%2=0 := by rw [hs]; simp
            have hDiv : c/2=c' := by rw [hs]; simp
            simp [fullCarryStep, hEven, hDiv]
        | true =>
            have hs : c+(Q-j)=2*c' := by simpa using hstep
            have hEven : (c+(Q-j))%2=0 := by rw [hs]; simp
            have hDiv : (c+(Q-j))/2=c' := by rw [hs]; simp
            simp [fullCarryStep, hEven, hDiv]
      have hsub : ∀ x, x∈[c'] → x∈fullCarryStep Q j [c] := by
        intro x hx
        simp at hx
        subst x
        exact hmem
      simpa [fullCarryStates] using
        (fullCarryStates_mono Q (j+1) [c']
          (fullCarryStep Q j [c]) hsub bits.length q ih)

theorem noFullPrefix_of_emptyCarry (Q K : Nat)
    (hempty : fullCarryStates Q 0 [1] K = []) :
    ¬ ∃ xs : List Bool, xs.length = K ∧
      fullSumBits Q 0 xs % 2^K = 2^K-1 := by
  rintro ⟨xs, hlen, hmod⟩
  let total := fullSumBits Q 0 xs
  have hmodadd := Nat.mod_add_div total (2^K)
  rw [hmod] at hmodadd
  have hsum : total+1 = 2^K*(total/2^K+1) := by
    have hdiv' : total = (2^K-1)+2^K*(total/2^K) :=
      hmodadd.symm
    have hdivPlus := congrArg (fun x => x+1) hdiv'
    calc
      total+1 = ((2^K-1)+2^K*(total/2^K))+1 := hdivPlus
      _ = (2^K-1+1)+2^K*(total/2^K) := by ac_rfl
      _ = 2^K+2^K*(total/2^K) := by
            have hsub : 2^K-1+1=2^K :=
              Nat.sub_add_cancel (Nat.one_le_pow K 2 (by decide))
            rw [hsub]
      _ = 2^K*(total/2^K+1) := by
            rw [Nat.mul_add]
            ac_rfl
  have hsum' : 1+fullSumBits Q 0 xs =
      2^xs.length*(fullSumBits Q 0 xs/2^K+1) := by
    simpa [total, hlen, Nat.add_comm] using hsum
  have hpath : FullCarryPath Q 0 xs 1
      (fullSumBits Q 0 xs/2^K+1) :=
    fullCarryPath_of_sum Q xs 0 1 _ hsum'
  have hmem := FullCarryPath.mem_fullCarryStates hpath
  rw [hlen, hempty] at hmem
  simp at hmem

/-- Every source CountCone history has a full-P Boolean prefix at every
    modulus 2^K with K no larger than its total inverse cost m. -/
theorem source_full_prefix (n b d m z K : Nat) (hn : 14≤n)
    (h : CountCone (14*2^n-2*n-16) 3 b d m z)
    (hK : 0<K) (hKm : K≤m) :
    ∃ xs : List Bool, xs.length=K ∧
      fullSumBits (7*2^n-(n+3)) 0 xs % 2^K = 2^K-1 := by
  let Q := 7*2^n-(n+3)
  have hodd : OddCone (14*2^n-2*n-16) 3 b d m :=
    counted_to_odd_cone _ _ _ _ _ _ h
  have hmass0 := odd_cone_mass
    (14*2^n-2*n-16) 3 b d m hodd
  have hp := BB6WallCarry.pow2_ge_1100_mul n hn
  have hP : n+3≤7*2^n := by omega
  have hroot : (14*2^n-2*n-16)+3+2*n+13=14*2^n := by omega
  have hmass : b+d+2*m+2*n+13=14*2^n := by omega
  have hQm : 2*Q=2*m+b+d+7 := by
    dsimp [Q]
    omega
  have hmq : m≤Q := by omega
  obtain ⟨A, hnd, hlt, hstart, hInv⟩ :=
    source_cost_witness n b d m z hn h
  have hd : d%2=1 := source_odd_right n b d m z h
  let v := (d-1)/2
  have hD : d-1=2*v := by
    dsimp [v]
    omega
  have hEq : 1+7*2^n*costPowSum A =
      2^m*v+costWeightedSum n A := by
    have hprod :
        2*(7*2^n*costPowSum A)=14*2^n*costPowSum A := by
      calc
        2*(7*2^n*costPowSum A) =
            (2*7)*2^n*costPowSum A := by ac_rfl
        _ = 14*2^n*costPowSum A := by simp
    have hDouble :
        2*(1+7*2^n*costPowSum A) =
          2*(2^m*v+costWeightedSum n A) := by
      calc
        2*(1+7*2^n*costPowSum A) =
            2+2*(7*2^n*costPowSum A) := by
              rw [Nat.mul_add]
        _ = 2+14*2^n*costPowSum A := by rw [hprod]
        _ = 2^m*(d-1)+2*costWeightedSum n A := hInv
        _ = 2*(2^m*v+costWeightedSum n A) := by
              rw [hD, Nat.mul_add]
              ac_rfl
    exact Nat.eq_of_mul_eq_mul_left (by decide : 0<2) hDouble
  have hA : ∀ s∈A, s≤Q := by
    intro s hs
    have hslt := hlt s hs
    omega
  have hAdd := fullSum_add_weighted n Q A hP rfl hA
  have hFull : 1+fullWeightedSum Q A=2^m*v := by
    have hcancel :
        (1+fullWeightedSum Q A)+costWeightedSum n A =
          (2^m*v)+costWeightedSum n A := by
      calc
        _ = 1+(fullWeightedSum Q A+costWeightedSum n A) := by ac_rfl
        _ = 1+7*2^n*costPowSum A := by rw [hAdd]
        _ = 2^m*v+costWeightedSum n A := hEq
    exact Nat.add_right_cancel hcancel
  obtain ⟨r, hr⟩ : ∃ r, 2^m=2^K*r := by
    refine ⟨2^(m-K), ?_⟩
    rw [← Nat.pow_add, Nat.add_sub_of_le hKm]
  have hdiv : 2^K ∣ 1+fullWeightedSum Q A := by
    rw [hFull, hr]
    exact ⟨r*v, by ac_rfl⟩
  have hzero : (1+fullWeightedSum Q A)%2^K=0 :=
    Nat.mod_eq_zero_of_dvd hdiv
  have hpow : 1<2^K := by
    have hpowge : 2≤2^K := by
      cases K with
      | zero => omega
      | succ k =>
          rw [Nat.pow_succ]
          have hp : 1≤2^k := Nat.one_le_pow k 2 (by decide)
          omega
    omega
  have hsumMod :
      (1+fullWeightedSum Q A)%2^K =
        (1%2^K+fullWeightedSum Q A%2^K)%2^K :=
    Nat.add_mod _ _ _
  rw [Nat.mod_eq_of_lt hpow] at hsumMod
  rw [hzero] at hsumMod
  have hrem : fullWeightedSum Q A%2^K<2^K :=
    Nat.mod_lt _ (by omega)
  have hmodZero :
      (1+fullWeightedSum Q A%2^K)%2^K=0 := hsumMod.symm
  have hFullMod : fullWeightedSum Q A%2^K=2^K-1 := by
    by_cases hlt : 1+fullWeightedSum Q A%2^K<2^K
    · rw [Nat.mod_eq_of_lt hlt] at hmodZero
      omega
    · have heq : 1+fullWeightedSum Q A%2^K=2^K := by omega
      omega
  obtain ⟨xs, hlen, hbits⟩ := fullWeighted_mod_bits Q K A hnd
  refine ⟨xs, hlen, ?_⟩
  calc
    fullSumBits Q 0 xs%2^K =
        fullWeightedSum Q A%2^K := hbits.symm
    _ = 2^K-1 := hFullMod

/-- An empty full-P carry layer at K rules out every original CountCone
    history whose total inverse cost is at least K, with no endpoint
    hypothesis and no restriction K≤n. -/
theorem source_countcone_cost_lt_full (n b d m z K : Nat)
    (hn : 14≤n)
    (h : CountCone (14*2^n-2*n-16) 3 b d m z)
    (hK : 0<K)
    (hno : ¬ ∃ xs : List Bool, xs.length=K ∧
      fullSumBits (7*2^n-(n+3)) 0 xs % 2^K = 2^K-1)
    : m<K := by
  by_cases hKm : K≤m
  · exact False.elim (hno (source_full_prefix n b d m z K hn h hK hKm))
  · omega

#print axioms fullPrefixSum_cons
#print axioms fullPrefix_bits
#print axioms fullWeighted_mod_prefix
#print axioms fullWeighted_mod_bits
#print axioms fullSum_add_weighted
#print axioms fullCarryPath_of_sum
#print axioms FullCarryPath.mem_fullCarryStates
#print axioms noFullPrefix_of_emptyCarry
#print axioms source_full_prefix
#print axioms source_countcone_cost_lt_full

end BB6.Agent28FullPrefix
