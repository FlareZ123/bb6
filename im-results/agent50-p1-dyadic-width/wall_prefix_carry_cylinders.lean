import Lean

/-!
# Lean certificate: root-prefix carry cylinders for the two fourth-edge restart families

This file uses only Lean core (`import Lean`). `bitExpr n rest` is the prefix sum
`(n+3) + sum_{s=1}^{k} x_s (n+3+s) 2^s`, where `rest` has length `k` and
`x_s` is its Boolean selection bit. The leading `(n+3)` fixes `x_0=1`.

`carryStatesFrom` is the exact dynamic program for the carry recurrence
`c_{s+1}=(c_s+x_s(n+3+s))/2`, retaining both choices precisely when integral.
The theorem `noBitSubset_of_emptyCarry` proves that an empty carry layer excludes
all such Boolean prefixes. `noBitSubset_of_add_multiple` lifts a certificate
from `n` to every `n + 2^(k+1)t`, since the prefix expression changes by a
multiple of `2^(k+1)`.

The final four theorems exclude the indicated infinite parameter cylinders in
the two local restart progressions. The source-wall-to-subset bridge is stated
in the accompanying Markdown note and is to be composed with the independent
source theorem `source_wall_cost_list_identity` in `WallTelescopingSource.lean`.
-/

namespace BB6WallCarry

def sumBits (n j : Nat) : List Bool → Nat
  | [] => 0
  | b :: bs => (if b then n + 3 + j else 0) + 2 * sumBits n (j + 1) bs

inductive CarryPath (n : Nat) : Nat → List Bool → Nat → Nat → Prop
  | nil (j c : Nat) : CarryPath n j [] c c
  | cons (j c c' q : Nat) (b : Bool) (bs : List Bool)
      (hstep : c + (if b then n + 3 + j else 0) = 2 * c')
      (htail : CarryPath n (j + 1) bs c' q) :
      CarryPath n j (b :: bs) c q

theorem carryPath_of_sum (n : Nat) :
    ∀ (xs : List Bool) (j c q : Nat),
      c + sumBits n j xs = 2 ^ xs.length * q → CarryPath n j xs c q := by
  intro xs
  induction xs with
  | nil =>
      intro j c q h
      simp [sumBits] at h
      subst q
      exact CarryPath.nil j c
  | cons b bs ih =>
      intro j c q h
      let t := if b then n + 3 + j else 0
      have hEq : c + t + 2 * sumBits n (j + 1) bs =
          2 * (2 ^ bs.length * q) := by
        calc
          c + t + 2 * sumBits n (j + 1) bs = c + (t + 2 * sumBits n (j + 1) bs) := by omega
          _ = (2 ^ bs.length * 2) * q := by simpa [sumBits, t, Nat.pow_succ] using h
          _ = 2 * (2 ^ bs.length * q) := by ac_rfl
      have hEven : (c + t) % 2 = 0 := by omega
      have hStep : c + t = 2 * ((c + t) / 2) := by omega
      have hTail : (c + t) / 2 + sumBits n (j + 1) bs = 2 ^ bs.length * q := by omega
      refine CarryPath.cons j c ((c + t) / 2) q b bs ?_ ?_
      · simpa [t] using hStep
      · exact ih (j + 1) ((c + t) / 2) q hTail

def carryStep (n j : Nat) (cs : List Nat) : List Nat :=
  cs.flatMap fun c =>
    (if c % 2 = 0 then [c / 2] else []) ++
    (if (c + (n + 3 + j)) % 2 = 0 then [(c + (n + 3 + j)) / 2] else [])

def carryStatesFrom (n j : Nat) (cs : List Nat) : Nat → List Nat
  | 0 => cs
  | k + 1 => carryStatesFrom n (j + 1) (carryStep n j cs) k

theorem carryStep_mono (n j : Nat) {cs1 cs2 : List Nat}
    (hsub : ∀ x, x ∈ cs1 → x ∈ cs2) :
    ∀ y, y ∈ carryStep n j cs1 → y ∈ carryStep n j cs2 := by
  intro y hy
  simp only [carryStep, List.mem_flatMap] at hy ⊢
  rcases hy with ⟨c, hc, hopt⟩
  exact ⟨c, hsub c hc, hopt⟩

theorem carryStatesFrom_mono (n j : Nat) (cs1 cs2 : List Nat)
    (hsub : ∀ x, x ∈ cs1 → x ∈ cs2) :
    ∀ k y, y ∈ carryStatesFrom n j cs1 k → y ∈ carryStatesFrom n j cs2 k := by
  intro k
  induction k generalizing j cs1 cs2 with
  | zero =>
      intro y hy
      simpa [carryStatesFrom] using hsub y hy
  | succ k ih =>
      intro y hy
      apply ih (j + 1) (carryStep n j cs1) (carryStep n j cs2)
        (carryStep_mono n j hsub) y
      simpa [carryStatesFrom] using hy

theorem CarryPath.mem_carryStatesFrom {n j : Nat} {xs : List Bool} {c q : Nat}
    (h : CarryPath n j xs c q) :
    q ∈ carryStatesFrom n j [c] xs.length := by
  induction h with
  | nil j c =>
      simp [carryStatesFrom]
  | @cons j c c' q b bs hstep htail ih =>
      have hmem : c' ∈ carryStep n j [c] := by
        cases b with
        | false =>
            have hs : c = 2 * c' := by simpa using hstep
            have hEven : c % 2 = 0 := by rw [hs]; simp
            have hDiv : c / 2 = c' := by rw [hs]; simp
            simp [carryStep, hEven, hDiv]
        | true =>
            have hs : c + (n + 3 + j) = 2 * c' := by simpa using hstep
            have hEven : (c + (n + 3 + j)) % 2 = 0 := by rw [hs]; simp
            have hDiv : (c + (n + 3 + j)) / 2 = c' := by rw [hs]; simp
            simp [carryStep, hEven, hDiv]
      have hsub : ∀ x, x ∈ [c'] → x ∈ carryStep n j [c] := by
        intro x hx
        simp at hx
        subst x
        exact hmem
      simpa [carryStatesFrom] using
        (carryStatesFrom_mono n (j + 1) [c'] (carryStep n j [c]) hsub bs.length q ih)

theorem noBitSubset_of_emptyCarry (n k : Nat) (hnEven : n % 2 = 0)
    (hempty : carryStatesFrom n 1 [((n + 2) / 2)] k = []) :
    ¬ ∃ (rest : List Bool), rest.length = k ∧
      ((n + 3) + 2 * sumBits n 1 rest) % 2 ^ (k + 1) = 1 := by
  rintro ⟨rest, hlen, hmod⟩
  let total := (n + 3) + 2 * sumBits n 1 rest
  obtain ⟨q, hsum⟩ : ∃ q, total = 1 + 2 ^ (k + 1) * q := by
    have hmodadd := Nat.mod_add_div total (2 ^ (k + 1))
    rw [hmod] at hmodadd
    exact ⟨total / 2 ^ (k + 1), by omega⟩
  have hEven : n + 2 = 2 * ((n + 2) / 2) := by omega
  have hsum' : total - 1 = 2 ^ (k + 1) * q := by omega
  have hEq : (n + 2) + 2 * sumBits n 1 rest =
      2 * (2 ^ k * q) := by
    calc
      (n + 2) + 2 * sumBits n 1 rest = total - 1 := by dsimp [total]; omega
      _ = 2 ^ (k + 1) * q := hsum'
      _ = 2 * (2 ^ k * q) := by rw [Nat.pow_succ]; ac_rfl
  have hEq' : 2 * ((n + 2) / 2 + sumBits n 1 rest) =
      2 * (2 ^ k * q) := by
    calc
      2 * ((n + 2) / 2 + sumBits n 1 rest) =
          2 * ((n + 2) / 2) + 2 * sumBits n 1 rest := by rw [Nat.mul_add]
      _ = (n + 2) + 2 * sumBits n 1 rest := by rw [← hEven]
      _ = 2 * (2 ^ k * q) := hEq
  have hTail : (n + 2) / 2 + sumBits n 1 rest =
      2 ^ k * q := Nat.mul_left_cancel (by decide : 0 < 2) hEq'
  have hpath := carryPath_of_sum n rest 1 ((n + 2) / 2) q (by
    simpa [hlen] using hTail)
  have hmem : q ∈ carryStatesFrom n 1 [((n + 2) / 2)] k := by
    simpa [hlen] using hpath.mem_carryStatesFrom
  rw [hempty] at hmem
  simp at hmem

def sumPowers : List Bool → Nat
  | [] => 0
  | b :: bs => (if b then 1 else 0) + 2 * sumPowers bs

theorem sumBits_add (n d j : Nat) (xs : List Bool) :
    sumBits (n + d) j xs = sumBits n j xs + d * sumPowers xs := by
  induction xs generalizing j with
  | nil => simp [sumBits, sumPowers]
  | cons b bs ih =>
      cases b <;> simp [sumBits, sumPowers, ih, Nat.mul_add, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] <;> ac_rfl

def bitExpr (n : Nat) (rest : List Bool) : Nat :=
  (n + 3) + 2 * sumBits n 1 rest

theorem bitExpr_add (n d : Nat) (rest : List Bool) :
    bitExpr (n + d) rest = bitExpr n rest + d * (1 + 2 * sumPowers rest) := by
  simp [bitExpr, sumBits_add, Nat.mul_add, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]
  ac_rfl

theorem noBitSubset_of_add_multiple (n k t : Nat) (hnEven : n % 2 = 0)
    (hempty : carryStatesFrom n 1 [((n + 2) / 2)] k = []) :
    ¬ ∃ (rest : List Bool), rest.length = k ∧
      bitExpr (n + 2 ^ (k + 1) * t) rest % 2 ^ (k + 1) = 1 := by
  intro h
  rcases h with ⟨rest, hlen, hmod⟩
  have hmodEq : bitExpr (n + 2 ^ (k + 1) * t) rest % 2 ^ (k + 1) =
      bitExpr n rest % 2 ^ (k + 1) := by
    rw [bitExpr_add]
    have hdvd : 2 ^ (k + 1) ∣ (2 ^ (k + 1) * t) * (1 + 2 * sumPowers rest) :=
      ⟨t * (1 + 2 * sumPowers rest), by ac_rfl⟩
    rw [Nat.add_mod, Nat.mod_eq_zero_of_dvd hdvd]
    simp
  have hbase : bitExpr n rest % 2 ^ (k + 1) = 1 := by
    rw [← hmodEq]
    exact hmod
  exact (noBitSubset_of_emptyCarry n k hnEven hempty) ⟨rest, hlen, by simpa [bitExpr] using hbase⟩

theorem noPrefix_600418_cylinder (t : Nat) :
    ¬ ∃ rest : List Bool, rest.length = 59 ∧
      bitExpr (600418 + 2 ^ 60 * t) rest % 2 ^ 60 = 1 :=
  noBitSubset_of_add_multiple 600418 59 t (by decide) (by decide)

theorem noPrefix_1195474_cylinder (t : Nat) :
    ¬ ∃ rest : List Bool, rest.length = 11 ∧
      bitExpr (1195474 + 2 ^ 12 * t) rest % 2 ^ 12 = 1 :=
  noBitSubset_of_add_multiple 1195474 11 t (by decide) (by decide)

theorem noPrefix_712786_cylinder (t : Nat) :
    ¬ ∃ rest : List Bool, rest.length = 13 ∧
      bitExpr (712786 + 2 ^ 14 * t) rest % 2 ^ 14 = 1 :=
  noBitSubset_of_add_multiple 712786 13 t (by decide) (by decide)

theorem noPrefix_1416034_cylinder (t : Nat) :
    ¬ ∃ rest : List Bool, rest.length = 21 ∧
      bitExpr (1416034 + 2 ^ 22 * t) rest % 2 ^ 22 = 1 :=
  noBitSubset_of_add_multiple 1416034 21 t (by decide) (by decide)

theorem noPrefix_familyI_h1 (t : Nat) :
    ¬ ∃ rest : List Bool, rest.length = 59 ∧
      bitExpr (5362 + 595056 * (1 + 2 ^ 56 * t)) rest % 2 ^ 60 = 1 := by
  have hEq : 5362 + 595056 * (1 + 2 ^ 56 * t) = 600418 + 2 ^ 60 * (37191 * t) := by omega
  rw [hEq]
  exact noPrefix_600418_cylinder (37191 * t)

theorem noPrefix_familyI_h2 (t : Nat) :
    ¬ ∃ rest : List Bool, rest.length = 11 ∧
      bitExpr (5362 + 595056 * (2 + 2 ^ 8 * t)) rest % 2 ^ 12 = 1 := by
  have hEq : 5362 + 595056 * (2 + 2 ^ 8 * t) = 1195474 + 2 ^ 12 * (37191 * t) := by omega
  rw [hEq]
  exact noPrefix_1195474_cylinder (37191 * t)

theorem noPrefix_familyII_h1 (t : Nat) :
    ¬ ∃ rest : List Bool, rest.length = 13 ∧
      bitExpr (9538 + 703248 * (1 + 2 ^ 10 * t)) rest % 2 ^ 14 = 1 := by
  have hEq : 9538 + 703248 * (1 + 2 ^ 10 * t) = 712786 + 2 ^ 14 * (43953 * t) := by omega
  rw [hEq]
  exact noPrefix_712786_cylinder (43953 * t)

theorem noPrefix_familyII_h2 (t : Nat) :
    ¬ ∃ rest : List Bool, rest.length = 21 ∧
      bitExpr (9538 + 703248 * (2 + 2 ^ 18 * t)) rest % 2 ^ 22 = 1 := by
  have hEq : 9538 + 703248 * (2 + 2 ^ 18 * t) = 1416034 + 2 ^ 22 * (43953 * t) := by omega
  rw [hEq]
  exact noPrefix_1416034_cylinder (43953 * t)


theorem familyI_terminal_m_ge_n_aux (n P u : Nat)
    (hP : 1100 * n ≤ P) (hU : 1058 * u + 636 = 17 * P) (hn : 1 ≤ n) :
    n ≤ 14 * u - 2 * n - 3 := by omega

theorem familyII_terminal_m_ge_n_aux (n P u : Nat)
    (hP : 1100 * n ≤ P) (hU : 1198 * u + 712 = 87 * P) (hn : 1 ≤ n) :
    n ≤ 14 * u - 2 * n - 3 := by omega

theorem pow2_ge_1100_mul (n : Nat) (hn : 14 ≤ n) : 1100 * n ≤ 2 ^ n := by
  induction n with
  | zero => omega
  | succ n ih =>
      by_cases hbase : n = 13
      · subst n
        have hbase : 1100 * 14 ≤ 2 ^ 14 := by decide
        simpa using hbase
      · have hn' : 14 ≤ n := by omega
        have hprev := ih hn'
        have hpow : 1100 ≤ 2 ^ n := by omega
        rw [Nat.pow_succ]
        omega

theorem familyI_terminal_m_ge_n (n u : Nat) (hn : 14 ≤ n)
    (hU : 1058 * u + 636 = 17 * 2 ^ n) :
    n ≤ 14 * u - 2 * n - 3 := by
  apply familyI_terminal_m_ge_n_aux n (2 ^ n) u
  · exact pow2_ge_1100_mul n hn
  · exact hU
  · omega

theorem familyII_terminal_m_ge_n (n u : Nat) (hn : 14 ≤ n)
    (hU : 1198 * u + 712 = 87 * 2 ^ n) :
    n ≤ 14 * u - 2 * n - 3 := by
  apply familyII_terminal_m_ge_n_aux n (2 ^ n) u
  · exact pow2_ge_1100_mul n hn
  · exact hU
  · omega

#print axioms noPrefix_familyI_h1
#print axioms noPrefix_familyI_h2
#print axioms noPrefix_familyII_h1
#print axioms noPrefix_familyII_h2
#print axioms familyI_terminal_m_ge_n
#print axioms familyII_terminal_m_ge_n

end BB6WallCarry
