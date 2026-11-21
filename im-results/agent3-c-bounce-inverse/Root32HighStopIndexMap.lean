import Lean.Elab.Tactic.Omega

namespace BB6.Agent3Root32HighStopIndexMap

/-- The nine already-derived root-index cylinders, expressed in the
quotient j where r=32+64*j. This is coverage bookkeeping only. -/
def coveredJ (j : Nat) : Prop :=
  j % 16 = 3 ∨
  j % 256 = 149 ∨
  j % 256 = 165 ∨
  j % 512 = 117 ∨
  j % 512 = 181 ∨
  j % 1024 = 549 ∨
  j % 1024 = 1013 ∨
  j % 4096 = 2613 ∨
  j % 8192 = 4133

/-- The corresponding nine parameter cylinders in t. -/
def coveredT (t : Nat) : Prop :=
  t % 16 = 1 ∨
  t % 256 = 47 ∨
  t % 256 = 31 ∨
  t % 512 = 79 ∨
  t % 512 = 15 ∨
  t % 1024 = 159 ∨
  t % 1024 = 719 ∨
  t % 4096 = 1167 ∨
  t % 8192 = 7839

/-- The original root32 equation, with r=32+64*j and
u=1802+6720*t, is exactly the normalized equation used below. -/
theorem root32_original_to_tj (u r t j E : Nat)
    (hE : 30 ≤ E)
    (hu : u = 1802 + 6720*t)
    (hr : r = 32 + 64*j)
    (hroot : 18018 + 211*u + 22155*r = 20 * 2^(E-13)) :
    17300 + 22155*(t+j) = 5 * 2^(E-17) := by
  have hexp : E-13 = 4 + (E-17) := by omega
  have hpow : 20*2^(E-13) = 64*(5*2^(E-17)) := by
    rw [hexp, Nat.pow_add, show (2:Nat)^4 = 16 by decide]
    omega
  rw [hu,hr] at hroot
  have hleft :
      18018 + 211*(1802+6720*t) + 22155*(32+64*j) =
        64*(17300+22155*(t+j)) := by omega
  rw [hleft,hpow] at hroot
  omega

/-- The saturated root equation fixes t+j modulo 8192. -/
theorem root32_tj_mod8192 (t j E : Nat)
    (hE : 30 ≤ E)
    (hroot : 17300 + 22155 * (t+j) = 5 * 2^(E-17)) :
    (t+j) % 8192 = 3780 := by
  have hexp : E-17 = 13 + (E-30) := by omega
  have hdiv : 8192 ∣ 5 * 2^(E-17) := by
    refine ⟨5 * 2^(E-30), ?_⟩
    rw [hexp, Nat.pow_add, show (2:Nat)^13 = 8192 by decide]
    omega
  have hdiv' : 8192 ∣ 17300 + 22155 * (t+j) := by
    rw [hroot]
    exact hdiv
  rcases hdiv' with ⟨q,hq⟩
  have hmul :
      291 * (17300 + 22155 * (t+j)) = 8192 * (291*q) := by
    calc
      291 * (17300 + 22155 * (t+j))
          = 291 * (8192*q) := by rw [hq]
      _ = 8192 * (291*q) := by omega
  have hexpand :
      291 * (17300 + 22155 * (t+j)) =
        8192 * (614 + 787*(t+j)) + (4412 + (t+j)) := by
    calc
      291 * (17300 + 22155 * (t+j))
          = 291*17300 + (291*22155)*(t+j) := by omega
      _ = (8192*614+4412) + (8192*787+1)*(t+j) := by omega
      _ = 8192 * (614 + 787*(t+j)) + (4412 + (t+j)) := by omega
  rw [hexpand] at hmul
  have hdivN : 8192 ∣ 4412 + (t+j) := by
    refine ⟨291*q - (614 + 787*(t+j)), ?_⟩
    omega
  have hmodN : (4412 + (t+j)) % 8192 = 0 :=
    Nat.mod_eq_zero_of_dvd hdivN
  have hmodN' : (4412 + (t+j)%8192) % 8192 = 0 := by
    rw [Nat.add_mod] at hmodN
    have hconst : 4412%8192 = 4412 :=
      Nat.mod_eq_of_lt (by decide : 4412 < 8192)
    rw [hconst] at hmodN
    exact hmodN
  have hbound : (t+j)%8192 < 8192 :=
    Nat.mod_lt _ (by decide)
  omega

private theorem reduce_modulus (n k : Nat)
    (hk : k ∣ 8192) (hn : n % 8192 = 3780) :
    n % k = 3780 % k := by
  have hleft : (n%8192)%k = n%k :=
    Nat.mod_mod_of_dvd n hk
  have h := congrArg (fun z : Nat => z%k) hn
  rw [hleft] at h
  exact h

/-- Exact root-index arithmetic maps the nine j-cylinders to the
nine t-cylinders. This theorem makes no reachability assertion. -/
theorem root32_highstop_index_map (t j E : Nat)
    (hE : 30 ≤ E)
    (hroot : 17300 + 22155 * (t+j) = 5 * 2^(E-17))
    (hj : coveredJ j) :
    coveredT t := by
  have hN := root32_tj_mod8192 t j E hE hroot
  rcases hj with h1 | h2 | h3 | h4 | h5 | h6 | h7 | h8 | h9
  · left
    have hN16 := reduce_modulus (t+j) 16 (by decide) hN
    have hres : 3780%16=4 := by decide
    rw [hres] at hN16
    have hsplit : (t+j)%16 = (t%16+j%16)%16 :=
      Nat.add_mod t j 16
    rw [h1] at hsplit
    omega
  · right
    left
    have hN256 := reduce_modulus (t+j) 256 (by decide) hN
    have hres : 3780%256=196 := by decide
    rw [hres] at hN256
    have hsplit : (t+j)%256 = (t%256+j%256)%256 :=
      Nat.add_mod t j 256
    rw [h2] at hsplit
    omega
  · right
    right
    left
    have hN256 := reduce_modulus (t+j) 256 (by decide) hN
    have hres : 3780%256=196 := by decide
    rw [hres] at hN256
    have hsplit : (t+j)%256 = (t%256+j%256)%256 :=
      Nat.add_mod t j 256
    rw [h3] at hsplit
    omega
  · right
    right
    right
    left
    have hN512 := reduce_modulus (t+j) 512 (by decide) hN
    have hres : 3780%512=196 := by decide
    rw [hres] at hN512
    have hsplit : (t+j)%512 = (t%512+j%512)%512 :=
      Nat.add_mod t j 512
    rw [h4] at hsplit
    omega
  · right
    right
    right
    right
    left
    have hN512 := reduce_modulus (t+j) 512 (by decide) hN
    have hres : 3780%512=196 := by decide
    rw [hres] at hN512
    have hsplit : (t+j)%512 = (t%512+j%512)%512 :=
      Nat.add_mod t j 512
    rw [h5] at hsplit
    omega
  · right
    right
    right
    right
    right
    left
    have hN1024 := reduce_modulus (t+j) 1024 (by decide) hN
    have hres : 3780%1024=708 := by decide
    rw [hres] at hN1024
    have hsplit : (t+j)%1024 = (t%1024+j%1024)%1024 :=
      Nat.add_mod t j 1024
    rw [h6] at hsplit
    omega
  · right
    right
    right
    right
    right
    right
    left
    have hN1024 := reduce_modulus (t+j) 1024 (by decide) hN
    have hres : 3780%1024=708 := by decide
    rw [hres] at hN1024
    have hsplit : (t+j)%1024 = (t%1024+j%1024)%1024 :=
      Nat.add_mod t j 1024
    rw [h7] at hsplit
    omega
  · right
    right
    right
    right
    right
    right
    right
    left
    have hN4096 := reduce_modulus (t+j) 4096 (by decide) hN
    have hres : 3780%4096=3780 := by decide
    rw [hres] at hN4096
    have hsplit : (t+j)%4096 = (t%4096+j%4096)%4096 :=
      Nat.add_mod t j 4096
    rw [h8] at hsplit
    omega
  · right
    right
    right
    right
    right
    right
    right
    right
    have hsplit : (t+j)%8192 = (t%8192+j%8192)%8192 :=
      Nat.add_mod t j 8192
    rw [h9] at hsplit
    omega

#print axioms root32_original_to_tj
#print axioms root32_tj_mod8192
#print axioms root32_highstop_index_map

end BB6.Agent3Root32HighStopIndexMap
